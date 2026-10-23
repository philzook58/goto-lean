import Std.WP
import Std.Tactic.Do

/-! Finite block effects, interpreted both by weakest preconditions and concrete execution.
Expressions and local state remain ordinary Lean code, not an embedded expression language. -/
namespace GotoLean
open Std.WP Lean.Order
set_option experimental.vcgen true

/-- Original GOTO instruction and source/property information. -/
abbrev Site := String

/-- Only effects are represented as data. Each generated basic block is finite. -/
inductive Action (α : Type) where
  | done (value : α)
  | choose (site : Site) (width : Nat) (next : BitVec width → Action α)
  | check (site : Site) (condition : Bool) (next : Action α)
  | assume (site : Site) (condition : Bool) (next : Action α)

namespace Action

def bind (x : Action α) (f : α → Action β) : Action β :=
  match x with
  | .done a => f a
  | .choose site w k => .choose site w (fun v => bind (k v) f)
  | .check site b k => .check site b (bind k f)
  | .assume site b k => .assume site b (bind k f)

instance : Monad Action where
  pure := .done
  bind := bind

@[simp] theorem bind_done (a : α) (f : α → Action β) : bind (.done a) f = f a := rfl

@[simp] theorem bind_pure (x : Action α) : bind x .done = x := by
  induction x with
  | done => rfl
  | choose site w k ih => simp only [bind]; congr; funext v; exact ih v
  | check site b k ih => simp only [bind, ih]
  | assume site b k ih => simp only [bind, ih]

theorem bind_assoc (x : Action α) (f : α → Action β) (g : β → Action γ) :
    bind (bind x f) g = bind x (fun a => bind (f a) g) := by
  induction x with
  | done => rfl
  | choose site w k ih => simp only [bind]; congr; funext v; exact ih v
  | check site b k ih => simp only [bind, ih]
  | assume site b k ih => simp only [bind, ih]

instance : LawfulMonad Action := LawfulMonad.mk' Action
  (fun x => bind_pure x) (fun _ _ => rfl) bind_assoc

/-- Safety of a finite block, including checks even when no result is returned. -/
def wp (x : Action α) (post : α → Prop) : Prop :=
  match x with
  | .done a => post a
  | .choose _ _ k => ∀ v, wp (k v) post
  | .check _ b k => b = true ∧ wp k post
  | .assume _ b k => b = true → wp k post

theorem wp_mono (x : Action α) (h : ∀ a, P a → Q a) : wp x P → wp x Q := by
  induction x with
  | done a => exact h a
  | choose site w k ih => exact fun hx v => ih v (hx v)
  | check site b k ih => exact fun hx => ⟨hx.1, ih hx.2⟩
  | assume site b k ih => exact fun hx hb => ih (hx hb)

@[simp] theorem wp_bind (x : Action α) (f : α → Action β) (post : β → Prop) :
    wp (bind x f) post = wp x (fun a => wp (f a) post) := by
  induction x with
  | done => rfl
  | choose site w k ih => simp only [wp, bind, ih]
  | check site b k ih => simp only [wp, bind, ih]
  | assume site b k ih => simp only [wp, bind, ih]

instance : WP (Action α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => x.wp post⟩
  wp_trans_monotone x := fun _ _ _ _ _ h => wp_mono x h

instance : WPMonad Action Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := id
  bind_le_wp_bind x f post _ := by
    change wp x (fun a => wp (f a) post) → wp (bind x f) post
    rw [wp_bind]; exact id

@[simp, grind =] theorem wp_apply_eq (x : Action α) (post : α → Prop) (epost : EStack⟨⟩) :
    Std.WP.wp x post epost = x.wp post := rfl

@[simp, grind =] theorem wp_pure (a : α) (post : α → Prop) :
    (pure a : Action α).wp post = post a := rfl

end Action

def choose (site : Site) (width : Nat) : Action (BitVec width) :=
  .choose site width .done

def check (site : Site) (condition : Bool) : Action Unit := .check site condition (.done ())
def assume (site : Site) (condition : Bool) : Action Unit := .assume site condition (.done ())

@[spec] theorem choose_spec (site : Site) (w : Nat) (Q : BitVec w → Prop) :
    ⦃∀ v, Q v⦄ choose site w ⦃Q⦄ := ⟨id⟩

@[spec] theorem check_spec (site : Site) (b : Bool) (Q : Unit → Prop) :
    ⦃b = true ∧ Q ()⦄ check site b ⦃Q⦄ := ⟨id⟩

@[spec] theorem assume_spec (site : Site) (b : Bool) (Q : Unit → Prop) :
    ⦃b = true → Q ()⦄ assume site b ⦃Q⦄ := ⟨id⟩

/-- CBMC's bit-blasted division leaves the result unconstrained on zero divisors. -/
def divide (site : Site) (signed remainder : Bool) (x y : BitVec w) : Action (BitVec w) := do
  if y == 0 then choose site w
  else pure (if signed then (if remainder then x.srem y else x.sdiv y)
    else (if remainder then x % y else x / y))

/-- Bound the intermediate natural number when executing oversized left shifts. -/
def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  if n < w then x <<< n else 0

@[simp] theorem shiftLeft_eq (x : BitVec w) (n : Nat) : shiftLeft x n = x <<< n := by
  unfold shiftLeft
  split
  · rfl
  · exact (BitVec.shiftLeft_eq_zero (by omega)).symm

/-- Continue with another block/state, or return a value. -/
abbrev Next (σ α : Type) := Sum σ α

/-- One generated block, specialized to its PC and local-variable state. -/
abbrev Step (σ α : Type) := σ → Action (Next σ α)

/-- Safety and return postconditions for every execution of at most `fuel` blocks. -/
def safe (step : Step σ α) : Nat → σ → (α → Prop) → Prop
  | 0, _, _ => True
  | n + 1, s, Q => (step s).wp (Sum.elim (fun s' => safe step n s' Q) Q)

theorem safe_mono (step : Step σ α) (n : Nat) (s : σ) (h : ∀ a, P a → Q a) :
    safe step n s P → safe step n s Q := by
  induction n generalizing s with
  | zero => exact id
  | succ n ih =>
    apply Action.wp_mono
    intro next; cases next with
    | inl s' => exact ih s'
    | inr a => exact h a

/-- A monotone specification, used for unbounded generated functions. -/
structure Program (α : Type) where
  wp : (α → Prop) → Prop
  mono : ∀ {P Q}, (∀ a, P a → Q a) → wp P → wp Q

instance : WP (Program α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => x.wp post⟩
  wp_trans_monotone x := fun _ _ _ _ _ h => x.mono h

/-- Unbounded safety and partial correctness: all finite prefixes are safe. -/
def run (step : Step σ α) (initial : σ) : Program α where
  wp Q := ∀ n, safe step n initial Q
  mono h hx n := safe_mono step n initial h (hx n)

/-- A PC-indexed invariant excludes failed checks and establishes every return postcondition. -/
@[spec] theorem run_spec (step : Step σ α) (initial : σ) (I : σ → Prop) (Q : α → Prop)
    (preserves : ∀ s, I s → (step s).wp (Sum.elim I Q)) :
    ⦃I initial⦄ run step initial ⦃Q⦄ := by
  constructor
  intro hi n
  induction n generalizing initial with
  | zero => trivial
  | succ n ih =>
    apply Action.wp_mono (step initial) _ (preserves initial hi)
    intro next hn
    cases next with
    | inl s => exact ih s hn
    | inr a => exact hn

end GotoLean
