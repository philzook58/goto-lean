#include "printer.h"
#include <goto-programs/goto_model.h>
#include <solvers/flattening/boolbv_width.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/string_constant.h>
#include <util/validate.h>
#include <algorithm>
#include <cctype>
#include <deque>
#include <filesystem>
#include <map>
#include <memory>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>
#include <vector>

namespace {
using Instruction = goto_programt::instructiont;

std::string quote(const std::string &s) {
  std::string out = "\"";
  for (unsigned char c : s) {
    if (c == '\\' || c == '"') { out += '\\'; out += char(c); }
    else if (c == '\n') out += "\\n";
    else if (c == '\r') out += "\\r";
    else if (c == '\t') out += "\\t";
    else if (c < 32 || c == 127) out += '?';
    else out += char(c);
  }
  return out + '"';
}

std::string single_line(std::string s) {
  for (auto &c : s) if (static_cast<unsigned char>(c) < 32) c = ' ';
  return s;
}

std::string source_position(const source_locationt &loc) {
  auto path = std::filesystem::path(id2string(loc.get_file()));
  if (path.empty()) return {};
  if (path.is_absolute()) path = path.lexically_relative(std::filesystem::current_path());
  auto result = path.generic_string() + ":" + id2string(loc.get_line());
  if (!loc.get_column().empty()) result += ":" + id2string(loc.get_column());
  return single_line(result);
}

// Prefixing avoids all Lean keywords and collisions with generated implementation names.
std::string identifier(const std::string &s) {
  std::string out = "v_";
  for (unsigned char c : s) out += std::isalnum(c) && c < 128 ? char(c) : '_';
  return out;
}

struct Printer {
  const goto_modelt &model;
  const goto_functiont &function;
  const std::string function_name;
  namespacet ns;
  boolbv_widtht bv_width;
  std::vector<const Instruction *> instructions;
  std::map<const Instruction *, std::size_t> indices;
  std::set<std::size_t> reachable, leaders;
  std::map<irep_idt, std::string> names;
  std::map<irep_idt, typet> locals;
  std::map<irep_idt, exprt> globals;
  std::set<irep_idt> parameters;
  std::set<irep_idt> addressed;
  bool memory = false;
  bool calls = false;
  unsigned call_variants = 0;
  std::string module;
  const Instruction *current = nullptr;
  typet return_type;
  unsigned temporary = 0;

  Printer(const goto_modelt &m, const goto_functiont &f, std::string name)
    : model(m), function(f), function_name(std::move(name)), ns(m.symbol_table), bv_width(ns) {
    return_type = to_code_type(model.symbol_table.lookup_ref(function_name).type).return_type();
    for (const auto &i : function.body.instructions) {
      indices.emplace(&i, instructions.size()); instructions.push_back(&i);
    }
  }

  std::string site() const {
    if (!current) return function_name;
    const auto &loc = current->source_location();
    std::ostringstream s;
    s << function_name << ": GOTO " << current->location_number;
    if (!loc.get_file().empty()) s << "; " << source_position(loc);
    if (!loc.get_property_id().empty()) s << "; property " << loc.get_property_id();
    if (!loc.get_comment().empty()) s << "; " << loc.get_comment();
    return single_line(s.str());
  }

  [[noreturn]] void fail(const std::string &message) const {
    throw std::runtime_error(site() + ": " + message);
  }

  const typet &representation(const typet &t) const {
    if (t.id() == ID_struct_tag) return ns.follow_tag(to_struct_tag_type(t));
    if (t.id() == ID_union_tag) return ns.follow_tag(to_union_tag_type(t));
    if (t.id() == ID_c_enum_tag) return representation(ns.follow_tag(to_c_enum_tag_type(t)));
    if (t.id() == ID_c_enum) return to_c_enum_type(t).underlying_type();
    return t;
  }

  std::size_t array_size(const typet &t) const {
    mp_integer n;
    const auto &size = to_array_type(t).size();
    if (size.id() != ID_constant || to_integer(to_constant_expr(size), n) || n < 0 ||
        n > std::numeric_limits<unsigned>::max())
      fail("non-constant or oversized array length");
    return numeric_cast_v<std::size_t>(n);
  }

  unsigned width(const typet &input) const {
    const auto &t = representation(input);
    if (t.id() == ID_array) {
      array_size(t);
      width(to_array_type(t).element_type());
    } else if (t.id() == ID_struct || t.id() == ID_union) {
      if (t.id() == ID_union && config.ansi_c.endianness !=
          configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN)
        fail("big-endian union layout is not implemented");
      for (const auto &c : to_struct_union_type(t).components()) width(c.type());
    } else if (t.id() == ID_pointer) {
      if (to_pointer_type(t).get_width() != config.ansi_c.pointer_width)
        fail("mixed pointer widths are not implemented");
    } else if (t.id() != ID_signedbv && t.id() != ID_unsignedbv && t.id() != ID_c_bool &&
               t.id() != ID_bool && t.id() != ID_empty)
      fail("unsupported type " + id2string(input.id()));
    if (t.id() == ID_empty) return 0;
    const auto w = bv_width.get_width_opt(t);
    if (!w || *w > std::numeric_limits<unsigned>::max()) fail("unsupported bit width");
    if (*w == 0 && (t.id() == ID_signedbv || t.id() == ID_unsignedbv || t.id() == ID_c_bool))
      fail("zero-width scalar bitvectors are unsupported");
    return static_cast<unsigned>(*w);
  }

  std::string type(const typet &t) const {
    if (t.id() == ID_bool) return "Bool";
    if (t.id() == ID_empty) return "Unit";
    return "BitVec " + std::to_string(width(t));
  }

  std::string zero(const typet &t) const { return t.id() == ID_bool ? "false" : "0"; }

  std::string bits(const std::string &value, const typet &t) const {
    if (t.id() == ID_bool) return "(if " + value + " then (1 : BitVec 1) else 0)";
    if (t.id() == ID_empty) return "(0 : BitVec 0)";
    return value;
  }

  std::string from_bits(const std::string &value, const typet &t) const {
    if (t.id() == ID_bool) return "(" + value + " != 0)";
    if (t.id() == ID_empty) return "()";
    return value;
  }

  std::string index_value(const exprt &e, std::ostream &out, unsigned indent) {
    if (e.type().id() == ID_integer && e.id() == ID_constant)
      return "(" + id2string(e.get(ID_value)) + " : Int)";
    auto value = expression(e, out, indent);
    return representation(e.type()).id() == ID_signedbv ? "(" + value + ").toInt" :
      "(Int.ofNat (" + value + ").toNat)";
  }

  unsigned member_offset(const typet &t, const irep_idt &name) const {
    const auto &r = representation(t);
    if (r.id() == ID_union) return 0;
    return static_cast<unsigned>(bv_width.get_member(to_struct_type(r), name).offset);
  }

  std::string offset_bits() const {
    return "offsetBits";
  }

  void abi(std::ostream &out) const {
    if (memory)
      out << "abbrev offsetBits : Nat := "
          << config.ansi_c.pointer_width - config.bv_encoding.object_bits << '\n'
          << "abbrev objectBits : Nat := " << config.bv_encoding.object_bits << "\n\n";
  }

  bool contains_pointer(const typet &input) const {
    const auto &t = representation(input);
    if (t.id() == ID_pointer) return true;
    if (t.id() == ID_array) return contains_pointer(to_array_type(t).element_type());
    if (t.id() == ID_struct || t.id() == ID_union)
      for (const auto &c : to_struct_union_type(t).components())
        if (contains_pointer(c.type())) return true;
    return false;
  }

  // Value bits and addressable bytes must agree; do not silently reinterpret packed bitfields.
  unsigned byte_size(const typet &t) const {
    auto size = pointer_offset_size(t, ns);
    if (!size || *size <= 0 || *size > std::numeric_limits<unsigned>::max())
      fail("unsupported object byte size");
    return numeric_cast_v<unsigned>(*size);
  }

  void memory_layout(const typet &input) const {
    const auto &t = representation(input);
    if (width(t) % 8 != 0 || width(t) / 8 != byte_size(t))
      fail("addressable layout differs from packed value layout (bitfields/padding unsupported)");
    if (t.id() == ID_array) memory_layout(to_array_type(t).element_type());
    if (t.id() == ID_struct || t.id() == ID_union) {
      for (const auto &c : to_struct_union_type(t).components()) {
        memory_layout(c.type());
        if (t.id() == ID_struct) {
          auto offset = ::member_offset(to_struct_type(t), c.get_name(), ns);
          if (!offset || *offset * 8 != member_offset(t, c.get_name()))
            fail("addressable member layout differs from packed value layout");
        }
      }
    }
  }

  void mark_addressed(const exprt &e) {
    if (e.id() == ID_symbol) {
      if (e.type().id() == ID_code) fail("function addresses/indirect calls are not implemented");
      if (model.symbol_table.lookup_ref(to_symbol_expr(e).identifier()).is_static_lifetime)
        fail("address-taking of global/static storage is unsupported");
      addressed.insert(to_symbol_expr(e).identifier());
    } else if (e.id() == ID_member) mark_addressed(to_member_expr(e).compound());
    else if (e.id() == ID_index) mark_addressed(to_index_expr(e).array());
    else if (e.id() != ID_dereference) fail("unsupported addressable expression " + id2string(e.id()));
  }

  bool memory_place(const exprt &e) const {
    if (e.id() == ID_dereference) return true;
    if (e.id() == ID_symbol) return addressed.count(to_symbol_expr(e).identifier());
    if (e.id() == ID_member) return memory_place(to_member_expr(e).compound());
    if (e.id() == ID_index) return memory_place(to_index_expr(e).array());
    return false;
  }

  void local(const symbol_exprt &s) {
    const auto &id = s.identifier();
    type(s.type());
    if (locals.count(id)) return;
    const auto &sym = model.symbol_table.lookup_ref(id);
    if (sym.is_static_lifetime)
      fail("global/static storage is unsupported: " + id2string(id));
    locals.emplace(id, s.type());
    std::string base = identifier(id2string(sym.base_name.empty() ? id : sym.base_name));
    std::string name = base;
    unsigned suffix = 1;
    while (std::any_of(names.begin(), names.end(), [&](const auto &p) { return p.second == name; }))
      name = base + "_" + std::to_string(++suffix);
    names.emplace(id, name);
  }

  std::vector<std::size_t> successors(std::size_t index) const {
    const auto &i = *instructions.at(index);
    std::vector<std::size_t> result;
    if (i.is_end_function()) return result;
    if (i.is_goto()) {
      if (i.targets.size() != 1) fail("expected one GOTO target");
      auto found = indices.find(&*i.get_target());
      if (found == indices.end()) fail("GOTO target outside selected function");
      if (!(i.condition() == false)) result.push_back(found->second);
      if ((i.condition() == true)) return result;
    }
    if (index + 1 == instructions.size()) fail("function falls off GOTO instruction list");
    result.push_back(index + 1);
    return result;
  }

  void prepare() {
    function.validate(ns, validation_modet::EXCEPTION);
    if (instructions.empty()) fail("function has no body");
    current = instructions.front();
    type(return_type);
    for (const auto &id : function.parameter_identifiers) {
      local(model.symbol_table.lookup_ref(id).symbol_expr()); parameters.insert(id);
    }
    std::deque<std::size_t> queue{0};
    while (!queue.empty()) {
      auto index = queue.front(); queue.pop_front();
      if (!reachable.insert(index).second) continue;
      current = instructions[index];
      if (current->is_decl()) local(current->decl_symbol());
      for (auto next : successors(index)) queue.push_back(next);
    }
    leaders.insert(0);
    for (auto index : reachable) {
      current = instructions[index];
      if (current->is_goto()) {
        for (auto next : successors(index)) leaders.insert(next);
        if (reachable.count(index + 1)) leaders.insert(index + 1);
      }
      if (body_call(*current)) leaders.insert(index + 1);
    }
    // Zero-filled record fields are never observed before their declaration's havoc.
    // Check definite lifetime on every path, including back edges and DEAD markers.
    std::set<irep_idt> all;
    for (const auto &p : locals) all.insert(p.first);
    std::map<std::size_t, std::set<irep_idt>> live;
    for (auto index : reachable) live[index] = index == 0 ? parameters : all;
    bool changed;
    do {
      changed = false;
      for (auto index : reachable) {
        const auto &i = *instructions[index];
        auto after = live[index];
        if (i.is_decl()) after.insert(i.decl_symbol().identifier());
        if (i.is_dead()) after.erase(i.dead_symbol().identifier());
        for (auto next : successors(index)) {
          auto &before = live[next];
          std::set<irep_idt> intersection;
          std::set_intersection(before.begin(), before.end(), after.begin(), after.end(),
            std::inserter(intersection, intersection.end()));
          if (before != intersection) { before = std::move(intersection); changed = true; }
        }
      }
    } while (changed);
    bool pointer_expression = false;
    for (auto index : reachable) {
      current = instructions[index];
      const auto &i = *current;
      auto check_symbols = [&](const exprt &expr, const auto &self) -> void {
        pointer_expression = pointer_expression || contains_pointer(expr.type());
        if (expr.id() == ID_address_of) mark_addressed(to_address_of_expr(expr).object());
        if (expr.id() == ID_symbol && expr.type().id() != ID_code) {
          const auto &id = to_symbol_expr(expr).identifier();
          if (!locals.count(id)) {
            const auto &symbol = model.symbol_table.lookup_ref(id);
            auto initial = symbol.value;
            if (initial.is_nil() && !symbol.is_extern && symbol.mode == ID_C) {
              const auto zero = zero_initializer(symbol.type, symbol.location, ns);
              if (zero) initial = *zero;
            }
            if (!symbol.is_static_lifetime || initial.id() != ID_constant)
              fail("global requires a constant scalar initializer: " + id2string(id));
            type(symbol.type);
            globals.emplace(id, initial);
            return;
          }
          if (!live[index].count(id)) fail("symbol used outside its definite lifetime: " + id2string(id));
        }
        for (const auto &op : expr.operands()) self(op, self);
      };
      if (!i.is_decl() && !i.is_dead()) check_symbols(i.code(), check_symbols);
      if (i.has_condition()) check_symbols(i.condition(), check_symbols);
    }
    memory = calls || pointer_expression || !globals.empty() || !addressed.empty() ||
      contains_pointer(return_type);
    for (auto index : reachable) memory = memory || !library_call(*instructions[index]).empty();
    for (const auto &[id, t] : locals) {
      memory = memory || contains_pointer(t);
      if (addressed.count(id)) {
        if (parameters.count(id)) fail("address-taking of parameters is not implemented");
        memory_layout(t);
      }
    }
    if (memory && (config.ansi_c.char_width != 8 || config.ansi_c.endianness !=
        configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN ||
        config.bv_encoding.object_bits == 0 ||
        config.bv_encoding.object_bits >= config.ansi_c.pointer_width))
      fail("object memory requires 8-bit bytes, little endian and a nonempty pointer ID/offset split");
    current = nullptr;
  }

  static void line(std::ostream &out, unsigned indent, const std::string &s) {
    // Only wrap finite let-expressions; continuation indentation preserves block layout.
    const auto arrow = s.find(" ← ");
    if (indent + s.size() <= 100 || s.compare(0, 4, "let ") != 0 || arrow == std::string::npos) {
      out << std::string(indent, ' ') << s << '\n';
      return;
    }
    out << std::string(indent, ' ') << s.substr(0, arrow + 4) << '\n';
    std::size_t start = arrow + 5, space = std::string::npos;
    bool quoted = false, escaped = false;
    unsigned depth = 0;
    const unsigned continuation = indent + 4;
    for (std::size_t i = start; i < s.size(); ++i) {
      const char c = s[i];
      if (escaped) { escaped = false; continue; }
      if (quoted && c == '\\') { escaped = true; continue; }
      if (c == '"') quoted = !quoted;
      if (!quoted) {
        if (c == '(' || c == '[' || c == '{') ++depth;
        if ((c == ')' || c == ']' || c == '}') && depth) --depth;
        if (c == ' ' && depth == 0) space = i;
      }
      if (i - start + continuation >= 100 && space != std::string::npos && space >= start) {
        out << std::string(continuation, ' ') << s.substr(start, space - start) << '\n';
        start = space + 1;
      }
    }
    out << std::string(continuation, ' ') << s.substr(start) << '\n';
  }

  std::string fresh() { return "t" + std::to_string(temporary++); }

  std::string havoc(const typet &t, std::ostream &out, unsigned indent) {
    auto tmp = fresh();
    const unsigned w = t.id() == ID_bool ? 1 : width(t);
    line(out, indent, "let " + tmp + " ← choose " + quote(site()) + " " + std::to_string(w));
    return t.id() == ID_bool ? "(" + tmp + " != 0)" : tmp;
  }

  std::string address(const exprt &e, std::ostream &out, unsigned indent) {
    if (e.id() == ID_symbol && addressed.count(to_symbol_expr(e).identifier()))
      return "s." + names.at(to_symbol_expr(e).identifier());
    if (e.id() == ID_dereference)
      return expression(to_dereference_expr(e).pointer(), out, indent);
    if (e.id() == ID_index) {
      const auto &a = to_index_expr(e);
      auto base = address(a.array(), out, indent);
      auto index = index_value(a.index(), out, indent);
      return "(Pointer.add " + offset_bits() + " " + base + " (" + index + " * " +
        std::to_string(byte_size(e.type())) + "))";
    }
    if (e.id() == ID_member) {
      const auto &m = to_member_expr(e);
      memory_layout(m.compound().type());
      auto base = address(m.compound(), out, indent);
      return "(Pointer.add " + offset_bits() + " " + base + " " +
        std::to_string(member_offset(m.compound().type(), m.get_component_name()) / 8) + ")";
    }
    fail("unsupported addressable expression " + id2string(e.id()));
  }

  std::string expression(const exprt &e, std::ostream &out, unsigned indent) {
    type(e.type());
    const auto &id = e.id();
    if (id == ID_address_of) return address(to_address_of_expr(e).object(), out, indent);
    if (memory_place(e)) {
      memory_layout(e.type());
      auto p = address(e, out, indent), tmp = fresh();
      line(out, indent, "let " + tmp + " ← Memory.load " + quote(site()) + " " +
        offset_bits() + " " + std::to_string(width(e.type())) + " s.memory " + p);
      return from_bits(tmp, e.type());
    }
    if (id == ID_symbol) {
      const auto &symbol = to_symbol_expr(e);
      if (globals.count(symbol.identifier())) {
        const auto &initial = globals.at(symbol.identifier());
        return from_bits("(s.memory.getGlobal " + quote(id2string(symbol.identifier())) + " " +
          bits(expression(initial, out, indent), e.type()) + ")", e.type());
      }
      auto found = names.find(to_symbol_expr(e).identifier());
      if (found == names.end()) fail("nonlocal expression symbol");
      return "s." + found->second;
    }
    if (id == ID_constant) {
      if (e.type().id() == ID_bool) return (e == true) ? "true" : "false";
      if (e.type().id() == ID_pointer) {
        const auto &c = to_constant_expr(e);
        auto v = c.is_null_pointer() ? mp_integer(0) : bvrep2integer(c.get_value(), width(e.type()), false);
        return "(" + integer2string(v) + " : " + type(e.type()) + ")";
      }
      mp_integer v;
      if (to_integer(constant_exprt(e.get(ID_value), representation(e.type())), v))
        fail("invalid bitvector constant");
      return "(" + integer2string(v) + " : " + type(e.type()) + ")";
    }
    if (id == ID_side_effect && e.get(ID_statement) == ID_nondet)
      return havoc(e.type(), out, indent);
    if (id == ID_side_effect && e.get(ID_statement) == ID_allocate) {
      if (e.operands().size() != 2 || e.type().id() != ID_pointer ||
          e.operands()[0].type().id() != ID_unsignedbv || e.operands()[1].type().id() != ID_bool)
        fail("unsupported allocate signature");
      const auto &base = to_pointer_type(e.type()).base_type();
      // CBMC uses the pointee extent for typed allocations, not the size operand.
      auto size = base.id() == ID_empty ? expression(e.operands()[0], out, indent) + ".toNat" :
        std::to_string(byte_size(base));
      auto zero = expression(e.operands()[1], out, indent);
      auto tmp = fresh();
      line(out, indent, "let " + tmp + " ← Memory.allocate " + quote(site()) + " " +
        offset_bits() + " objectBits s.memory " + size + " " + zero);
      line(out, indent, "s := { s with memory := " + tmp + ".2 }");
      return tmp + ".1";
    }
    if (id == ID_overflow_result_mult) {
      if (e.operands().size() != 2 || e.type().id() != ID_struct)
        fail("unsupported multiplication overflow result signature");
      return expression(struct_exprt({
        mult_exprt(e.operands()[0], e.operands()[1]),
        binary_predicate_exprt(e.operands()[0], ID_overflow_mult, e.operands()[1])},
        e.type()), out, indent);
    }
    if (id == ID_string_constant)
      return expression(to_string_constant(e).to_array_expr(), out, indent);
    if (id == ID_index) {
      const auto &a = to_index_expr(e);
      if (a.array().type().id() != ID_array)
        fail("unsupported indexed type " + id2string(a.array().type().id()));
      const auto &t = to_array_type(a.array().type());
      auto value = expression(a.array(), out, indent);
      auto index = index_value(a.index(), out, indent);
      auto tmp = fresh();
      line(out, indent, "let " + tmp + " ← arrayRead " + quote(site()) + " " +
        std::to_string(array_size(t)) + " " + std::to_string(width(e.type())) + " " +
        value + " " + index);
      return from_bits(tmp, e.type());
    }
    if (id == ID_member) {
      const auto &m = to_member_expr(e);
      auto value = expression(m.compound(), out, indent);
      return from_bits("(BitVec.extractLsb' " +
        std::to_string(member_offset(m.compound().type(), m.get_component_name())) + " " +
        std::to_string(width(e.type())) + " " + value + ")", e.type());
    }
    if (id == ID_with) {
      const auto &w = to_with_expr(e);
      auto old = expression(w.old(), out, indent);
      std::string offset, valid = "true";
      if (representation(e.type()).id() == ID_array) {
        auto index = fresh();
        line(out, indent, "let " + index + " := " + index_value(w.where(), out, indent));
        offset = "(" + index + ".toNat * " + std::to_string(width(w.new_value().type())) + ")";
        valid = "decide (0 ≤ " + index + " ∧ " + index + " < " +
          std::to_string(array_size(e.type())) + ")";
      } else offset = std::to_string(member_offset(e.type(), w.where().get(ID_component_name)));
      auto value = bits(expression(w.new_value(), out, indent), w.new_value().type());
      return "(if " + valid + " then replaceBits " + old + " " + offset + " " + value +
        " else " + old + ")";
    }
    if (id == ID_array_of) {
      const auto &element = e.operands().at(0);
      auto value = bits(expression(element, out, indent), element.type());
      return "(arrayOf " + std::to_string(array_size(e.type())) + " " + value + ")";
    }
    if (id == ID_array || id == ID_struct || id == ID_union) {
      const auto total = width(e.type());
      std::string packed = "(0 : BitVec " + std::to_string(total) + ")";
      unsigned offset = 0;
      for (const auto &operand : e.operands()) {
        auto value = bits(expression(operand, out, indent), operand.type());
        packed = "(" + packed + " ||| (shiftLeft (BitVec.setWidth " +
          std::to_string(total) + " " + value + ") " + std::to_string(offset) + "))";
        offset += width(operand.type());
      }
      if (id == ID_union && offset < total) {
        auto padding = fresh();
        line(out, indent, "let " + padding + " ← choose " + quote(site()) + " " +
          std::to_string(total - offset));
        packed = "(" + packed + " ||| (shiftLeft (BitVec.setWidth " +
          std::to_string(total) + " " + padding + ") " + std::to_string(offset) + "))";
      }
      return packed;
    }
    if (id == ID_if) {
      if (e.operands().size() != 3) fail("malformed if expression");
      auto condition = expression(e.operands().at(0), out, indent);
      std::ostringstream yes, no;
      auto a = expression(e.operands().at(1), yes, indent + 2);
      auto b = expression(e.operands().at(2), no, indent + 2);
      if (yes.str().empty() && no.str().empty())
        return "(if " + condition + " then " + a + " else " + b + ")";
      auto tmp = fresh();
      line(out, indent, "let " + tmp + " ← if " + condition + " then do");
      out << yes.str(); line(out, indent + 2, "pure " + a);
      line(out, indent, "else do");
      out << no.str(); line(out, indent + 2, "pure " + b);
      return tmp;
    }
    if (id == ID_typecast) {
      if (e.operands().size() != 1) fail("malformed cast");
      auto value = expression(e.operands().at(0), out, indent);
      const auto &src = e.operands().at(0).type();
      if (e.type().id() == ID_empty) return "()";
      if (e.type().id() == ID_bool) {
        if (src.id() == ID_bool) return value;
        return "(" + value + " != 0)";
      }
      if (e.type().id() == ID_c_bool)
        return "(if " + (src.id() == ID_bool ? value : "(" + value + " != 0)") +
          " then (1 : " + type(e.type()) + ") else 0)";
      if (src.id() == ID_bool)
        return "(if " + value + " then (1 : " + type(e.type()) + ") else 0)";
      if (width(src) == width(e.type())) return value;
      auto method = representation(src).id() == ID_signedbv ? "BitVec.signExtend" : "BitVec.setWidth";
      return "(" + std::string(method) + " " + std::to_string(width(e.type())) + " " + value + ")";
    }
    if ((id == ID_shl || id == ID_lshr || id == ID_ashr) && e.operands().size() == 2) {
      auto value = expression(e.operands().at(0), out, indent);
      const auto &distance = e.operands().at(1);
      std::string shift;
      if (distance.id() == ID_constant) {
        mp_integer n;
        if (to_integer(to_constant_expr(distance), n) || n < 0 || n > 2147483647)
          fail("constant shift distance outside CBMC's supported nonnegative int range");
      }
      if (distance.type().id() == ID_integer && distance.id() == ID_constant) {
        mp_integer n;
        if (to_integer(to_constant_expr(distance), n) || n < 0) fail("invalid shift distance");
        shift = "(" + integer2string(n) + " : Nat)";
      } else shift = "(" + expression(distance, out, indent) + ").toNat";
      if (id == ID_ashr) return "(BitVec.sshiftRight " + value + " " + shift + ")";
      if (id == ID_shl) return "(shiftLeft " + value + " " + shift + ")";
      return "(" + value + " >>> " + shift + ")";
    }
    if ((id == ID_plus || id == ID_minus) && e.type().id() == ID_pointer) {
      std::string pointer, delta = "(0 : Int)";
      for (const auto &operand : e.operands()) {
        if (operand.type().id() == ID_pointer) {
          if (!pointer.empty()) fail("multiple pointers in pointer arithmetic");
          pointer = expression(operand, out, indent);
        } else {
          auto value = id == ID_minus ?
            index_value(unary_minus_exprt(operand), out, indent) : index_value(operand, out, indent);
          delta = "(" + delta + " + " + value + ")";
        }
      }
      if (pointer.empty()) fail("missing pointer in pointer arithmetic");
      return "(Pointer.add " + offset_bits() + " " + pointer + " (" + delta + " * " +
        std::to_string(byte_size(to_pointer_type(e.type()).base_type())) + "))";
    }
    std::vector<std::string> args;
    for (const auto &op : e.operands()) args.push_back(expression(op, out, indent));
    if (args.size() == 1) {
      if (id == ID_is_dynamic_object)
        return "(s.memory.heap.contains (Pointer.object " + offset_bits() + " " + args[0] + "))";
      if (id == ID_pointer_object)
        return "(BitVec.ofNat " + std::to_string(width(e.type())) + " (Pointer.object " +
          offset_bits() + " " + args[0] + "))";
      if (id == ID_pointer_offset)
        return "(BitVec.setWidth " + std::to_string(width(e.type())) + " (BitVec.setWidth " +
          offset_bits() + " " + args[0] + "))";
      if (id == ID_is_invalid_pointer)
        return "(Pointer.object " + offset_bits() + " " + args[0] + " == 1)";
      if (id == ID_object_size) {
        auto tmp = fresh();
        line(out, indent, "let " + tmp + " ← Memory.objectSize " + quote(site()) + " " +
          offset_bits() + " " + std::to_string(width(e.type())) + " s.memory " + args[0]);
        return tmp;
      }
    }
    if (((id == ID_r_ok || id == ID_w_ok || id == ID_rw_ok) && args.size() == 2) ||
        ((id == ID_prophecy_r_ok || id == ID_prophecy_w_ok || id == ID_prophecy_rw_ok) &&
          args.size() == 4)) {
      auto tracked = [&](unsigned index, const std::string &name) {
        return args.size() == 4 ? args[index] :
          "(s.memory.getGlobal " + quote(name) + " (0 : " + type(e.operands()[0].type()) + "))";
      };
      return "(Memory.rwOk " + offset_bits() + " s.memory " + args[0] + " " + args[1] +
        ".toNat " + tracked(2, "__CPROVER_deallocated") + " " + tracked(3, "__CPROVER_dead_object") + ")";
    }
    if ((id == ID_overflow_plus || id == ID_overflow_minus || id == ID_overflow_mult) &&
        args.size() == 2) {
      const auto &t = representation(e.operands()[0].type());
      if (t.id() != ID_signedbv && t.id() != ID_unsignedbv)
        fail("unsupported overflow operand type " + id2string(t.id()));
      const std::string operation = id == ID_overflow_plus ? "add" :
        id == ID_overflow_minus ? "sub" : "mul";
      return "(BitVec." + std::string(t.id() == ID_signedbv ? "s" : "u") + operation +
        "Overflow " + args[0] + " " + args[1] + ")";
    }
    if (id == ID_minus && args.size() == 2 && e.operands()[0].type().id() == ID_pointer &&
        e.operands()[1].type().id() == ID_pointer) {
      auto tmp = fresh();
      line(out, indent, "let " + tmp + " ← pointerDifference " + quote(site()) + " " +
        offset_bits() + " " + std::to_string(width(e.type())) + " " +
        std::to_string(byte_size(to_pointer_type(e.operands()[0].type()).base_type())) + " " +
        args[0] + " " + args[1]);
      return tmp;
    }
    if (args.size() == 1) {
      if (id == ID_not) return "(!" + args[0] + ")";
      if (id == ID_bitnot) return "(~~~" + args[0] + ")";
      if (id == ID_unary_minus) return "(-" + args[0] + ")";
      if (id == ID_unary_plus) return args[0];
    }
    std::string op;
    if (id == ID_plus) op = "+";
    else if (id == ID_minus) op = "-";
    else if (id == ID_mult) op = "*";
    else if (id == ID_bitand) op = "&&&";
    else if (id == ID_bitor) op = "|||";
    else if (id == ID_bitxor) op = "^^^";
    else if (id == ID_and) op = "&&";
    else if (id == ID_or) op = "||";
    else if (id == ID_xor || id == ID_notequal) op = "!=";
    else if (id == ID_equal) op = "==";
    else if (id == ID_implies && args.size() == 2) return "(!" + args[0] + " || " + args[1] + ")";
    if (!op.empty() && args.size() >= 2) {
      std::string value = args.front();
      for (std::size_t i = 1; i < args.size(); ++i) value = "(" + value + " " + op + " " + args[i] + ")";
      return value;
    }
    if (args.size() == 2) {
      if (id == ID_lt || id == ID_le || id == ID_gt || id == ID_ge) {
        auto a = args[0], b = args[1];
        if (id == ID_gt || id == ID_ge) std::swap(a, b);
        if (e.operands()[0].type().id() == ID_pointer)
          return "(Pointer.compare " + offset_bits() + " " +
            (id == ID_le || id == ID_ge ? "true" : "false") + " " + a + " " + b + ")";
        const bool sign = representation(e.operands().at(0).type()).id() == ID_signedbv;
        const std::string comparison = (id == ID_lt || id == ID_gt) ? "lt" : "le";
        return "(BitVec." + std::string(sign ? "s" : "u") + comparison + " " + a + " " + b + ")";
      }
      if (id == ID_div || id == ID_mod) {
        auto tmp = fresh();
        line(out, indent, "let " + tmp + " ← divide " + quote(site()) + " " +
          (representation(e.type()).id() == ID_signedbv ? "true" : "false") + " " +
          (id == ID_mod ? "true" : "false") + " " + args[0] + " " + args[1]);
        return tmp;
      }
    }
    fail("unsupported expression " + id2string(id));
  }

  std::string destination(const exprt &e) {
    if (e.id() != ID_symbol) fail("unsupported assignment destination " + id2string(e.id()));
    auto found = names.find(to_symbol_expr(e).identifier());
    if (found == names.end()) fail("nonlocal assignment");
    return found->second;
  }

  struct Place { std::string field, offset = "0", valid = "true"; };

  Place place(const exprt &e, std::ostream &out, unsigned indent) {
    if (e.id() == ID_symbol) return {destination(e)};
    if (e.id() == ID_member) {
      const auto &m = to_member_expr(e);
      auto p = place(m.compound(), out, indent);
      p.offset = "(" + p.offset + " + " +
        std::to_string(member_offset(m.compound().type(), m.get_component_name())) + ")";
      return p;
    }
    if (e.id() == ID_index) {
      const auto &a = to_index_expr(e);
      auto p = place(a.array(), out, indent);
      auto value = index_value(a.index(), out, indent);
      auto index = fresh();
      line(out, indent, "let " + index + " := " + value);
      p.offset = "(" + p.offset + " + " + index + ".toNat * " + std::to_string(width(e.type())) + ")";
      p.valid = "(" + p.valid + " && decide (0 ≤ " + index + " ∧ " + index + " < " +
        std::to_string(array_size(a.array().type())) + "))";
      return p;
    }
    fail("unsupported assignment destination " + id2string(e.id()));
  }

  void assign(const exprt &lhs, const std::string &value, std::ostream &out, unsigned indent) {
    if (memory_place(lhs)) {
      memory_layout(lhs.type());
      auto p = address(lhs, out, indent), tmp = fresh();
      line(out, indent, "let " + tmp + " ← Memory.store " + quote(site()) + " " + offset_bits() +
        " s.memory " + p + " " + bits(value, lhs.type()));
      line(out, indent, "s := { s with memory := " + tmp + " }");
      return;
    }
    if (lhs.id() == ID_symbol) {
      const auto &id = to_symbol_expr(lhs).identifier();
      if (globals.count(id)) {
        line(out, indent, "s := { s with memory := s.memory.setGlobal " + quote(id2string(id)) +
          " " + bits(value, lhs.type()) + " }");
        return;
      }
      line(out, indent, "s := { s with " + destination(lhs) + " := " + value + " }");
      return;
    }
    auto p = place(lhs, out, indent);
    auto old = "s." + p.field;
    line(out, indent, "s := { s with " + p.field + " := if " + p.valid +
      " then replaceBits " + old + " " + p.offset + " " + bits(value, lhs.type()) + " else " + old + " }");
  }

  bool nondet_call(const Instruction &i) const {
    if (!i.is_function_call()) return false;
    if (i.call_function().id() != ID_symbol || !i.call_arguments().empty()) return false;
    const auto name = id2string(to_symbol_expr(i.call_function()).identifier());
    if (name.rfind("nondet_", 0) != 0 && name.rfind("__VERIFIER_nondet_", 0) != 0) return false;
    auto found = model.goto_functions.function_map.find(name);
    return found == model.goto_functions.function_map.end() || !found->second.body_available();
  }

  bool body_call(const Instruction &i) const {
    if (!i.is_function_call() || i.call_function().id() != ID_symbol) return false;
    auto found = model.goto_functions.function_map.find(to_symbol_expr(i.call_function()).identifier());
    return found != model.goto_functions.function_map.end() && found->second.body_available();
  }

  std::string library_call(const Instruction &i) const {
    if (!i.is_function_call() || i.call_function().id() != ID_symbol || body_call(i)) return {};
    auto name = id2string(to_symbol_expr(i.call_function()).identifier());
    return name == "memcpy" || name == "strlen" || name == "malloc" || name == "free" ? name : "";
  }

  std::vector<std::string> call_arguments(const Instruction &i, std::ostream &out, unsigned indent) {
    std::vector<std::string> values;
    for (const auto &a : i.call_arguments()) {
      auto value = expression(a, out, indent), tmp = fresh();
      line(out, indent, "let " + tmp + " := " + value);
      values.push_back(tmp);
    }
    return values;
  }

  void print_library(const Instruction &i, std::ostream &out, unsigned indent) {
    const auto name = library_call(i);
    if (!i.call_lhs().is_nil() && i.call_lhs().id() != ID_symbol)
      fail("library result requires a local-symbol destination; normalize the GOTO call first");
    auto args = call_arguments(i, out, indent);
    const auto &ret = to_code_type(i.call_function().type()).return_type();
    if (name == "malloc" || name == "free") {
      if (args.size() != 1 || (name == "malloc" ?
          (ret.id() != ID_pointer || i.call_arguments()[0].type().id() != ID_unsignedbv) :
          (ret.id() != ID_empty || i.call_arguments()[0].type().id() != ID_pointer)))
        fail("unsupported " + name + " signature");
      auto tmp = fresh();
      line(out, indent, "let " + tmp + " ← Memory." + name + " " + quote(site()) + " " +
        offset_bits() + (name == "malloc" ? " objectBits" : "") + " s.memory " +
        args[0] + (name == "malloc" ? ".toNat" : ""));
      line(out, indent, "s := { s with memory := " + tmp + (name == "malloc" ? ".2" : "") + " }");
      if (name == "malloc" && !i.call_lhs().is_nil()) assign(i.call_lhs(), tmp + ".1", out, indent);
      return;
    }
    if (args.size() != (name == "memcpy" ? 3u : 1u) ||
        i.call_arguments()[0].type().id() != ID_pointer)
      fail("unsupported " + name + " signature");
    auto tmp = fresh();
    if (name == "memcpy") {
      if (i.call_arguments()[1].type().id() != ID_pointer || ret.id() != ID_pointer ||
          i.call_arguments()[2].type().id() != ID_unsignedbv)
        fail("unsupported memcpy signature");
      line(out, indent, "let " + tmp + " ← Memory.memcpy " + quote(site()) + " " + offset_bits() +
        " s.memory " + args[0] + " " + args[1] + " " + args[2] + ".toNat");
      line(out, indent, "s := { s with memory := " + tmp + ".2 }");
      if (!i.call_lhs().is_nil()) assign(i.call_lhs(), tmp + ".1", out, indent);
    } else {
      if (ret.id() != ID_unsignedbv) fail("unsupported strlen signature");
      line(out, indent, "let " + tmp + " ← Memory.strlen " + quote(site()) + " " + offset_bits() +
        " " + std::to_string(width(ret)) + " s.memory " + args[0]);
      if (!i.call_lhs().is_nil()) assign(i.call_lhs(), tmp, out, indent);
    }
  }

  void print_call(const Instruction &i, std::size_t next, std::ostream &out, unsigned indent) {
    const auto &id = to_symbol_expr(i.call_function()).identifier();
    const auto &callee = model.goto_functions.function_map.at(id);
    const auto &ct = to_code_type(model.symbol_table.lookup_ref(id).type);
    if (ct.has_ellipsis() || i.call_arguments().size() != callee.parameter_identifiers.size())
      fail("variadic or mismatched call arguments");
    if (!i.call_lhs().is_nil() && i.call_lhs().id() != ID_symbol)
      fail("call result requires a local-symbol destination; normalize the GOTO call first");
    auto args = call_arguments(i, out, indent);
    std::string initial = module + identifier(id2string(id)) + ".initial";
    for (std::size_t n = 0; n < args.size(); ++n) {
      if (i.call_arguments()[n].type() != model.symbol_table.lookup_ref(callee.parameter_identifiers[n]).type)
        fail("call argument requires an explicit GOTO typecast");
      initial += " " + args[n];
    }
    const auto tag = "." + identifier(id2string(id));
    line(out, indent, "return .call (" + tag + " (" + initial + " s.memory)) (fun returned => do");
    line(out, indent + 2, "match returned with");
    line(out, indent + 2, "| " + tag + " (" + (i.call_lhs().is_nil() ? "_value" : "value") + ", memory) =>");
    line(out, indent + 4, "let mut s := { s with memory := memory }");
    if (!i.call_lhs().is_nil()) assign(i.call_lhs(), "value", out, indent + 4);
    line(out, indent + 4, "pure (." + identifier(function_name) + " (" + pc(next) + ", s))");
    if (call_variants > 1) {
      line(out, indent + 2, "| _ =>");
      line(out, indent + 4, "check " + quote(site() + "; internal return type") + " false");
      line(out, indent + 4, "pure (." + identifier(function_name) + " (" + pc(next) + ", s))");
    }
    line(out, indent, ")");
  }

  std::string pc(std::size_t index) const { return ".b" + std::to_string(index); }

  void transfer(std::ostream &out, unsigned indent, std::size_t target) const {
    line(out, indent, calls ? "return .next (." + identifier(function_name) + " (" + pc(target) + ", s))" :
      "return .inl (" + pc(target) + ", s)");
  }

  void declarations(std::ostream &out) const {
    out << "abbrev Result := " << type(return_type) << "\n";
    if (memory) out << "abbrev Output := Result × Memory\n";
    out << "\nstructure Locals where\n";
    for (const auto &[id, t] : locals)
      out << "  " << names.at(id) << " : " << (addressed.count(id) ?
        "BitVec " + std::to_string(config.ansi_c.pointer_width) : type(t)) << " := " << zero(t)
          << " -- " << single_line(id2string(id)) << (addressed.count(id) ? " (object address)" : "") << '\n';
    if (memory) out << "  memory : Memory := {}\n";
    out << "  result : Option Result := none\n  deriving Repr\n\ninductive PC where\n";
    for (auto index : leaders) {
      const auto &i = *instructions.at(index);
      out << "  | b" << index << " -- GOTO " << i.location_number;
      if (!i.source_location().get_file().empty()) out << "; " << source_position(i.source_location());
      out << '\n';
    }
    out << "  deriving Repr, BEq\n\nabbrev Frame := PC × Locals\n\n";
  }

  void blocks(std::ostream &out, unsigned indent) {
    for (auto start : leaders) {
      line(out, indent, "| " + pc(start) + " =>");
      for (std::size_t index = start; ; ++index) {
        if (index != start && leaders.count(index)) { transfer(out, indent + 2, index); break; }
        if (!reachable.count(index)) fail("internal block partition error");
        current = instructions.at(index);
        const auto &i = *current;
        // The executable diagnostic below retains the full property text.
        const auto &loc = i.source_location();
        line(out, indent + 2, "-- " + (loc.get_property_id().empty() ? site() :
          function_name + ": GOTO " + std::to_string(i.location_number) + "; " + source_position(loc)));
        if (i.is_decl()) {
          auto value = havoc(i.decl_symbol().type(), out, indent + 2);
          if (addressed.count(i.decl_symbol().identifier())) {
            auto tmp = fresh();
            line(out, indent + 2, "let " + tmp + " ← Memory.alloc " + quote(site()) + " " + offset_bits() +
              " objectBits s.memory " +
              bits(value, i.decl_symbol().type()));
            line(out, indent + 2, "s := { s with " + destination(i.decl_symbol()) + " := " + tmp +
              ".1, memory := " + tmp + ".2 }");
          } else
            line(out, indent + 2, "s := { s with " + destination(i.decl_symbol()) + " := " + value + " }");
        } else if (i.is_assign()) {
          auto value = expression(i.assign_rhs(), out, indent + 2);
          assign(i.assign_lhs(), value, out, indent + 2);
        } else if (i.is_set_return_value()) {
          auto value = expression(i.return_value(), out, indent + 2);
          line(out, indent + 2, "s := { s with result := some " + value + " }");
        } else if (i.is_assert() || i.is_assume()) {
          auto condition = expression(i.condition(), out, indent + 2);
          line(out, indent + 2, i.is_assert() ? "check" : "assume");
          line(out, indent + 4, quote(site()));
          line(out, indent + 4, condition);
        } else if (i.is_goto()) {
          auto condition = expression(i.condition(), out, indent + 2);
          if (!(i.condition() == false)) {
            if (!(i.condition() == true)) line(out, indent + 2, "if " + condition + " then");
            transfer(out, indent + ((i.condition() == true) ? 2 : 4), indices.at(&*i.get_target()));
          }
          if (!(i.condition() == true)) transfer(out, indent + 2, index + 1);
          break;
        } else if (i.is_end_function()) {
          for (const auto &id : addressed)
            line(out, indent + 2, "s := { s with memory := s.memory.release " + offset_bits() + " s." + names.at(id) + " }");
          auto result = [&](const std::string &value) {
            if (calls) return "return .returned (." + identifier(function_name) + " (" + value + ", s.memory))";
            return "return .inr " + (memory ? "(" + value + ", s.memory)" : value);
          };
          if (return_type.id() == ID_empty) line(out, indent + 2, result("()"));
          else {
            line(out, indent + 2, "match s.result with");
            line(out, indent + 2, "| some value => " + result("value"));
            line(out, indent + 2, "| none =>");
            auto value = havoc(return_type, out, indent + 4);
            line(out, indent + 4, result(value));
          }
          break;
        } else if (i.is_function_call() && nondet_call(i)) {
          const auto &t = to_code_type(i.call_function().type()).return_type();
          auto value = havoc(t, out, indent + 2);
          if (!i.call_lhs().is_nil())
            assign(i.call_lhs(), value, out, indent + 2);
        } else if (!library_call(i).empty()) {
          print_library(i, out, indent + 2);
        } else if (calls && body_call(i)) {
          print_call(i, index + 1, out, indent + 2);
          break;
        } else if (i.is_other() && i.code().get_statement() == ID_expression) {
          expression(to_code_expression(i.code()).expression(), out, indent + 2);
        } else if (i.is_dead() && addressed.count(i.dead_symbol().identifier())) {
          line(out, indent + 2, "s := { s with memory := s.memory.release " + offset_bits() + " s." +
            destination(i.dead_symbol()) + " }");
        } else if (!i.is_skip() && !i.is_location() && !i.is_dead()) {
          std::ostringstream kind;
          kind << i.type();
          if (i.is_function_call() && i.call_function().id() == ID_symbol)
            kind << " " << to_symbol_expr(i.call_function()).identifier();
          fail("unsupported instruction " + kind.str());
        }
      }
    }
    current = nullptr;
  }

  void initial_definition(std::ostream &out) const {
    out << "\ndef initial";
    for (const auto &id : function.parameter_identifiers)
      out << "\n    (" << names.at(id) << " : " << type(locals.at(id)) << ")";
    if (memory) out << "\n    (memory : Memory := {})";
    out << " : Frame :=\n  (" << pc(0) << ", {";
    bool first = true;
    for (const auto &id : function.parameter_identifiers) {
      out << (first ? "\n    " : ",\n    ") << names.at(id) << " := " << names.at(id); first = false;
    }
    if (memory) out << (first ? "\n    " : ",\n    ") << "memory := memory";
    out << " })\n";
  }

  std::string print() {
    prepare();
    std::ostringstream out;
    out << "-- Generated by goto-lean; edit proofs and harnesses in separate modules.\n"
        << "import GotoLean\n\nnamespace " << identifier(function_name) << "\nopen GotoLean\n\n";
    abi(out);
    const std::string output = memory ? "Output" : "Result";
    declarations(out);
    out << "def step (frame : Frame) : Action (Next Frame " << output << ") := do\n"
        << "  let (pc, initial) := frame\n  let mut s := initial\n  match pc with\n";
    blocks(out, 2);
    initial_definition(out);
    std::string binders, arguments;
    for (const auto &id : function.parameter_identifiers) {
      binders += "\n    (" + names.at(id) + " : " + type(locals.at(id)) + ")";
      arguments += " " + names.at(id);
    }
    auto memory_binder = memory ? "\n    (memory : Memory := {})" : "";
    if (memory) arguments += " memory";
    out << "\ndef run" << binders << memory_binder << " : Program " << output << " :=\n"
        << "  GotoLean.run step (initial" << arguments << ")\n"
        << "\ndef eval" << binders << "\n    (fuel : Nat) (choices : List Nat := [])" << memory_binder << " :\n"
        << "    Outcome " << output << " × List Nat :=\n"
        << "  evalLoop step (fun frame => reprStr frame.1) fuel (initial" << arguments << ") choices\n"
        << "\nend " << identifier(function_name) << '\n';
    return out.str();
  }
};
}

std::string print_lean(const goto_modelt &model, const std::string &function) {
  auto found = model.goto_functions.function_map.find(function);
  if (found == model.goto_functions.function_map.end())
    throw std::runtime_error("function not found: " + function);
  std::map<std::string, std::unique_ptr<Printer>> functions;
  std::deque<std::string> queue{function};
  bool calls = false;
  while (!queue.empty()) {
    auto name = queue.front(); queue.pop_front();
    if (functions.count(name)) continue;
    auto p = std::make_unique<Printer>(model, model.goto_functions.function_map.at(name), name);
    p->prepare();
    for (auto index : p->reachable) {
      const auto &i = *p->instructions[index];
      if (p->body_call(i)) {
        calls = true;
        queue.push_back(id2string(to_symbol_expr(i.call_function()).identifier()));
      }
    }
    functions.emplace(name, std::move(p));
  }
  if (!calls) return functions.at(function)->print();
  std::set<std::string> tags;
  const std::string module = "Functions.";
  std::ostringstream out;
  out << "-- Generated by goto-lean; direct calls use a shared Lean call stack.\n"
      << "import GotoLean\n\nnamespace " << identifier(function) << "\nopen GotoLean\n\n";
  for (const auto &[name, p] : functions)
    if (p->memory) { p->abi(out); break; }
  out << "namespace Functions\n\n";
  for (auto &[name, p] : functions) {
    if (!tags.insert(identifier(name)).second) throw std::runtime_error("function-name collision: " + name);
    p->calls = true;
    p->module = module;
    p->call_variants = functions.size();
    p->prepare();
    out << "namespace " << identifier(name) << "\n\n";
    p->declarations(out);
    p->initial_definition(out);
    out << "\nend " << identifier(name) << "\n\n";
  }
  out << "end Functions\n\ninductive Activation where\n";
  for (const auto &[name, p] : functions)
    out << "  | " << identifier(name) << " (frame : " << module << identifier(name) << ".Frame)\n";
  out << "  deriving Repr\n\ninductive Value where\n";
  for (const auto &[name, p] : functions)
    out << "  | " << identifier(name) << " (value : " << module << identifier(name) << ".Output)\n";
  out << "\nabbrev Output := " << module << identifier(function) << ".Output\n"
      << "abbrev Frame := CallState Activation Value\n\n"
      << "def body (frame : Activation) : Action (Transfer Activation Value) := do\n"
      << "  match frame with\n";
  for (auto &[name, p] : functions) {
    out << "  | ." << identifier(name) << " frame =>\n"
        << "    let (pc, initial) := frame\n    let mut s := initial\n    match pc with\n";
    p->blocks(out, 4);
  }
  out << "\ndef finish (value : Value) : Action Output := do\n  match value with\n"
      << "  | ." << identifier(function) << " result => pure result\n";
  if (functions.size() > 1)
    out << "  | _ =>\n    check \"internal entry return type\" false\n    pure ("
        << (functions.at(function)->return_type.id() == ID_empty ? "()" :
          functions.at(function)->zero(functions.at(function)->return_type)) << ", {})\n";
  out << "\ndef step : Step Frame Output := callStep body finish\n";
  const auto &root = *functions.at(function);
  std::string binders, arguments;
  for (const auto &id : root.function.parameter_identifiers) {
    binders += "\n    (" + root.names.at(id) + " : " + root.type(root.locals.at(id)) + ")";
    arguments += " " + root.names.at(id);
  }
  out << "\ndef initial" << binders << "\n    (memory : Memory := {}) : Frame :=\n"
      << "  (." << identifier(function) << " (" << module << identifier(function) << ".initial" << arguments
      << " memory), [])\n"
      << "\ndef run" << binders << "\n    (memory : Memory := {}) : Program Output :=\n"
      << "  GotoLean.run step (initial" << arguments << " memory)\n"
      << "\ndef eval" << binders << "\n    (fuel : Nat) (choices : List Nat := []) (memory : Memory := {}) :\n"
      << "    Outcome Output × List Nat :=\n"
      << "  evalLoop step (fun frame => reprStr frame.1) fuel (initial" << arguments << " memory) choices\n"
      << "\nend " << identifier(function) << '\n';
  return out.str();
}
