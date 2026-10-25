#!/usr/bin/env python3
"""Compile a handwritten spec and audit explicitly named public claims."""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True,
                        help='generated Lake project containing Model.lean')
    parser.add_argument('--spec', default='Spec.lean', help='spec path relative to project')
    parser.add_argument('--claim', action='append', default=[], help='public theorem to audit; repeat as needed')
    parser.add_argument('--completion-claim', action='append', default=[],
                        help='audit and require a public finishes statement')
    parser.add_argument('--replay-only', action='store_true', help='compile concrete checks without claiming a proof')
    parser.add_argument('--memory-mb', type=int, default=1024,
                        help='Lean memory limit in MB for compilation and audit (default: 1024)')
    args = parser.parse_args()
    if args.memory_mb <= 0:
        parser.error('--memory-mb must be positive')
    project = args.project.resolve()
    spec = (project / args.spec).resolve()
    if not spec.is_file():
        parser.error(f'missing spec: {spec}')
    claims = args.claim + args.completion_claim
    if bool(claims) == args.replay_only:
        parser.error('choose named claims or --replay-only')
    if any(not re.fullmatch(r"[A-Za-z_][\w.']*", name) for name in claims):
        parser.error('claims must be qualified Lean identifiers')

    def check(path):
        command = ['lake', '-d', str(project), 'lean', str(path), '--', '-j1',
                   f'-M{args.memory_mb}']
        print('Checking ' + str(path), flush=True)
        subprocess.run(command, check=True, cwd=project)

    check(spec)
    if args.replay_only:
        print('Concrete checks compiled. No universal theorem was audited.')
        return
    # Audit a copy of the exact current file; leave the user's spec untouched.
    text = 'import GotoLean.Audit\nimport GotoLean.Termination\n' + spec.read_text()
    text += '\n' + '\n'.join('#check_axioms ' + name for name in claims) + '\n'
    for name in args.completion_claim:
        text += f'''\nrun_cmd Lean.Elab.Command.liftTermElabM do
  let declaration ← Lean.getConstInfo `{name}
  Lean.Meta.forallTelescope declaration.type fun _ result => do
    unless result.isAppOf `GotoLean.finishes do
      throwError "{name}: expected a public finishes theorem; WP alone does not state completion"
'''
    # Keep source-relative resources (e.g. proof certificates) in the same place.
    with tempfile.NamedTemporaryFile(mode='w', prefix='AuditSpec_', suffix='.lean',
                                     dir=spec.parent, delete=False) as temporary:
        temporary.write(text)
        audit = Path(temporary.name)
    try:
        check(audit)
    finally:
        audit.unlink(missing_ok=True)
    print('Compiled and axiom-audited: ' + ', '.join(claims))
    print('Review each theorem statement separately for the requested scope.')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode)
