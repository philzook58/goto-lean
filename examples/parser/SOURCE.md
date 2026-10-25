# Source

`take_word.c` contains locally written repair helpers, `take_word` and `copy_word`,
from the AI-assisted `cornell-serial-assurance` workspace experiment. Its source
is `src/fixed_step.inc`; `scripts/prepare.py` extracts the helpers into
`generated/take_word.inc`. The standalone example adds its own small `main`.
These helpers are not functions from the original Cornell firmware.

The motivating firmware and course material are Cornell ECE 4760's
[serial-interface example](https://people.ece.cornell.edu/land/courses/ece4760/RP2040/C_SDK_serial/serial_terminal.html)
and [serial_cmd.c](https://people.ece.cornell.edu/land/courses/ece4760/RP2040/C_SDK_serial/brl4_serial_interface/serial_cmd.c).
The local experiment records downloads on 2026-10-21. Their original authorship
and notices belong to those upstream artifacts, not to an asserted upstream
version of these new helpers.

No published revision or explicit license for the local repair was recorded.
That provenance/license gap remains unresolved; this example must not be described
as an MIT-licensed or otherwise license-verified Cornell source snapshot.
