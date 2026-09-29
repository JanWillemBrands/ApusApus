# Active TODO

This file is the canonical active TODO list for the project. It holds actionable items only; put
completed work and historical explanations in design notes or commit messages.

1. **`where` on its own line after a generic clause is rejected.**
    8 + 8 files. Failure sites `x>⏎        <HERE>where x: x` and `, x>⏎        <HERE>where x: x`,
    expected `"#" "#if" "#sourceLocation"`. A `where` clause on the line after `>` — likely a
    layout gate (`>n<`) that should permit a line break there.
