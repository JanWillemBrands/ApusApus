# Active TODO

This file is the canonical active TODO list for the project. It holds actionable items only; put
completed work and historical explanations in design notes or commit messages.

1. **`$` inside an identifier is rejected: `_$id`, `a$b`.**
    5 files in the crawl, all FluentKit, which declares `var _$id` as a protocol requirement and
    then uses `From()._$id.field.key`. Confirmed ground truth: `swiftc -parse` ACCEPTS both
    `struct S { var _$id: Int = 0 }` and `let v = a$b`. Our failure sites put `<HERE>` exactly at
    the `$` (`var _<HERE>$id`, `let v = a<HERE>$b`), so the lexer stops the identifier there.
    - Fix in `ApusApus/SwiftGrammarRegexLibrary.swift`: `identifierCharacter` (line ~84) does not
      include `$`. `identifierHead` (line ~65) must NOT get it — a LEADING `$` is the property
      wrapper projection (`$foo`), which is already its own terminal
      (`propertyWrapperProjection`), and admitting `$` in head position would make the two
      terminals overlap.
    - Check first what swift-syntax's lexer does (`Sources/SwiftParser/Lexer/Lexer+Cursor.swift`,
      `advanceIfValidContinuationOfIdentifier`) — it diagnoses `$` in identifiers in some
      positions, so the accepted set may be narrower than "any non-initial `$`". Ground the change
      in that function plus `swiftc -parse`, not in TSPL, whose `identifier-character` omits `$`.
    - Reproducers: the 5 non-`same` files in `/tmp/crawlW/results.jsonl`.

## Maintenance Rule

- Add new TODOs here only when they are active and actionable.
- Move completed investigations and historical explanations to design notes or commit messages.
- `codex.md` and `claude.md` reference this file instead of maintaining separate TODO lists.
