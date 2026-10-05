# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Put completed work and historical explanations in design notes or commit messages.

1. DONE 2026-10-05 — `macroHead = "#" >s< ( propertyWrapperProjection | escapedIdentifier )`: the
    dollar-name alternate now also takes a backtick-escaped name, since swift-syntax lexes both as
    ordinary identifier tokens after `#` (so `#\`if\`` is a macro, not a directive, and needs none of
    `poundName`'s exclusions). No converter change: the head text minus `#` is already swift-syntax's
    token text. 11/11 focused shapes `same` (generic args, trailing closure, declaration position,
    spaced `# \`x\`` still rejected); `MiscellaneousTests.swift` underaccept → `same`; slice 0
    changes; fixtures `macro-escaped-*`. Original item follows.
    Accept escaped macro names such as `#\`expect\`(...)`. The crawl rejects
    apple/swift-testing's `#\`expect\`(Bool(true))`, expecting `::` after the escaped identifier.
    `macroHead` uses `poundName` plus exclusions and a module-selector form; it likely needs an
    escaped-identifier macro-head path rather than treating `#` + escaped identifier as a module
    selector start.

2. DONE 2026-10-05 — one `objcSelectorName = identifier | escapedIdentifier` now serves both the
    bare selector and every piece, as swift-syntax `parseObjectiveCSelector` does (keywords and `_`
    already came through the raw `identifier` terminal). The escaped PIECE form `@objc(\`x\`:)`
    failed too, not just the bare one. The converter reads the shared rule instead of the
    `identifier` terminal at both sites. 13/13 focused shapes `same` (two rejects kept);
    `ObjCInteropTests.swift` underaccept → `same`; 60 `@objc(…)` files `same`; slice 0 changes;
    fixtures `objc-escaped-*`. Original item follows.
    Accept escaped bare ObjC selector names in `@objc(...)`. The crawl rejects
    `@objc(\`testExplicitNameWithBackticks\`)` in apple/swift-testing. `objcSelector = identifier`
    covers bare unescaped names, and `objcSelectorPiece = identifier? ":"` covers colon pieces; add
    the escaped bare-name case without broadening selector pieces more than SwiftSyntax does.

3. Fix interpolated-string parsing for qualified generic member expressions. The
    swift-distributed-actors close-brace failure from the 2026-10-03 crawl reduced to the standalone
    compiler/swift-syntax-accepted snippet `let s = "\(A.B<C>.d)"`, which APUS underaccepts at EOF.
    Controls: `let s = "\(A.B<C>)"`, `let s = "\(A.B.d)"`, and `let x = A.B<C>.d` are all `same`.
    The original late failure in `AggressiveNodeReplacementClusteredTests.swift` came from
    `"Registering actor with \(DistributedReception.Key<ServiceActor>.aggressiveNodeReplacementService)!"`
    poisoning the parse until the following member body. This is separate from the statement-condition
    newline-closure mode leak tracked in #5.

4. DONE 2026-10-05 — applied: `typeMemberName = >-> ( "Type" "Protocol" ) identifierToken | "self"`,
    and `@prefer` dropped from `type`'s `metatypeType` alternate. 4/4 crawl files `same`; slice: the
    one ambiguity → `same`, 0 other changes; suite 47 → 45 failures (both
    `testSuppressedImplicitConformance#3` ambiguity assertions resolved); six `metatype-*` /
    `member-type-*` fixtures. Original analysis follows.
    Remove the metatype/member-type ambiguity under a postfix. Found by the 2026-10-04 partial
    crawl (all 4 of its residual ambiguities: IBAnimatable, LiveContainer, 2× SwiftUIX), fingerprint
    `simpleType ambiguous alternate [memberType] | [metatypeType]`. Minimal: `let t: P.Type? = nil`.
    Every `X.Type?`, `X.Type!`, `X.Protocol?` and `X.Type.Type` is ambiguous; a bare `X.Type` is
    not. Cause: `X.Type` derives both as `metatypeType = simpleType "." ( "Type" | "Protocol" )` and
    as `memberType = simpleType "." typeMemberName`, because `typeMemberName = identifierToken |
    "self"` and `Type`/`Protocol` lex as identifiers. At top level `type`'s `@prefer metatypeType`
    hides it; once the metatype is the BASE of `?`/`!`/`.Type` it sits in `simpleType`, which lists
    both alternates with no preference. swift-syntax's member loop tests `.Type`/`.Protocol` FIRST,
    so `X.Type` is never a member type. Principled fix: exclude `Type`/`Protocol` from
    `typeMemberName`; the `@prefer metatypeType` on `type` should then be redundant and removable.
    TESTED 2026-10-05 on a scratch copy only (not applied — Codex owns the change):
    `typeMemberName = >-> ( "Type" "Protocol" ) identifierToken | "self" .` makes all 4 crawl files
    and 4/4 minimal shapes `same`, with 8 neighbours unchanged (`A.B`, `A.B.C?`, `A.Types`,
    `A.TypeX`, `[any Markup].Index`, `(each T).Output`, `Foo.Type.self`, bare `P.Type`); 1,593-file
    slice: 1 change, the slice's only ambiguity → `same`. Dropping `@prefer` from
    `| @prefer metatypeType` on top of that gives byte-identical results, so it is redundant.

5. Scope the "no newline-opened closure in a statement condition" rule to the condition itself.
    OpenEmu `FileManager+Hashing.swift` reduces to
        while g(x: {
          d.h {
          }
        }) {}
    which swiftc and swift-syntax accept, and APUS rejects at the final `}`. The same holds for `if`
    and `guard`; the one-line form `while g(x: { d.h { } }) {}` passes. Cause:
    `closureExpression = samelineOpenedClosure | @excludedFrom(conditionExpression) … newlineOpenedClosure`
    models swift-syntax's `.stmtCondition` flavor (a brace opening a new line is the statement
    body, not a trailing closure), but `@excludedFrom` is SPAN CONTAINMENT and applies at any
    depth. The two annotations are a CONJUNCTION (prune only where inside both), so the rule really
    reads "a newline-opened closure that is a trailing closure, anywhere inside a condition".
    Measured 2026-10-05 on the unmodified grammar: multi-line closure ARGUMENTS in conditions are
    fine (`if g(x: {⏎1⏎}) {}`, unlabeled, in an array, in parens, `guard`, `while let` — all
    `same`), and condition-LEVEL trailing closures are fine; the only failure is a trailing closure
    NESTED inside an argument or closure body within the condition. It is the only
    `@excludedFrom(conditionExpression)` in the grammar. In swift-syntax the flavor resets inside nested contexts — argument lists and closure
    bodies are parsed with `.basic` flavor — so a trailing closure nested in a call argument inside
    the condition is legal. What is needed is "excluded only while the NEAREST enclosing context
    is the condition", which plain containment cannot say. Current design direction: replace
    containment with scoped parser modes, as detailed in `documentation/Parser Modes Migration Plan.md`.
    The remaining close-brace/EOF bucket from TODO #3 also mostly collapses into this issue:
      - `AutomaticDictionaryTrainingSession.swift`:
            func f() {
              a {
                guard x,
                      b.contains(where: {
                        $0 == y
                      }) else { return }
              }
            }
      - `PronunciationDictionaryStore.swift`:
            func f() throws {
              guard a.allSatisfy({ x in
                b.allSatisfy {
                  $0 == x
                }
              }) else { throw E.x }
            }
      - `GitHubCopilotModelPicker.swift` / `SuggestionSettingsGeneralSectionView.swift`:
            func f() {
              Form {
                Picker(content: {
                  if !models.contains(where: {
                    $0.id == x
                  }) {
                    Text("x")
                  }
                })
              }
            }
      - `TestReducerRunner.swift`:
            func f() {
              if a.contains(where: { x in b.contains {
                $0 == x
              } }) { continue }
            }
    In all four shapes, the same construct passes when parsed outside statement-condition context;
    the failure appears only when a nested unlabeled/labeled trailing closure remains inside the
    condition by BSR span containment.
