# Active TODO

1. Fix the regex/operator boundary overaccept:
   ```swift
   x
   =/0/
   ```
   `swiftc` and SwiftSyntax reject the asymmetric `=`, but ApusApus accepts it.

2. Accept `@abi` subscript declarations:
   ```swift
   struct S<Element> {
       @abi(subscript(i: Int) -> Element)
       subscript(i: Int) -> Element { fatalError() }
   }
   ```
   This compiles, but ApusApus rejects it.

3. Reject unknown macro introduced-name kinds:
   ```swift
   @attached(member, names: discard(class))
   macro m()
   ```
   `swiftc` and SwiftSyntax reject it, but ApusApus accepts it. Macro role errors such as
   `@freestanding(member)` are compiler/SwiftSyntax disagreements and are out of scope.

4. Fix directive boundaries:
   - Accept a trailing comment after an empty `#sourceLocation`:
     ```swift
     #sourceLocation(file: "x", line: 1)
     #sourceLocation() // comment
     ```
   - Reject residue on a `#if` directive:
     ```swift
     #if A @objc
     #endif
     func f() {}
     ```

5. Reject duplicate accessors:
   ```swift
   protocol P { var x: Int { get get throws } }
   ```
   Fix the duplicate/effect invariants before considering cases where `swiftc` and SwiftSyntax
   disagree, such as some `_modify`-without-get forms.

6. Remove the key-path residual ambiguity:
   ```swift
   #if NEVER
   \T
   .
   Protocol
   #endif
   ```
   ApusApus retains `keyPathComponents` and `keyPathExpressionStop` readings.

7. Remove the `yield` residual ambiguity:
   ```swift
   var f: () -> Void { _read { yield { } } }
   ```
   ApusApus retains expression-statement and `yieldStatement` readings.

8. Remove the `_effects` token residual ambiguity:
   ```swift
   @_effects(notEscaping _)
   func f() {}
   ```
   ApusApus retains `identifier` and `nonWordToken` readings for `_`.

9. After fixing acceptance and residual ambiguities, audit the 39 AST tree differences. Start with:
   ```swift
   import A
   .B.C
   ```
   Require a normalized structural difference before investigating a `no-normalized-difference`
   result.
