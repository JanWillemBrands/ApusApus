# Active TODO

This file is the canonical active TODO list.

1. Re-audit the 25 isolated-compiler/SwiftSyntax disagreements from the top-100 crawl in their originating project build contexts. A bare `swiftc -parse` rejection is not authoritative when package flags, availability-macro definitions, imports, or generated configuration are missing; `_uttypesAPI` proved this for `@available`.
