//
//  GrammarDiagnostics.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.04.12.
//

import OSLog

extension GrammarNode {

//  What it computes: pairwise intersections of alternates' FIRST sets, plus FIRST ∩ FOLLOW where the node is nullable. Pure set arithmetic over terminal IDs, done once at grammar load from the FIRST/FOLLOW fixpoint. It also populates node.ambiguous, which the tracing/diagnostics read.
//
//  Who consumes it: grammar.isLL1, asserted by LL1DetectionTests against small textbook grammars, and printed by main.swift. Nothing in the parser. Since isLocallyLL1 is gone, verifyLL1's result no longer influences parsing at all.
//
//  So it reliably means exactly one thing: no terminal ID appears in two alternates' FIRST sets (or in FIRST and FOLLOW when nullable). That is a statement about grammar symbols.
//
//  What it does not mean — and this is the part that's stale relative to lex-on-demand: it does not mean at most one alternate can be predicted at a given input position. Three reasons, all of which survive symbol-disjointness:
//
//    • Distinct terminal IDs can co-match the same characters — an identifier regex and the literal "for" are different IDs with disjoint FIRST sets, and both match for.
//    • testSelect asks the lexer a per-position question ("does any terminal in this alternate's FIRST match here?"). Set disjointness cannot answer it.
//    • The lexer returns a set of matches of differing lengths — maximal munch isn't global — so even a single terminal can fork.
//
//  verifyLL1 is a grammar-structure signal — useful for the detection tests, for main's report, and for populating ambiguous — but it is no longer, and can no longer be treated as, a parser precondition. Anyone reading "LL1 is true" should not infer prediction determinism.

    @discardableResult
    func verifyLL1() -> Bool {
        var subtreeIsLL1 = true
        switch kind {
        case .EOS, .T, .TI, .C, .B, .EPS:
            if seq?.verifyLL1() == false { subtreeIsLL1 = false }
        case .N:
            if let seq { // rhs
                if !seq.verifyLL1() { subtreeIsLL1 = false }
                // For a RHS nonterminal, check the definition's FIRST (via alt)
                // against this position's FOLLOW. The positional 'first' includes
                // look-through tokens from the continuation, which would cause
                // false conflicts.
                if let production = alt, production.isNullable {
                    let definitionFirst = production.first.subtracting([""])
                    ambiguous = definitionFirst.intersection(follow)
                }
            } else { // lhs
                if !handleAlternatesAmbiguity() { subtreeIsLL1 = false }
            }
        case .ALT:
            if seq?.verifyLL1() == false { subtreeIsLL1 = false }
        case .DO, .POS, .OPT, .KLN:
            if seq?.verifyLL1() == false { subtreeIsLL1 = false }
            if !handleAlternatesAmbiguity() { subtreeIsLL1 = false }
        case .END:
            break
        }
        if !ambiguous.isEmpty {
            subtreeIsLL1 = false
        }
        return subtreeIsLL1
    }

    private func handleAlternatesAmbiguity() -> Bool {
        // ambiguity set of KLN and POS is the intersection of follow(KLN) with the union of the pairwise intersections of all its first(ALT)'s ('duplicates')
        var subtreeIsLL1 = true

        var occurances: [String:Int] = [:]
        // count occurances in firsts
        var current = self.alt
        while let altNode = current {
            if current?.verifyLL1() == false { subtreeIsLL1 = false }
            for element in altNode.first {
                occurances[element, default: 0] += 1
            }
            current = altNode.alt
        }
        // count occurances in follow only when this node can derive ε,
        // because a token in FOLLOW then competes with the alternates' FIRST tokens
        if isNullable {
            for element in follow {
                occurances[element, default: 0] += 1
            }
        }
        // keep only duplicated occurances
        for (element, count) in occurances where count > 1 {
            ambiguous.insert(element)
        }
        if !ambiguous.isEmpty {
            subtreeIsLL1 = false
        }

        return subtreeIsLL1
    }
}

extension GrammarNode {

    func detectSchrödingerConflict() {
        switch kind {
        case .EOS, .T, .TI, .C, .B, .EPS:
            seq?.detectSchrödingerConflict()
        case .N:
            if let seq { // rhs
                seq.detectSchrödingerConflict()
            } else { // lhs
                handleAlternatesSchrödingerConflict()
            }
        case .ALT:
            seq?.detectSchrödingerConflict()
        case .DO, .POS, .OPT, .KLN:
            seq?.detectSchrödingerConflict()
            handleAlternatesSchrödingerConflict()
        case .END:
            break
        }
        identifierKeywordConflict()
    }

    func possibleMatch(of tokenType: String, with: String) -> Bool {
        return true
    }
    
    func possibleIdentifier(_ element: String) -> Bool {
        let startsWithLetter = element.first?.isLetter ?? false
        let isLiteral = GrammarNode.grammar?.terminals[element]?.isLiteral == true
        return startsWithLetter && isLiteral
    }
    
    func identifierKeywordConflict() {
        if first.contains("plainIdentifier") {
            let overlap = Set(first.filter { possibleIdentifier($0) })
            if !overlap.isEmpty {
                print("Schrödinger NODE plainIdentifier ~ \(overlap.sorted())\n  \(self.ebnfDot())")
            }
        }
    }

    private func handleAlternatesSchrödingerConflict() {
        // Schrödinger tokens may match additional branches compared with the pure FIRST and FOLLOW sets.
        // this creates more GLL descriptors and more work.
        // here we check ambiguous overlap between plainIdentifier and keywords
        var schrödingerAlert = false
        var conflicts: Set<String> = []
        
        var current = self.alt
        while let altNode = current {
            current?.detectSchrödingerConflict()
//            Logger.grammar.debug("ALT: \(altNode.first.sorted())")
            if first.contains("plainIdentifier") {
                schrödingerAlert = true
            } else {
                for element in altNode.first {
                    if possibleIdentifier(element) {
                        conflicts.insert(element)
                    }
                }
            }
            current = altNode.alt
        }
        
        // inspect elements in follow only when this node can derive ε,
        // because a token in FOLLOW then competes with the alternates' FIRST tokens
        if isNullable {
            if follow.contains("plainIdentifier") {
                schrödingerAlert = true
            } else {
                for element in follow {
                    if possibleIdentifier(element) {
                        conflicts.insert(element)
                    }
                }
            }
        }
        if schrödingerAlert && !conflicts.isEmpty {
            print("Schrödinger ALTERNATES plainIdentifier ~ \(conflicts.sorted())\n  \(self.ebnfDot())")
        }
    }
    
}

// MARK: - Predicate target reachability (TODO.md / Make trivia handling principled)

extension Grammar {

    /// Flag `@canParse(N)` / `@cannotParse(N)` whose target can NEVER be predicted.
    ///
    /// `LookaheadPredicateRule` answers "does `N` derive here?" by querying `N`'s yields. An empty
    /// answer is ambiguous — `N` was attempted and failed (a real **false**), or `N` was never
    /// attempted (the query is **blind**) — and blind resolves to the PERMISSIVE verdict: a negated
    /// predicate with no target yields prunes nothing, so `@cannotParse(N)` silently becomes `true`.
    /// `Grammar Predicate Lookahead Design.md` calls that "a specification error, not a silent
    /// false"; this is that error being raised.
    ///
    /// SCOPE — this catches the UNCONDITIONALLY blind cases only: a target that no production body
    /// mentions, or that nothing reachable from the root mentions. It cannot catch a target that is
    /// referenced somewhere but not predicted AT THE ANCHOR, which is what bit
    /// `@cannotParse(accessorBlockBrace)` (referenced by `getterSetterBlock`, hence reachable, but
    /// never predicted at a *variable* brace). Deciding that statically needs per-dotted-position
    /// reachability — an LR(0)-style item closure — which this deliberately does not build, so the
    /// anchor-local half of the class still has to be checked by hand. TODO.md / Make trivia handling principled records why the
    /// runtime alternative (seeding a sub-parse when the query looks blind) was tried and reverted.
    ///
    /// Returns one message per blind site (empty = clean) as well as logging, so tests can assert on
    /// the result instead of scraping OSLog.
    @discardableResult
    func diagnosePredicateTargets() -> [String] {
        var findings: [String] = []
        var targets: [(target: String, owner: String)] = []
        var referenced: Set<String> = []
        var seen = Set<ObjectIdentifier>()

        func walk(_ node: GrammarNode?, owner: String) {
            guard let node, seen.insert(ObjectIdentifier(node)).inserted else { return }
            for predicate in node.forwardPredicates {
                targets.append((predicate.targetName, owner))
            }
            // A symbol occurrence in an alternate body is what makes a name PREDICTABLE. Names that
            // appear only as predicate operands never get a descriptor.
            for symbol in node.bodySymbols {
                referenced.insert(symbol.name)
            }
            if node.kind != .END { walk(node.seq, owner: owner) }
            walk(node.alt, owner: owner)
        }
        for (name, nt) in nonTerminals { walk(nt, owner: name) }

        // Reachability from the root, following body symbols.
        var live: Set<String> = []
        var queue: [String] = nonTerminals[root.name] != nil ? [root.name] : Array(nonTerminals.keys.filter { $0 == root.name })
        if queue.isEmpty, let start = grammarRootName { queue = [start] }
        while let name = queue.popLast() {
            guard live.insert(name).inserted, let nt = nonTerminals[name] else { continue }
            var altSeen = Set<ObjectIdentifier>()
            func collect(_ node: GrammarNode?) {
                guard let node, altSeen.insert(ObjectIdentifier(node)).inserted else { return }
                for symbol in node.bodySymbols where nonTerminals[symbol.name] != nil {
                    queue.append(symbol.name)
                }
                if node.kind != .END { collect(node.seq) }
                collect(node.alt)
            }
            collect(nt)
        }

        for (target, owner) in targets {
            guard nonTerminals[target] != nil || terminals[target] != nil else {
                findings.append("undefined predicate target '\(target)' used by '\(owner)'")
                continue
            }
            // Terminal operands are a lexical peek, not a yield query, so reachability is moot.
            guard terminals[target] == nil else { continue }
            if !referenced.contains(target) {
                findings.append("""
                    BLIND PREDICATE: '\(target)' is named only as a predicate operand (by '\(owner)') \
                    and appears in no production body, so it is never predicted and the predicate is \
                    vacuously satisfied everywhere. Reference it from a production, or seed it. \
                    See TODO.md / Make trivia handling principled.
                    """)
            } else if !live.isEmpty && !live.contains(target) {
                findings.append("""
                    BLIND PREDICATE: '\(target)' (used by '\(owner)') is unreachable from the grammar \
                    root, so it is never predicted and the predicate is vacuously satisfied \
                    everywhere. See TODO.md / Make trivia handling principled.
                    """)
            }
        }
        for finding in findings {
            Logger.grammar.error("\(finding, privacy: .public)")
        }
        return findings
    }

    /// The name of the nonterminal the parser actually starts from, when `root` is the EOS sentinel.
    private var grammarRootName: String? {
        root.seq?.name ?? nonTerminals.keys.first
    }
}
