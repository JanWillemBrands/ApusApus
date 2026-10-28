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

// MARK: - Predicate targets

extension Grammar {

    /// Reachability from the start symbol, following production bodies across flavor copies.
    func computeParsedNonTerminals() -> Set<String> {
        var parsed: Set<String> = []
        var queue = [root.seq?.name ?? startSymbol].filter { nonTerminals[$0] != nil }
        while let name = queue.popLast() {
            guard parsed.insert(name).inserted else { continue }
            var seen = Set<ObjectIdentifier>()
            func collect(_ node: GrammarNode?) {
                guard let node, seen.insert(ObjectIdentifier(node)).inserted else { return }
                for symbol in node.bodySymbols where nonTerminals[symbol.name] != nil {
                    queue.append(symbol.name)
                }
                if node.kind != .END { collect(node.seq) }
                if !node.isRHS { collect(node.alt) }
            }
            for instance in instances(of: name) { collect(instance) }
        }
        return parsed
    }

    /// Flag `@canParse(N)` / `@cannotParse(N)` whose target is not defined.
    ///
    /// A target need not be reachable: one that no reachable production body names is answered by
    /// a speculative recogniser (`MessageParser.canDerive`), so it is never blind. An undefined name
    /// is still a specification error.
    ///
    /// Returns one message per bad site (empty = clean) as well as logging, so tests can assert on
    /// the result instead of scraping OSLog.
    @discardableResult
    func diagnosePredicateTargets() -> [String] {
        var findings: [String] = []
        var seen = Set<ObjectIdentifier>()
        func walk(_ node: GrammarNode?, owner: String) {
            guard let node, seen.insert(ObjectIdentifier(node)).inserted else { return }
            for predicate in node.forwardPredicates
            where nonTerminals[predicate.targetName] == nil && terminals[predicate.targetName] == nil {
                findings.append("undefined predicate target '\(predicate.targetName)' used by '\(owner)'")
            }
            if node.kind != .END { walk(node.seq, owner: owner) }
            // Every production is a root below; an RHS reference (`.alt` → its LHS) is not followed.
            if !node.isRHS { walk(node.alt, owner: owner) }
        }
        for (name, nt) in nonTerminals { walk(nt, owner: name) }
        for finding in findings {
            Logger.grammar.error("\(finding, privacy: .public)")
        }
        return findings
    }


    /// Flag a preference that can remove every parse: an alternative that outranks a sibling
    /// (`@prefer` over an unmarked or avoided sibling, or unmarked over an `@avoid`) and lies
    /// on a cycle that reads no input. In `A = @prefer A | "a"` every tree of `A` ends in the
    /// `"a"` alternative, and there `A → A` covers the same tokens and outranks it, so no
    /// tree is left (Bend/SPEC.bend, preferences). A cycle through an alternative that
    /// outranks nothing is harmless: `A = @prefer "a" | A`.
    ///
    /// An alternative reaches a nonterminal over its own span when the nonterminal (or a
    /// bracket holding it) can be the whole of the alternative: every other item can read
    /// nothing. A bracket's alternative is checked against the nonterminal that holds the
    /// bracket, which may report a cycle the bracket cannot actually close.
    ///
    /// Grammar loading refuses a grammar with findings (`ApusParserError.preferenceCycle`).
    /// Returns one message per bad alternative (empty = clean) as well as logging.
    @discardableResult
    func diagnosePreferenceCycles() -> [String] {
        // Which nonterminals can read nothing, as a fixpoint. (A node's `isNullable` reads its
        // positional FIRST set, which looks through to what follows, so it can't say this.)
        var nullable = Set<ObjectIdentifier>()
        func readsNothing(_ s: GrammarNode) -> Bool {
            switch s.kind {
            case .EPS, .B, .OPT, .KLN: return true
            case .N: return s.alt.map { nullable.contains(ObjectIdentifier($0)) } ?? false
            case .DO, .POS: return someAlternativeReadsNothing(s.alt)
            default: return false
            }
        }
        func someAlternativeReadsNothing(_ head: GrammarNode?) -> Bool {
            var scan = head
            while let a = scan {
                if a.bodySymbols.allSatisfy(readsNothing) { return true }
                scan = a.alt
            }
            return false
        }
        var grew = true
        while grew {
            grew = false
            for lhs in allProductions where !nullable.contains(ObjectIdentifier(lhs)) && someAlternativeReadsNothing(lhs.alt) {
                nullable.insert(ObjectIdentifier(lhs))
                grew = true
            }
        }

        // The nonterminals (LHS nodes) an alternative body can be entirely, over its own span.
        func sameSpanTargets(_ body: [GrammarNode], into targets: inout [GrammarNode], seen: inout Set<ObjectIdentifier>) {
            for (k, s) in body.enumerated()
            where body.indices.allSatisfy({ $0 == k || readsNothing(body[$0]) }) {
                if s.kind == .N, let lhs = s.alt {
                    targets.append(lhs)
                } else if s.kind.isBracket, seen.insert(ObjectIdentifier(s)).inserted {
                    var scan = s.alt
                    while let a = scan { sameSpanTargets(a.bodySymbols, into: &targets, seen: &seen); scan = a.alt }
                }
            }
        }
        func targets(ofBody body: [GrammarNode]) -> [GrammarNode] {
            var out: [GrammarNode] = []
            var seen = Set<ObjectIdentifier>()
            sameSpanTargets(body, into: &out, seen: &seen)
            return out
        }

        // Edges LHS → LHS over the same span, and whether `goal` is reachable from `start`.
        var edges: [ObjectIdentifier: [GrammarNode]] = [:]
        func edgesOf(_ lhs: GrammarNode) -> [GrammarNode] {
            if let known = edges[ObjectIdentifier(lhs)] { return known }
            var out: [GrammarNode] = []
            var scan = lhs.alt
            while let a = scan { out += targets(ofBody: a.bodySymbols); scan = a.alt }
            edges[ObjectIdentifier(lhs)] = out
            return out
        }
        func reaches(_ from: [GrammarNode], _ goal: GrammarNode) -> Bool {
            var stack = from
            var visited = Set<ObjectIdentifier>()
            while let n = stack.popLast() {
                if n === goal { return true }
                guard visited.insert(ObjectIdentifier(n)).inserted else { continue }
                stack += edgesOf(n)
            }
            return false
        }

        func rank(_ a: GrammarNode) -> Int { a.isPreferred ? 2 : (a.isAvoided ? 0 : 1) }

        var findings: [String] = []
        // One choice point: the alternative chain from `head`, held by nonterminal `owner`.
        func check(chain head: GrammarNode?, owner: GrammarNode) {
            var alts: [GrammarNode] = []
            var scan = head
            while let a = scan { alts.append(a); scan = a.alt }
            guard let lowest = alts.map(rank).min() else { return }
            for (n, a) in alts.enumerated() where rank(a) > lowest {
                if reaches(targets(ofBody: a.bodySymbols), owner) {
                    findings.append("'\(owner.name)': alternative \(n + 1) outranks a sibling and can derive '\(owner.name)' again without reading input, so the preference can remove every parse")
                }
            }
        }
        var seenBrackets = Set<ObjectIdentifier>()
        func walkBrackets(_ node: GrammarNode?, owner: GrammarNode) {
            guard let node, seenBrackets.insert(ObjectIdentifier(node)).inserted else { return }
            if node.kind.isBracket { check(chain: node.alt, owner: owner) }
            if node.kind != .END { walkBrackets(node.seq, owner: owner) }
            if !node.isRHS { walkBrackets(node.alt, owner: owner) }
        }
        for lhs in allProductions {
            check(chain: lhs.alt, owner: lhs)
            walkBrackets(lhs.alt, owner: lhs)
        }
        for finding in findings {
            Logger.grammar.error("\(finding, privacy: .public)")
        }
        return findings
    }

}
