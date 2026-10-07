//
//  ModeSpecialization.swift
//  ApusApus
//
//  Parser modes compiled into the grammar. See `documentation/Parser Modes Specialization.md`.
//

import OSLog

// A parser mode is a finite inherited attribute: `@setMode`/`@clearMode` fix a child
// occurrence's mode as `(m | add) & ~remove`, and `@requiresMode`/`@rejectsMode` are fixed tests
// on that mode. Modes are SCOPED: `@carries(m)` on a production declares that `m` passes into it;
// entering any other nonterminal drops `m` (a swift-syntax parameter that is not forwarded). A CFG
// with finitely many inherited attribute values is a plain CFG over indexed nonterminals `X⟨m⟩`,
// so instead of carrying `m` in every descriptor, CRF key and BSR yield, this pass builds that
// CFG once at grammar load:
//
//   0. validation: every mode is declared by some `@carries`, set into a production that carries
//      it, and tested only where it can be present;
//   1. relevance: `rel(X)` = the carried mode bits that can change the language of `X`;
//   2. expansion: every original production is its own `X⟨0⟩` instance; an occurrence reached
//      under a mode that projects onto a non-empty subset of `rel(Y)` links to a copy `Y⟨m⟩`
//      (memoized, so recursion closes into a cycle between copies);
//   3. pruning: occurrences whose mode test fails statically are dead, and so is every
//      alternate containing one (to a fixpoint, since a copy can lose all its alternates).
//
// The parser then sees an ordinary grammar: a slot's identity already says which mode it is in.
// Grammars without modes, and every nonterminal outside all scopes, are left untouched.
//
// Runs right after the grammar text is parsed, while every production is still a TREE
// (END links and RHS `.alt` bindings are not resolved yet), so copying is a tree clone.

extension Grammar {

    private struct InstanceKey: Hashable {
        let name: String
        let mode: UInt64
    }

    /// The bits an occurrence's tests use.
    private static func tests(_ node: GrammarNode) -> UInt64 {
        node.requiredModes | node.rejectedModes
    }

    /// The mode an occurrence is entered with, given the mode of its context. Its tests are
    /// evaluated on this mode.
    private static func childMode(_ node: GrammarNode, from mode: UInt64) -> UInt64 {
        (mode | node.modeAdd) & ~node.modeRemove
    }

    /// Whether an occurrence's `@requiresMode`/`@rejectsMode` tests hold under `mode` (its child mode).
    private static func allows(_ node: GrammarNode, in mode: UInt64) -> Bool {
        if node.requiredModes != 0, (mode & node.requiredModes) != node.requiredModes { return false }
        if node.rejectedModes != 0, (mode & node.rejectedModes) == node.rejectedModes { return false }
        return true
    }

    /// Visit the body elements of each alternate owned by `owner` (an LHS or a bracket).
    /// Pre-resolution shape: `owner.alt` → ALT chain via `.alt`; `ALT.seq` → elements → END.
    private static func forEachElement(of owner: GrammarNode, _ visit: (GrammarNode) -> Void) {
        var alternate = owner.alt
        while let alt = alternate {
            var element = alt.seq
            while let e = element, e.kind != .END {
                visit(e)
                element = e.seq
            }
            alternate = alt.alt
        }
    }

    /// The bits of `name`'s scope (`@carries`); 0 for undefined names.
    private func carried(_ name: String) -> UInt64 {
        nonTerminals[name]?.carriedModes ?? 0
    }

    private func modeNames(_ bits: UInt64) -> String {
        modeNameToBit.filter { bits & $0.value != 0 }.keys.sorted().joined(separator: " ")
    }

    /// Load-time checks of the mode declarations. Errors make the annotations meaningless (a mode
    /// that can never be present where it is tested); warnings flag annotations with no effect.
    private func validateParserModes(_ originals: [GrammarNode]) throws {
        var problems: [String] = []
        var declared: UInt64 = 0
        var setSomewhere: UInt64 = 0
        for lhs in originals { declared |= lhs.carriedModes }

        // `possible`: the bits that can be present at this point of `owner`'s body.
        func check(_ owner: GrammarNode, in production: GrammarNode, possible: UInt64) {
            Self.forEachElement(of: owner) { e in
                let used = e.modeAdd | e.modeRemove | Self.tests(e)
                if used & ~declared != 0 {
                    problems.append("mode '\(modeNames(used & ~declared))' is used in '\(production.name)' but no production @carries it")
                }
                setSomewhere |= e.modeAdd
                let child = (possible | e.modeAdd) & ~e.modeRemove
                if Self.tests(e) & ~child & declared != 0 {
                    problems.append("'\(production.name)' tests mode '\(modeNames(Self.tests(e) & ~child))', which can never be present there; add it to '\(production.name)'s @carries or remove the test")
                }
                if e.kind == .N, nonTerminals[e.name] != nil {
                    let target = carried(e.name)
                    if e.modeAdd & ~target != 0 {
                        problems.append("'\(production.name)' sets mode '\(modeNames(e.modeAdd & ~target))' on '\(e.name)', which does not @carries it")
                    }
                    if e.modeRemove != 0, Self.tests(e) == 0, e.modeRemove & possible & target == 0 {
                        report("'\(production.name)' clears '\(modeNames(e.modeRemove))' on '\(e.name)', but that mode can never reach it there; the @clearMode has no effect")
                    }
                } else if e.kind.isBracket {
                    check(e, in: production, possible: child)
                }
            }
        }
        for lhs in originals { check(lhs, in: lhs, possible: lhs.carriedModes) }

        for (name, bit) in modeNameToBit where declared & bit != 0 && setSomewhere & bit == 0 {
            report("mode '\(name)' is carried but never set; it has no effect")
        }
        if !problems.isEmpty {
            for problem in problems { Logger.grammar.error("parser modes: \(problem, privacy: .public)") }
            throw ApusParserError.unexpectedToken(explanation: "parser modes: " + problems.joined(separator: "; "))
        }
    }

    /// Compile parser modes into the grammar graph. No-op for grammars without modes.
    func specializeParserModes() throws {
        guard !modeNameToBit.isEmpty else { return }
        let originals = nonTerminals.keys.sorted().map { nonTerminals[$0]! }
        try validateParserModes(originals)

        /// The mode a nonterminal occurrence passes to its callee: the child mode, restricted to
        /// the callee's scope. Tests on the occurrence see the unrestricted child mode, i.e. the
        /// caller's context.
        func calleeMode(_ e: GrammarNode, from mode: UInt64) -> UInt64 {
            Self.childMode(e, from: mode) & carried(e.name)
        }

        // 1. Relevance — least fixpoint, `scoped` restricted to each callee's `@carries`. A bit an
        //    occurrence sets or clears is fixed for that child, so it never makes the context
        //    depend on it. The unscoped variant only feeds the scope-exit lint below.
        func relevance(scoped: Bool) -> [String: UInt64] {
            var rel: [String: UInt64] = [:]
            func ownerRelevance(_ owner: GrammarNode) -> UInt64 {
                var bits: UInt64 = 0
                Self.forEachElement(of: owner) { e in
                    var inner = Self.tests(e)
                    if e.kind == .N { inner |= (rel[e.name] ?? 0) & (scoped ? carried(e.name) : ~0) }
                    if e.kind.isBracket { inner |= ownerRelevance(e) }
                    bits |= inner & ~(e.modeAdd | e.modeRemove)
                }
                return bits
            }
            var changed = true
            while changed {
                changed = false
                for lhs in originals {
                    let bits = ownerRelevance(lhs) & (scoped ? lhs.carriedModes : ~0)
                    if bits != rel[lhs.name] ?? 0 {
                        rel[lhs.name] = bits
                        changed = true
                    }
                }
            }
            return rel
        }
        let rel = relevance(scoped: true)

        // Scope exits that may matter: a carried bit dropped on entering a nonterminal that could
        // still reach a test of it. Expected at intended boundaries; anything else is a scope
        // that is too small. Informational.
        let reach = relevance(scoped: false)
        for (modeName, bit) in modeNameToBit.sorted(by: { $0.value < $1.value }) {
            var exits = Set<String>()
            func collectExits(_ owner: GrammarNode, from production: GrammarNode) {
                Self.forEachElement(of: owner) { e in
                    if e.kind == .N, production.carriedModes & bit != 0, e.modeRemove & bit == 0,
                       carried(e.name) & bit == 0, (reach[e.name] ?? 0) & bit != 0 {
                        exits.insert("\(production.name)→\(e.name)")
                    } else if e.kind.isBracket {
                        collectExits(e, from: production)
                    }
                }
            }
            for lhs in originals { collectExits(lhs, from: lhs) }
            if !exits.isEmpty {
                report("mode '\(modeName)' drops at \(exits.count) scope exits: \(exits.sorted().joined(separator: " "))")
            }
        }

        // 2. Expansion. Copies are cloned from the pristine originals: binding only rewrites RHS
        //    `.alt` pointers (which every copy rebinds) and dead marks live in a side table, so the
        //    originals' tree structure is unchanged until pruning.
        var table: [InstanceKey: GrammarNode] = [:]
        var worklist: [(owner: GrammarNode, mode: UInt64)] = originals.map { ($0, 0) }
        var dead = Set<ObjectIdentifier>()

        func instance(_ name: String, _ mode: UInt64) -> GrammarNode? {
            guard let template = nonTerminals[name] else { return nil }
            let projected = mode & (rel[name] ?? 0)
            if projected == 0 { return template }
            let key = InstanceKey(name: name, mode: projected)
            if let existing = table[key] { return existing }
            let copy = template.copySubtree()
            copy.origin = template
            copy.instanceMode = projected
            table[key] = copy
            specializations.append(copy)
            specializationsByName[name, default: []].append(copy)
            worklist.append((copy, projected))
            return copy
        }

        func bind(_ owner: GrammarNode, _ mode: UInt64) {
            Self.forEachElement(of: owner) { e in
                let child = Self.childMode(e, from: mode)
                guard Self.allows(e, in: child) else {
                    dead.insert(ObjectIdentifier(e))
                    return
                }
                if e.kind == .N {
                    // Undefined names stay unbound; `handleNonTerminal` reports them.
                    e.alt = instance(e.name, calleeMode(e, from: mode))
                } else if e.kind.isBracket {
                    bind(e, child)
                }
            }
        }

        while let item = worklist.popLast() {
            bind(item.owner, item.mode)
        }

        // 3. Pruning — to a fixpoint, because a copy can lose every alternate, which makes every
        //    occurrence bound to it dead in turn.
        func isEmptyProduction(_ node: GrammarNode?) -> Bool {
            guard let node, node.kind == .N, !node.isRHS else { return false }
            return node.alt == nil
        }

        /// Remove dead alternates from `owner`'s chain. Returns true when anything changed.
        func prune(_ owner: GrammarNode) -> Bool {
            var changedHere = false
            var previous: GrammarNode? = nil
            var alternate = owner.alt
            while let alt = alternate {
                var alive = true
                var before: GrammarNode = alt
                var element = alt.seq
                while let e = element, e.kind != .END {
                    if e.kind.isBracket, prune(e) { changedHere = true }
                    if dead.contains(ObjectIdentifier(e))
                        || (e.kind == .N && isEmptyProduction(e.alt))
                        || ((e.kind == .DO || e.kind == .POS) && e.alt == nil) {
                        alive = false
                        break
                    }
                    if (e.kind == .OPT || e.kind == .KLN) && e.alt == nil {
                        // Every body alternate is dead: the group can only match ε. Unlink it.
                        before.seq = e.seq
                        changedHere = true
                    } else {
                        before = e
                    }
                    element = e.seq
                }
                if alive, let first = alt.seq, first.kind == .END {
                    // Unlinking left the alternate with no symbols: keep it as an explicit ε.
                    let epsilon = GrammarNode(kind: .EPS, name: "ε")
                    epsilon.seq = first
                    alt.seq = epsilon
                }
                if alive {
                    previous = alt
                } else {
                    if let previous { previous.alt = alt.alt } else { owner.alt = alt.alt }
                    changedHere = true
                }
                alternate = alt.alt
            }
            return changedHere
        }

        let productions = originals + specializations
        var changed = true
        while changed {
            changed = false
            for lhs in productions where prune(lhs) { changed = true }
        }

        for lhs in productions where lhs.alt == nil {
            Logger.grammar.error("parser modes: '\(Self.instanceName(lhs, modes: self.modeNameToBit), privacy: .public)' has no alternate left under its mode")
        }

        // Diagnostics: how many copies each mode costs.
        for (modeName, bit) in modeNameToBit.sorted(by: { $0.value < $1.value }) {
            let copies = specializations.filter { $0.instanceMode & bit != 0 }.count
            report("mode '\(modeName)': \(copies) specialized copies")
        }
        report("\(specializations.count) specialized copies of \(originals.count) productions")
    }

    /// Record a parser-mode notice in `parserModeReport` and the grammar log.
    private func report(_ notice: String) {
        parserModeReport.append(notice)
        Logger.grammar.info("parser modes: \(notice, privacy: .public)")
    }

    /// `name⟨mode1 mode2⟩` for a specialized copy, plain `name` otherwise. Diagnostics only.
    static func instanceName(_ node: GrammarNode, modes: [String: UInt64]) -> String {
        guard node.instanceMode != 0 else { return node.name }
        let names = modes.filter { node.instanceMode & $0.value != 0 }.keys.sorted()
        return "\(node.name)⟨\(names.joined(separator: " "))⟩"
    }

    /// Every production: the originals plus their specialized copies.
    var allProductions: [GrammarNode] {
        Array(nonTerminals.values) + specializations
    }

    /// Every instance of the nonterminal `name`: the original first, then its copies.
    /// Use this wherever a nonterminal is looked up BY NAME to query its BSR yields.
    func instances(of name: String) -> [GrammarNode] {
        guard let original = nonTerminals[name] else { return [] }
        return [original] + (specializationsByName[name] ?? [])
    }
}
