//
//  Prediction.swift
//  tinyGLL
//
//  FIRST and FOLLOW, and the one-character test GLL makes with them.
//

import Foundation

// At a slot X ::= α·β the parse can go on with next character t only if
//
//     t ∈ FIRST(β)   or   β can read nothing and t ∈ FOLLOW(X)
//
// The parser asks this before every step that may fail: choosing an alternate, calling,
// skipping a bracket, going on after a return. Leaving out a step that fails the test removes
// only dead wood: the derivations stay the same.
//
// The tables are the smallest sets closed under these rules ('$' is the end of the input):
//
//     X ::= α,  α can read nothing        ⟹  X is nullable
//     X ::= α                             ⟹  FIRST(α) ⊆ FIRST(X)
//     S is the start symbol               ⟹  $ ∈ FOLLOW(S)
//     X ::= α Y β                         ⟹  FIRST(β) ⊆ FOLLOW(Y)
//     X ::= α Y β,  β can read nothing    ⟹  FOLLOW(X) ⊆ FOLLOW(Y)
//
// A bracket is a Y whose definition is its body; [ ] and { } can always read nothing, and in
// a loop a round can follow a round: FIRST(body) ⊆ FOLLOW(body). The rules are applied until
// nothing changes. (The same rules in Bend: Bend/core/TABLES.bend.)

nonisolated let endOfInput: Character = "$"

nonisolated struct Prediction {
    private(set) var nullable: Set<GrammarNode> = []
    private(set) var first: [GrammarNode: Set<Character>] = [:]
    private(set) var follow: [GrammarNode: Set<Character>] = [:]

    init(definitions: [GrammarNode], start: GrammarNode) {
        follow[start] = [endOfInput]
        var changed = true
        func add(_ characters: Set<Character>, to table: inout [GrammarNode: Set<Character>], at X: GrammarNode) {
            if !characters.isSubset(of: table[X, default: []]) {
                table[X, default: []].formUnion(characters)
                changed = true
            }
        }
        while changed {
            changed = false
            for X in definitions {
                var alternate = X.alt
                while let a = alternate {
                    let whole = firstOf(a.seq)
                    add(whole.characters, to: &first, at: X)
                    if whole.nullable && nullable.insert(X).inserted { changed = true }

                    var node = a.seq
                    while let Y = node, Y.kind != .END {
                        if let body = Y.alt, Y.kind == .N || Y.kind.isBracket {
                            let after = firstOf(Y.seq)
                            add(after.characters, to: &follow, at: body)
                            if after.nullable { add(follow[X, default: []], to: &follow, at: body) }
                            if Y.kind.isLoop { add(first[body, default: []], to: &follow, at: body) }
                        }
                        node = Y.seq
                    }
                    alternate = a.alt
                }
            }
        }
    }

    /// Can the parse go on at `slot` with `next`? (The test above.)
    func predicts(_ slot: GrammarNode, _ next: Character) -> Bool {
        let rest = firstOf(slot)
        return rest.characters.contains(next) || rest.nullable && follow[owner(of: slot), default: []].contains(next)
    }

    /// Can the rest of the alternate from `slot` begin with `next`? For callers that need something.
    func begins(_ slot: GrammarNode, with next: Character) -> Bool {
        firstOf(slot).characters.contains(next)
    }

    /// Can a bracket's body begin with `next`?
    func begins(body: GrammarNode, with next: Character) -> Bool {
        first[body, default: []].contains(next)
    }

    /// FIRST of the rest of an alternate, from `slot` to its END, and whether it can read nothing.
    private func firstOf(_ slot: GrammarNode?) -> (characters: Set<Character>, nullable: Bool) {
        var characters: Set<Character> = []
        var node = slot
        while let symbol = node, symbol.kind != .END {
            switch symbol.kind {
            case .T:
                return (characters.union([symbol.name]), false)
            case .N, .DO, .OPT, .KLN, .POS:
                guard let body = symbol.alt else { return (characters, false) }
                characters.formUnion(first[body, default: []])
                let skippable = symbol.kind == .OPT || symbol.kind == .KLN
                if !skippable && !nullable.contains(body) { return (characters, false) }
            case .EPS, .ALT, .END:
                break
            }
            node = symbol.seq
        }
        return (characters, true)
    }

    /// The definition an alternate belongs to: its END links back to it.
    private func owner(of slot: GrammarNode) -> GrammarNode {
        var node = slot
        while node.kind != .END { node = node.seq! }
        return node.seq!
    }
}
