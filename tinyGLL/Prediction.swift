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
// The parser asks this — viable(), as in ApusApus — before every step that may fail: choosing an
// alternate, entering, skipping a bracket, going on after a return. FOLLOW is global, so a step
// may pass that dies later, but no step that would succeed is stopped: leaving out a step that
// fails the test removes only dead wood. A caller that needs something asks FIRST alone.
//
// As in ApusApus, FIRST is kept per slot: node.first is FIRST of the rest of the alternate from
// that node on, with ε in it when the rest can read nothing. It is built right to left:
//
//     at END                       { ε }
//     at a terminal t              { t }
//     at ε                         FIRST after it
//     at a nonterminal or bracket  FIRST of its definition without ε, plus FIRST after it when
//                                  the definition can read nothing ([ ] and { } always can)
//
// A definition's FIRST is the union of its alternates' first slots, and FOLLOW of a definition Y
// collects, at every occurrence of Y:
//
//     FIRST after Y without ε, plus FOLLOW of the owner when the rest after Y can read nothing,
//     plus, for { } and < >, FIRST of Y's body (a round can follow a round)
//
// with $ ∈ FOLLOW(S). These are the smallest sets closed under the rules, found by applying
// them until nothing changes. (The same rules in Bend: Bend/core/TABLES.bend.)

/// What the parser finds at the end of the input.
nonisolated let endOfInput: Character = "$"

/// The mark in a FIRST set for "can read nothing".
nonisolated let epsilon: Character = "ε"

nonisolated extension Parser {

    func computeFirstAndFollow(start: GrammarNode) {
        start.follow = [endOfInput]
        var changed = true
        while changed {
            changed = false
            for X in allDefinitions {
                var alternate = X.alt
                while let a = alternate {
                    if updateFirst(from: a.seq!) { changed = true }
                    if !a.seq!.first.isSubset(of: X.first) {
                        X.first.formUnion(a.seq!.first)
                        changed = true
                    }
                    if updateFollow(in: a, of: X) { changed = true }
                    alternate = a.alt
                }
            }
        }
    }

    /// May the parse go on at `slot` with the character at `j`? A caller that needs something
    /// passes `mayBeEmpty: false`: then only FIRST counts.
    func viable(_ slot: GrammarNode, at j: Int, mayBeEmpty: Bool = true) -> Bool {
        let next = character(at: j)
        if slot.first.contains(next) { return true }
        return mayBeEmpty && slot.first.contains(epsilon) && slot.owner!.follow.contains(next)
    }

    // FIRST of every slot from `node` to the END of its alternate, right to left. True if one grew.
    private func updateFirst(from node: GrammarNode) -> Bool {
        if node.kind == .END {
            node.first = [epsilon]
            return false
        }
        let grewAfter = updateFirst(from: node.seq!)
        let after = node.seq!.first
        var first: Set<Character>
        switch node.kind {
        case .T:
            first = [node.name]
        case .N, .DO, .OPT, .KLN, .POS:
            let body = node.alt?.first ?? []
            first = body.subtracting([epsilon])
            if body.contains(epsilon) || node.kind == .OPT || node.kind == .KLN { first.formUnion(after) }
        default:
            first = after
        }
        let grew = first != node.first
        node.first = first
        return grew || grewAfter
    }

    // FOLLOW of every nonterminal and bracket in alternate `a` of X. True if one grew.
    private func updateFollow(in a: GrammarNode, of X: GrammarNode) -> Bool {
        var grew = false
        var node = a.seq!
        while node.kind != .END {
            if let Y = node.alt, node.kind == .N || node.kind.isBracket {
                let after = node.seq!.first
                var follow = Y.follow.union(after.subtracting([epsilon]))
                if after.contains(epsilon) { follow.formUnion(X.follow) }
                if node.kind.isLoop { follow.formUnion(Y.first.subtracting([epsilon])) }
                if follow != Y.follow { Y.follow = follow; grew = true }
            }
            node = node.seq!
        }
        return grew
    }
}
