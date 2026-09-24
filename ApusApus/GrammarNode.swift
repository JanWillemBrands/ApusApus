//
//  GrammarNode.swift
//  ApusApus
//
//  Created by Johannes Brands on 20/05/2024.
//

/*
 EOS    end of string ("$")
 T      terminal (singleton, case sensitive)
 TI     terminal (singleton, case insensitive)
 C      terminal character
 B      terminal builtin (whitespace, comment, etc)
 EPS    empty string ("ε" or "")
 N      nonterminal
 ALT    start of alternate
 END    end of alternate
 DO     group ()
 OPT    optional []
 POS    one or more <>
 KLN    zero or more (Kleene) {}
 
 END.seq references the start of production 'N' or closest 'DO', 'OPT', 'POS', or 'KLN' bracket
 END.alt references its alternate start 'ALT'
 */

import OSLog
import Foundation
import BitCollections

enum GrammarNodeError: Error {
    case undefinedNonTerminal(name: String, definedAsTerminal: Bool)
}

enum GrammarNodeKind { case EOS, T, TI, C, B, EPS, N, ALT, END, DO, OPT, POS, KLN }

enum Disambiguation: String { case shortest, longest, left, right }

/// One leading `@cannotParse(N)` / `@canParse(N)` predicate on an alternate, `N` a NONTERMINAL.
/// See `GrammarNode.forwardPredicates`.
struct ForwardPredicate {
    let targetName: String
    let negated: Bool
}

/// Structured predicate for `.B` boundary nodes. Layout boundaries still use `name`
/// directly; token lookaround uses this payload plus `boundaryPredicateBS` after
/// grammar symbol resolution.
enum BoundaryPredicate {
    case tokenLookahead(positive: Bool, kinds: Set<String>)
    case tokenLookbehind(positive: Bool, kinds: Set<String>, distance: Int)
}

/// Per-grammar-build scratch state, created fresh for each grammar load and
/// threaded through `resolveGrammarNodeLinks`. Each load owns its own instance,
/// so numbering is isolated by construction — no shared static to race on under
/// concurrent loads, and node numbers stay compact per grammar ([0, nodeCounter)).
final class GrammarBuild {  // TODO: why is this a final class and not a struct?
    var nodeCounter = 0
}

extension GrammarNodeKind {
    var isTerminal: Bool { self == .T || self == .TI || self == .C || self == .B }
    var isBracket:  Bool { self == .DO || self == .OPT || self == .KLN || self == .POS }
    var isLeaf:     Bool { isTerminal || self == .EPS }
    var isClosure:  Bool { self == .KLN || self == .POS }
}

final class GrammarNode {

    /// this is to give GrammarNodes access to their grammar
    static weak var grammar: Grammar?
    
    /// a unique number identifying each node, used in BSR yield
    var number = 0
    
    /// Integer ID from `Grammar.symbolToID`, set by `assignNameIDs()`.
    /// Only meaningful for terminal-like nodes (.T, .TI, .C, .B, .EOS, .EPS);
    /// nonterminals keep the default -1. Used by `tokenMatch()` for O(1) integer comparison.
    var nameID: Int!
    
    let kind: GrammarNodeKind
    let name: String

    /// True for LHS non-terminals declared with `:` — their parse result is
    /// consumed as trivia rather than emitted to the outer BSR. Recognised at
    /// trivia-skip time via a recursive `MessageParser` sub-instance.
    var isTrivia: Bool = false
    
    var alt, seq: GrammarNode?
//    var alt: GrammarNode? {
//        didSet {
//            // alt is overloaded:
//            // - ALT/END nodes: alt points to an .ALT node
//            // - RHS nonterminals (N with seq): alt points to the LHS .N definition
//            if let alt {
//                switch kind {
//                case .N where seq != nil:
//                    assert(alt.kind == .N, "RHS nonterminal alt should point to its LHS .N definition, got \(alt.kind)")
//                default:
//                    assert(alt.kind == .ALT, "alt should always point to a .ALT node, got \(alt.kind)")
//                }
//            }
//        }
//    }
//    var seq: GrammarNode? {
//        didSet {
//            assert(seq?.kind != .ALT, "seq should never point to a .ALT node")
//        }
//    }
    init(kind: GrammarNodeKind, name: String, alt: GrammarNode? = nil, seq: GrammarNode? = nil) {
        self.kind = kind
        self.name = name
        self.alt = alt
        self.seq = seq
    }

    var actions: [String] = []  // stores semantic actions
    var signature: String?      // function signature text (params, throws, return) for .N nodes
    var locals: [String] = []   // local declarations for generated function  TODO: can this be removed ???
    
    /// first is a positional prediction set: the tokens that can appear at this
    /// position in the sequence, including look-through of nullable elements.
    /// During FIRST/FOLLOW propagation (Grammar.handleBracket), ε is removed
    /// from OPT/KLN and replaced by the continuation's FIRST (concatenation rule).
    /// This means first does NOT contain ε for OPT/KLN, even though they are
    /// intrinsically nullable. Use isNullable for nullability checks instead.
    var first:      Set<String> = []
    var follow:     Set<String> = []
    var ambiguous:  Set<String> = []

    /// Exclusion set for Schrödinger dual suppression.
    /// When an excluded terminal matches the same end as a candidate, the
    /// parser suppresses that candidate.
    /// Populated by `---("if" "let" ...)` annotations in APUS grammar rules.
    var exclude:    Set<String> = []

    /// BitSet mirrors of first/follow/etc, populated by `Grammar.populateBitSets()`.
    /// Used by `testSelect()` and the follow check on the hot path for O(1) membership tests.
    var firstBS:                BitSet = []
    var followBS:               BitSet = []
    var ambiguousBS:            BitSet = []
    var excludeBS:              BitSet = []

    /// Structured payload for `.B` sequence boundaries such as token lookaround.
    /// Layout boundaries (`<s>`, `>s<`, `<n>`, `>n<`) leave this nil and use `name`.
    var boundaryPredicate: BoundaryPredicate?
    var boundaryPredicateBS: BitSet = []

    /// Alternate-level `@prefer` annotation. Captured at parse time on the `.ALT`
    /// node heading the alternate (prefix, right after `=` or `|`). Resolved by the
    /// Oracle (`PreferRule`): among the alternates of one nonterminal that derive
    /// the same parent node (same `(i,j)` span), the preferred alternate(s) win and
    /// the non-preferred siblings' yields are pruned.
    var isPreferred: Bool = false

    /// Alternate-level `@avoid` annotation — the negative dual of `@prefer`, ALWAYS on the
    /// `.ALT` node heading an alternate (prefix, right after `=`, `|`, or an opening
    /// `(`/`[`/`{`/`<`). "Avoid this alternate": it loses to its rivals. Its rivals are
    ///   • its **explicit siblings** — pruned same-span wherever a sibling covers the same
    ///     `(i,j)` (`@avoid A` ≡ `@prefer` on A's siblings), via Oracle `registerPrefer`; and
    ///   • when the enclosing group is an **OPT/KLN**, that group's **implicit empty (skip)
    ///     branch** — the reading where the whole optional is dropped. ε has no last body
    ///     symbol to key a same-span rule on, so the Oracle compiles this rival as an
    ///     alternate-aware follower-pivot (`AvoidOptionalRule`) via `registerOptionalSkip`.
    /// `[ @avoid X ]` (single body alternate) is thus just the skip-rival case: "prefer the
    /// skip", expressed as an annotation on the body alternate — NOT a bracket property, and
    /// NOT `@shortest` (extent over-prunes and changes acceptance).
    var isAvoided: Bool = false

    /// Parse predicate on an alternate — a leading `@cannotParse(N)` / `@canParse(N)` whose
    /// operand `N` is a NONTERMINAL. Captured on the `.ALT` node heading the alternate.
    /// The Oracle prunes the alternate's reading at its start position `i` when `N` does
    /// derive (`@cannotParse`, negated) or does not derive (`@canParse`, positive) at `i` —
    /// a Way-1 BSR query.
    /// See `Grammar Predicate Lookahead Design.md`. (Postfix `>->`/`>+>` with a TERMINAL
    /// operand remains the parse-time token gate in `factor()`.)
    /// REPEATABLE, and they compose as a CONJUNCTION — every predicate must hold, exactly like the
    /// containment predicates below. One gate per alternate could not express "not a declaration AND
    /// not an attribute" (see `statement` in `Swift.apus`).
    var forwardPredicates: [ForwardPredicate] = []

    /// Containment predicate on an alternate — leading `@within(N)` (repeatable, conjunction).
    /// Captured on the `.ALT` node. The Oracle keeps the alternate's reading only where its
    /// span is CONTAINED in a yield of EACH named container `N` (BSR containment = the GLL
    /// substitute for an inherited context/flavor), pruning otherwise. The declarative
    /// replacement for the procedural `@within` filter. See `Grammar Predicate Lookahead Design.md`.
    /// `@confinedTo(N…)` — positive containment: keep this alternate only where its span is
    /// contained in a yield of EACH `N`. `@excludedFrom(N…)` — negative: prune where contained.
    /// Both stack (conjunction over the containers). See `Grammar Predicate Lookahead Design.md`.
    var confinedToContainers: [String] = []
    var excludedFromContainers: [String] = []

    /// `@sameLine` — this nonterminal's span may not cross a newline consumed as trivia.
    /// Newlines inside a committed token (nested multiline string, block comment) are permitted.
    var requiresSameLine: Bool = false

    /// Terminal occurrence belongs directly to a structured `:` / `-` recognizer body and should
    /// match at the exact parser cursor instead of skipping leading trivia first. Normal `=`
    /// payloads reached from that body keep the default trivia skip.
    var suppressesLeadingTrivia: Bool = false

    /// Structured `-` lexical-nonterminal. The LHS production is recognized by a GLL sub-parse at
    /// lex time and emitted as a SINGLE token (like structured `:` trivia, but a token not trivia). References
    /// to it in other productions resolve to a terminal (`.T`) — the outer parser never sees the
    /// body characters, so they can't be re-read (e.g. a regex body can't alias an operator
    /// sequence). Mirrors swift-syntax's lexer committing to one `/…/` token.
    var isLexicalToken: Bool = false

    static var sizeofSets = 0
    
    /// Whether this node is intrinsically nullable (can derive ε).
    /// Per Definition 6 of "GLL syntax analysers for EBNF grammars":
    /// FIRST([ψ]) = FIRST(ψ) ∪ {ε} and FIRST({ψ}) = FIRST(ψ) ∪ {ε}
    /// OPT and KLN are always nullable by definition.
    var isNullable: Bool {
        switch kind {
        case .OPT, .KLN: return true
        default: return first.contains("")
        }
    }
    
    // BSR yields moved to `MessageParser.yields`, indexed by `node.number`.
    // Keeps the grammar load-time-immutable and lets multiple parsers (or a
    // recursive sub-parse) share a grammar without state collisions.
    
    var disambiguation: Disambiguation? // TODO:  this seems not to be used
}

//extension GrammarNode {
//    func isExpecting(_ token: Token) -> Bool {
//        if first.contains(token.kind) {
//            return true
//        } else if first.contains("") && follow.contains(token.kind) {
//            return true
//        } else {
//            var expectedTokens = first
//            if first.contains("") {
//                expectedTokens.formUnion(follow)
//            }
//            trace("expected \"\(token.kind)\" to be in", expectedTokens)
//            return false
//        }
//    }
//}

extension GrammarNode {
    /// LHS nonterminal: defines a production rule (has .alt chain, no .seq)
    var isLHS: Bool { kind == .N && seq == nil }
    
    /// RHS nonterminal: reference inside a sequence (has .seq, .alt → LHS definition)
    var isRHS: Bool { kind == .N && seq != nil }
    
    /// Collect the symbols of an alternate's body: walk .seq chain until .END.
    /// Call on an ALT node.
    var bodySymbols: [GrammarNode] {
        var symbols: [GrammarNode] = []
        var s = seq
        while let n = s {
            if n.kind == .END { break }
            symbols.append(n)
            s = n.seq
        }
        return symbols
    }
    
    /// Find the END node inside a bracket's first alternate body.
    var bracketEndNode: GrammarNode? {
        guard kind.isBracket else { return nil }
        var node = alt?.seq
        while let n = node {
            if n.kind == .END { return n }
            node = n.seq
        }
        return nil
    }
}

extension GrammarNode: Hashable {
    static func == (lhs: GrammarNode, rhs: GrammarNode) -> Bool {
        lhs.number == rhs.number
    }
    func hash(into hasher: inout Hasher) {
        hasher.combine(number)
    }
}

extension GrammarNode: CustomStringConvertible {
    
    var description: String { number.description }

    var kindName: String {
        "." + String(describing: self.kind).prefix(3)
    }
}

extension GrammarNode {
    // sets the .seq and .alt links for END nodes
    func resolveGrammarNodeLinks(parent: GrammarNode?, alternate: GrammarNode?, build: GrammarBuild) {
        number = build.nodeCounter
        build.nodeCounter += 1
        switch kind {
        case .EOS, .T, .TI, .C, .B, .EPS:
            seq?.resolveGrammarNodeLinks(parent: parent, alternate: alternate, build: build)
        case .N:
            if isRHS {
                seq?.resolveGrammarNodeLinks(parent: parent, alternate: alternate, build: build)
            } else {
                alt?.resolveGrammarNodeLinks(parent: self, alternate: alternate, build: build)
            }
        case .ALT:
            seq?.resolveGrammarNodeLinks(parent: parent, alternate: self, build: build)
            alt?.resolveGrammarNodeLinks(parent: parent, alternate: alternate, build: build)
        case .DO, .POS, .OPT, .KLN:
            alt?.resolveGrammarNodeLinks(parent: self, alternate: alternate, build: build)
            seq?.resolveGrammarNodeLinks(parent: parent, alternate: alternate, build: build)
        case .END:
            seq = parent
            alt = alternate
        }
    }
}

extension GrammarNode {
    /// Label for a bracket node showing only its own content, not the continuation.
    /// e.g. `{ "a" }` instead of `{ "a" } { "a" }`.
    func bracketLabel() -> String {
        switch kind {
        case .DO:  return "(\((alt?.ebnf() ?? "").trimmingCharacters(in: .whitespaces)))"
        case .OPT: return "[\((alt?.ebnf() ?? "").trimmingCharacters(in: .whitespaces))]"
        case .POS: return "<\((alt?.ebnf() ?? "").trimmingCharacters(in: .whitespaces))>"
        case .KLN: return "{\((alt?.ebnf() ?? "").trimmingCharacters(in: .whitespaces))}"
        default:   return name
        }
    }
    
    // when called on a lhs nonterminal GrammarNode this generates its full EBNF grammar
    func ebnf() -> String {
        var s = ""
        switch kind {
        case .EOS, .EPS:
            s += name + " "
            if let seq { s += seq.ebnf() }
        case .T, .TI, .C, .B:
            s += "\"" + name + "\" "
            if let seq { s += seq.ebnf() }
        case .N:
            if let seq { // rhs
                s += name + " " + seq.ebnf()
            } else { // lhs
                if let alt {
                    s += name + " = " + alt.ebnf() + "."
                }
            }
        case .ALT:
            if let seq { s += seq.ebnf() }
            if let alt { s +=  "| " + alt.ebnf() }
        case .END:
            break
        case .DO:
            if let alt { s += "( " + alt.ebnf() + ") " }
            if let seq { s += seq.ebnf() }
        case .OPT:
            if let alt { s += "[ " + alt.ebnf() + "] " }
            if let seq { s += seq.ebnf() }
        case .POS:
            if let alt { s += "< " + alt.ebnf() + "> " }
            if let seq { s += seq.ebnf() }
        case .KLN:
            if let alt { s += "{ " + alt.ebnf() + "} " }
            if let seq { s += seq.ebnf() }
        }
        return s
    }
}


extension GrammarNode {
    // EBNF dotted-slot rendering (diagnostics only). This used to keep four
    // process-global statics as recursion scratch, which was a data race once
    // tests run in parallel. State is now threaded locally, so `emit`/`ebnfDot`
    // are pure and reentrant — safe to call from any thread.
    enum Exit: Error { case endOfToplevel }

    func emit(into ebnf: inout String, dottedSlot: GrammarNode) throws {
        let middleDot = "\u{00B7}"
        switch kind {
        case .EOS, .T, .TI, .C, .B, .EPS:
            ebnf += name
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
        case .N:
            if let seq { // rhs
                ebnf += name
                if self == dottedSlot { ebnf += middleDot }
                try seq.emit(into: &ebnf, dottedSlot: dottedSlot)
            } else { // lhs
                ebnf += name
            }
        case .ALT:
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
            if let alt {
                ebnf +=  "|"
                try alt.emit(into: &ebnf, dottedSlot: dottedSlot)
            }
        case .END:
            if self == dottedSlot { ebnf += middleDot }
            if seq?.kind == .N {
                // this is the end of the top level alternate
                throw Exit.endOfToplevel
            }
        case .DO:
            if let alt {
                ebnf += "("
                try alt.emit(into: &ebnf, dottedSlot: dottedSlot)
                ebnf += ")"
            }
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
        case .OPT:
            if let alt {
                ebnf += "["
                try alt.emit(into: &ebnf, dottedSlot: dottedSlot)
                ebnf += "]"
            }
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
        case .POS:
            if let alt {
                ebnf += "<"
                try alt.emit(into: &ebnf, dottedSlot: dottedSlot)
                ebnf += ">"
            }
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
        case .KLN:
            if let alt {
                ebnf += "{"
                try alt.emit(into: &ebnf, dottedSlot: dottedSlot)
                ebnf += "}"
            }
            if self == dottedSlot { ebnf += middleDot }
            if let seq { try seq.emit(into: &ebnf, dottedSlot: dottedSlot) }
        }
    }

    func toplevels() -> (GrammarNode?, GrammarNode?) {
        // returns the the highest level alternate and the containing nonterminal
        var node = self
        while node.seq != nil {
            if node.kind == .END && node.seq?.kind == .N {
                return (node.alt, node.seq)
            }
            else {
                node = node.seq!
            }
        }
        return (nil, nil)
    }
    
    // generates the dotted ebnf for the toplevel containing alternate of the containing nonterminal
    // the dot is placed after the dottedSlot node:
    //   terminal/nonterminal: dot after the symbol  e.g. S="a"·{"a"}
    //   bracket (KLN etc):    dot after closing }   e.g. S="a"{"a"}·
    //   ALT:                  dot at start of body  e.g. S="a"{·"a"}
    //   END:                  dot at end of body    e.g. S="a"{"a"·}
    func ebnfDot() -> String {
        if kind == .N && seq == nil {
            // a lhs nonterminal
            return name
        } else {
            // construct the ebnf for the toplevel alternate production containing the dot
            var ebnf = ""
            let (toplevelAlternate, containingNonterminal) = toplevels()
            if let tla = toplevelAlternate, let cnt = containingNonterminal {
                try? tla.emit(into: &ebnf, dottedSlot: self)
                return cnt.name + "=" + ebnf
            } else {
                return ebnf
            }
        }
    }
}
