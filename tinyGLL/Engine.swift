//
//  Engine.swift
//  tinyGLL
//
//  Created by Johannes Brands on 2026.08.28.
//

import Foundation

// tinyGLL parses 'input' according to 'syntax' in a CNP - Clustered Nonterminal Parsing style.

// "Derivation representation using binary subtree sets"
// https://pure.royalholloway.ac.uk/ws/portalfiles/portal/33174042/Accepted_Manuscript.pdf

// "A Reference GLL Implementation"
// https://pure.royalholloway.ac.uk/ws/portalfiles/portal/56267014/sle23RefGLL.pdf

// Naming, as in the papers. The same letter means different things in a descriptor
// and in a yield, so the two conventions are spelled out once here:
//   L        a grammar slot (a position in a production)
//   X        a nonterminal (its LHS definition node)
//   in a descriptor (L, k, i):     k = cluster index,  i = input index
//   in a BinarySpan (i, k, j):     i = left extent,    k = pivot,  j = right extent
// So a descriptor's 'k' becomes a span's 'i', which is why addYield is called
// as addYield(L: cL, i: cU, k: cI, ...) — the swap is deliberate, not a typo.

// Start symbol 'S'. Empty production 'ε'.
// Terminals/nonterminals are single lowercase/uppercase letters.
// Space and newline are skipped.

//T = a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s | t | u | v | w | x | y | z | ε .
//N = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z .
//
//S = P | P S .
//P = N E A D .
//A = Q | Q B A .
//Q = F | F Q .
//F = T | N .
//
//E = = .
//D = . .
//B = | .

nonisolated enum GrammarError: Error, CustomStringConvertible {
    case unexpectedCharacter(Character, at: Int)
    case unexpectedFactor(Character, at: Int)
    case missingStartSymbol

    var description: String {
        switch self {
        case .unexpectedCharacter(let c, let position):
            return "found an unexpected '\(c)' at position \(position)"
        case .unexpectedFactor(let c, let position):
            return "found an unexpected factor '\(c)' at position \(position)"
        case .missingStartSymbol:
            return "missing start symbol 'S'"
        }
    }
}

// 'GrammarNode' builds a binary tree with its 'seq' and 'alt' links.
// terminal, nonTerminal and epsilon nodes are stored as T, N, EPS.
// The ALT and END nodes signal the start and end of a sequence.
nonisolated enum GrammarNodeKind { case T, EPS, N, ALT, END }

nonisolated final class GrammarNode {
    let kind: GrammarNodeKind
    let name: Character

    var alt, seq: GrammarNode?

    let number: Int // unique number to identify the node

    init(_ kind: GrammarNodeKind, _ name: Character, number: Int) {
        self.kind = kind
        self.name = name
        self.number = number
    }
}

// Paper: descriptor = (L, k, i) — grammar slot, cluster index, input index
nonisolated struct Descriptor: Hashable {
    let L: GrammarNode          // grammar slot
    let k: Int                  // cluster index: where the containing nonterminal was entered
    let i: Int                  // input index: how far this attempt has got
}

// The (ambiguous) parse tree is stored as a set of binary spans a.k.a. Binary Subtree Representation, not in an SPPF.
nonisolated struct BinarySpan: Hashable {
    //   (i:k:k)   an epsilon yield          — pivot at the right extent
    //   (i:k:k+1) a terminal yield          — one character consumed
    //   (i:k:j)   a prefix + postfix yield  — prefix [i,k), postfix [k,j)
    //   (i:i:j)   a nonterminal yield       — pivot at the left extent
    let i:  Int
    let k: Int
    let j: Int
}

// Paper: crfNode (L, i) — a grammar slot paired with an input position.
// Used in two roles, and 'index' means something different in each:
//   as a cluster key   (slot: the LHS nonterminal, index: cI) — where the cluster starts
//   as a return edge   (slot: the RHS nonterminal, index: cU) — where the caller started
nonisolated struct ParsePosition: Hashable {
    let slot: GrammarNode
    let index: Int
}

// Paper: clusterNode (X, k). The (X, k) label is the crf dictionary key, so it is not
// repeated here — what a cluster adds over its identity is these two sets.
nonisolated final class ParseCluster {
    var returns: Set<ParsePosition> = []
    var pops: Set<Int> = []         // Paper: P — contingent returns
}

// MARK: - Parser

nonisolated final class Parser {

    var syntax: [Character]
    var input: [Character]

    // stores LHS nonTerminal definition grammar trees by name.
    var nonTerminalDefinitions: [Character: GrammarNode] = [:]

    /// Numbers handed out to GrammarNodes so far, and so also the size 'yields' needs.
    private(set) var nodeCount = 0

    var unique: Set<Descriptor> = []
    var remaining: [Descriptor] = []

    // The three parse registers, all set by getDescriptor().
    var cL: GrammarNode!            // current grammar slot (seeded by the first getDescriptor())
    var cU = 0                      // current cluster index: input position where the nonterminal was entered
    var cI = 0                      // current input index

    // Individual 'GrammarNode' yields are retrievable by GrammarNode.number index.
    var yields: [Set<BinarySpan>] = []

    // Paper: CRF - Call Return Forest
    var crf: [ParsePosition: ParseCluster] = [:]

    init(syntax: String, input: String) {
        self.syntax = Array(syntax)
        self.input = Array(input)
    }

    /// The only way a GrammarNode should be made: it is the numbering that keeps 'yields'
    /// indexable by `node.number`.
    private func makeNode(_ kind: GrammarNodeKind, _ name: Character) -> GrammarNode {
        defer { nodeCount += 1 }
        return GrammarNode(kind, name, number: nodeCount)
    }

    // MARK: Parse the grammar

    // Recursive descent parser to transform the 'syntax' string into a 'grammarNode' tree.
    func parseGrammar() throws {
        var i = 0
        var c: Character = "$"

        // 'c' is the current unconsumed character, 'i' is the index after 'c'.
        func next(expect predicate: (Character) -> Bool = { _ in true } ) throws {
            if !predicate(c) {
                throw GrammarError.unexpectedCharacter(c, at: i - 1)
            }
            while i < syntax.count && ( syntax[i] == " " || syntax[i] == "\n" ) {
                i += 1
            }
            if i < syntax.count {
                c = syntax[i]
                i += 1
            } else {
                c = "$"
            }
        }

        var nonTerminal: GrammarNode!                   // the current LHS production being parsed
        var nonTerminalReferences: [GrammarNode] = []   // RHS nonTerminal (forward/backward) references

        func production() throws {
            let name = c
            try next() { $0.isUppercase }
            nonTerminal = makeNode(.N, name)
            // store the LHS nonTerminal definition
            nonTerminalDefinitions[nonTerminal.name] = nonTerminal
            try next() { $0 == "=" }
            nonTerminal.alt = try alternates()
            try next() { $0 == "." }
        }

        func alternates() throws -> GrammarNode {
            let startOfAlternates = try sequence()
            var tmp = startOfAlternates
            while c == "|" {
                try next()
                let nextAlternate = try sequence()
                tmp.alt = nextAlternate
                tmp = nextAlternate
            }
            return startOfAlternates
        }

        func sequence() throws -> GrammarNode {
            let startOfSequence = makeNode(.ALT, "[")
            var tmp = startOfSequence
            repeat {
                let terminal: GrammarNode
                if c == "ε" {
                    terminal = makeNode(.EPS, c)
                } else if c.isUppercase {
                    terminal = makeNode(.N, c)
                    nonTerminalReferences.append(terminal)
                } else if c.isLowercase {
                    terminal = makeNode(.T, c)
                } else {
                    throw GrammarError.unexpectedFactor(c, at: i - 1)
                }
                tmp.seq = terminal
                tmp = terminal
                try next()
            } while c.isLetter

            let end = makeNode(.END, "]")
            tmp.seq = end
            end.seq = nonTerminal
            end.alt = startOfSequence
            return startOfSequence
        }

        try next()
        while c != "$" {
            try production()
        }

        // resolve RHS references to nonTerminals
        for ref in nonTerminalReferences {
            ref.alt = nonTerminalDefinitions[ref.name]
        }
    }

    // MARK: Descriptors

    // Paper: dscAdd(L, k, i)
    func addDescriptor(L: GrammarNode, k: Int, i: Int) {
        let d = Descriptor(L: L, k: k, i: i)
        if unique.insert(d).inserted {
            remaining.append(d)
        }
    }

    // Paper: ntAdd(X, j) — add descriptors for all alternates of a nonterminal.
    func addDescriptorsForAlternates(X: GrammarNode, j: Int) {
        var alt = X.alt
        while let node = alt {
            addDescriptor(L: node.seq!, k: j, i: j)
            alt = node.alt
        }
    }

    func getDescriptor() -> Bool {
        if remaining.isEmpty {
            return false
        } else {
            let d = remaining.removeLast()
            cL = d.L
            cU = d.k
            cI = d.i
            return true
        }
    }

    // Paper: bsrAdd(X ::= α·β, i, k, j) — i/k/j are the left extent, pivot and right extent.
    func addYield(L: GrammarNode, i: Int, k: Int, j: Int) {
        let bs = BinarySpan(i: i, k: k, j: j)
        yields[L.number].insert(bs)
    }

    // MARK: Call and return

    // Paper: call(L, i, j) — enter a nonterminal (BSR paper §5.3.1, where "L is Y ::= αX·β":
    // the slot with the dot AFTER the called nonterminal). The paper labels both the CRF node
    // and the BSR element with that slot.
    //
    // The return edge here stores the nonterminal node itself — the dot BEFORE — because one
    // stored node then serves both uses on the way back out (see rtn):
    //   edge.slot        is the yield key      (paper: bsrAdd(L, ...))
    //   edge.slot.seq!   is the paper's L      (paper: dscAdd(L, ...))
    // Storing the paper's L instead would require a backward link to recover the nonterminal
    // for the yield. node ↔ node.seq is a bijection, so this is a relabeling, not a difference.
    func call() {
        // Create the return edge: (L=cL, i=cU), cL is the RHS nonterminal node
        let returnEdge = ParsePosition(slot: cL, index: cU)

        // Create the cluster key: (X=cL.alt!, k=cI), cL.alt! is the LHS nonterminal node
        let clusterKey = ParsePosition(slot: cL.alt!, index: cI)

        // Find or create the parseCluster in the crf
        if let existingCluster = crf[clusterKey] {
            if existingCluster.returns.insert(returnEdge).inserted {
                for pop in existingCluster.pops {
                    addDescriptor(L: cL.seq!, k: cU, i: pop)
                    addYield(L: cL, i: cU, k: cI, j: pop)
                }
            }
        } else {
            let newCluster = ParseCluster()
            crf[clusterKey] = newCluster
            newCluster.returns.insert(returnEdge)
            addDescriptorsForAlternates(X: cL.alt!, j: cI)
        }
    }

    // Paper: rtn(X, k, j) — return from a nonterminal.
    // Only X is passed; the paper's k and j are read from the registers cU and cI.
    func rtn(X: GrammarNode) {
        let clusterKey = ParsePosition(slot: X, index: cU)
        guard let cluster = crf[clusterKey] else { return }

        if cluster.pops.insert(cI).inserted {
            for returnEdge in cluster.returns {
                addDescriptor(L: returnEdge.slot.seq!, k: returnEdge.index, i: cI)
                addYield(L: returnEdge.slot, i: returnEdge.index, k: cU, j: cI)
            }
        }
    }

    // MARK: Parse the input

    func parseInput() throws {
        // Seed initial parse cluster and descriptors
        guard let grammarRoot = nonTerminalDefinitions["S"] else {
            throw GrammarError.missingStartSymbol
        }
        crf[ParsePosition(slot: grammarRoot, index: 0)] = ParseCluster()
        addDescriptorsForAlternates(X: grammarRoot, j: 0)

        // make the yield storage large enough
        yields = Array(repeating: [], count: nodeCount)

        nextDescriptor: while getDescriptor() {
            while true {
                switch cL.kind {
                case .T:
                    // Past the end of input there is nothing to match
                    if cI < input.count && input[cI] == cL.name {
                        addYield(L: cL, i: cU, k: cI, j: cI+1)
                        cI += 1
                        cL = cL.seq!
                    } else {
                        continue nextDescriptor
                    }
                case .N:
                    call()
                    continue nextDescriptor
                case .EPS:
                    addYield(L: cL, i: cU, k: cI, j: cI)
                    cL = cL.seq!
                case .ALT:
                    fatalError(#function + ": ALT should not happen here")
                case .END:
                    let nt = cL.seq! // the seq link of an END node points back to the nonTerminal node
                    addYield(L: nt, i: cU, k: cU, j: cI)
                    rtn(X: nt)
                    continue nextDescriptor
                }
            }
        }
    }

    /// True when the start symbol yields a span covering the whole input.
    var parseAccepted: Bool {
        guard let root = nonTerminalDefinitions["S"], yields.indices.contains(root.number) else {
            return false
        }
        return yields[root.number].contains { $0.i == 0 && $0.j == input.count }
    }

    /// Reads the grammar and then the input in one go, which is what every caller wants.
    /// Grammar errors surface before the input is looked at, so a caller that wants to draw
    /// the grammar of a rejected input can still do so from `nonTerminalDefinitions`.
    func run() throws {
        try parseGrammar()
        try parseInput()
    }
}
