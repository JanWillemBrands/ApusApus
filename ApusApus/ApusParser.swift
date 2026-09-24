//
//  ApusParser.swift
//  ApusApus
//
//  Created by Johannes Brands on 23/12/2024.
//

import OSLog
import Foundation
import RegexBuilder

enum ApusParserError: Error {
    case terminalNonterminalConflict(symbols: Set<String>)
    case invalidRegex(image: String, error: Error)
    case unexpectedToken(explanation: String)
    case scanningFailed(error: Error)
    case undefinedNonTerminal(name: String, definedAsTerminal: Bool)
    case startSymbolNotFound(name: String)
}

class ApusParser {
    
    let grammar = Grammar()
    var scanner: Scanner
    var tokens: [Token] { scanner.tokens }
    var cI: Int = 0               // current input position
    var token: Token { tokens[cI] }
    
    init(fromString inputString: String) throws {
        do {
            scanner = try Scanner(fromString: inputString, patterns: apusTerminals)
        } catch {
            Logger.scan.error("Failed to create scanner for input string '\(inputString.prefix(100), privacy: .public)'")
            throw ApusParserError.scanningFailed(error: error)
        }
    }
    
    init(fromFile inputFileURL: URL) throws {
        // Define a list of commonly supported encodings
        let encodings: [String.Encoding] = [
            .utf8,                // UTF-8
            .macOSRoman,          // Mac Roman (classic Mac OS encoding) PUT HIGH ON THE LIST BECAUSE OF PILCROW QUIRK
            .isoLatin1,           // ISO-8859-1 (Western European)
            .isoLatin2,           // ISO-8859-2 (Central/Eastern European)
            .ascii,               // ASCII
            .utf16,               // UTF-16 (with BOM)
            .utf16BigEndian,      // UTF-16 Big Endian
            .utf16LittleEndian,   // UTF-16 Little Endian
            .utf32,               // UTF-32 (with BOM)
            .utf32BigEndian,      // UTF-32 Big Endian
            .utf32LittleEndian,   // UTF-32 Little Endian
            .windowsCP1250,       // Windows Central European
            .windowsCP1251,       // Windows Cyrillic
            .windowsCP1252,       // Windows Latin-1
            .windowsCP1253,       // Windows Greek
            .windowsCP1254,       // Windows Turkish
            // Add more encodings as needed via raw values below
        ]
        
        var input = ""
        for encoding in encodings {
            do {
                input = try String(contentsOf: inputFileURL, encoding: encoding)
                break
            } catch {
                Logger.scan.error("Failed reading input file with \(encoding, privacy: .public): \(error)")
            }
        }
        do {
            scanner = try Scanner(fromString: input, patterns: apusTerminals)
        } catch {
            Logger.scan.info("Failed to create scanner for input file: \(inputFileURL, privacy: .public)")
            throw ApusParserError.scanningFailed(error: error)
        }
    }
    
    func parse(explicitStartSymbol: String = "") throws -> Grammar {
        cI = 0
        
        grammar.startSymbol = explicitStartSymbol
        try parseApusGrammar()
        
        let DUMP = false
        if DUMP {
            print("terminals: \(grammar.terminals.count)")
            for (name, tokenPattern) in grammar.terminals {
                print("\t", name, "\t", tokenPattern.source)
            }
            print("nonTerminals:")
            for (name, node) in grammar.nonTerminals {
                print("\t", name, "\t", node.kind)
            }
        }
        
        // TODO: can we really remove this?
        //        let conflictSet = Set(grammar.terminals.keys).intersection(Set(grammar.nonTerminals.keys))
        //        if !conflictSet.isEmpty {
        //            trace("grammar parser error: the following symbols have been defined as both terminal and nontermimal:", conflictSet)
        //            throw ApusParserError.terminalNonterminalConflict(symbols: conflictSet)
        //        }
        
        guard let root = grammar.nonTerminals[grammar.startSymbol] else {
            throw ApusParserError.startSymbolNotFound(name: grammar.startSymbol)
        }
        grammar.root = root
        let build = GrammarBuild()
        for (name, node) in grammar.nonTerminals.sorted(by: { $0.key > $1.key }) {      // a fixed ordering with 'S' appearing first in small test grammars
            if DUMP { print("Processing END nodes for:", name) }
            node.resolveGrammarNodeLinks(parent: node, alternate: node.alt, build: build)
        }
        grammar.nodeCount = build.nodeCounter
        
        grammar.root.follow.insert("○")
        grammar.finalizeSymbolTable()
        grammar.assignNameIDs()
        
        if DUMP { print("start symbol '\(grammar.startSymbol)' first:", grammar.root.first, "follow:", grammar.root.follow) }
        
        var oldSize = 0
        var newSize = 0
        repeat {
            oldSize = newSize
            newSize = 0
            for (_, node) in grammar.nonTerminals {
                if DUMP { print("nonterminalcount", grammar.nonTerminals.count) }
                GrammarNode.sizeofSets = 0
                try grammar.populateFirstFollowSets(for: node)
                newSize += GrammarNode.sizeofSets
            }
            if DUMP { print("first & follow", newSize) }
        } while newSize != oldSize
        // store the cumulative set size
        GrammarNode.sizeofSets = newSize
        
        // this is to a give GrammarNodes access to their own grammar
        GrammarNode.grammar = grammar
        
        var isLL1 = true
        for (name, node) in grammar.nonTerminals {
            if DUMP { print("Detecting ambiguity for:", name) }
            if !node.verifyLL1() { isLL1 = false }
            node.detectSchrödingerConflict()
        }
        grammar.isLL1 = isLL1
        grammar.propagateExcludeSets()
        grammar.diagnosePredicateTargets()
        try grammar.populateBitSets()
        
        return grammar
    }
    
    private var skip = false
    private var terminalAlias: String?
    
    func parseApusGrammar() throws {
        // Collect preamble actions (before first production)
        grammar.preamble = collectActions(at: 0)
        
        try expect(["identifier", "pragma"])
        repeat {
            try production()
        } while token.kind == "identifier" || token.kind == "pragma"
        
        // Collect epilogue actions (after last production, before messages/$)
        grammar.epilogue = collectActions(at: cI)
        
        try expect(["message", "○"])
        while token.kind == "message" {
            message()
        }
        
        try expect(["○"])
    }
    
    func production() throws {
        var disambiguationAnnotation: Disambiguation?
        if token.kind == "pragma", let d = Disambiguation(rawValue: token.stripped) {
            disambiguationAnnotation = d
            cI += 1
        }
        // `@sameLine` — a whole-nonterminal span property, so it sits at the
        // production start next to `@longest`/`@shortest`. The Oracle prunes this
        // nonterminal's LHS completion yields; it is not an alternate-level notion.
        var sameLineAnnotation = false
        if token.kind == "pragma", token.stripped == "sameLine" {
            sameLineAnnotation = true
            cI += 1
        }
        // `@literalMunch` — marks a regex terminal as participating in
        // literal-suppression maximal munch. See TODO #0.
        var isLiteralMunchAnnotation = false
        if token.kind == "pragma", token.stripped == "literalMunch" {
            isLiteralMunchAnnotation = true
            cI += 1
        }
        // `@preempt(X)` / `@preempt(X, N)` — this terminal's maximal munch must not swallow something
        // of higher priority. Both regex literals and generics were bolted onto an already-mature
        // Swift, so its lexer has to pre-empt operator munching for them; this states that directly.
        //   X — the terminal whose start positions define the SPLIT POINTS. It names a specific
        //       token shape rather than deriving split points from `FIRST(N)`, whose members may
        //       differ in spelling and boundary behavior.
        //   N — OPTIONAL: the construct that must actually PARSE at a split point for the shorter
        //       reading to win. Without it the split is merely offered (today's generics use).
        var preemptStartName: String? = nil
        var preemptConstructName: String? = nil
        if token.kind == "pragma", token.stripped == "preempt" {
            cI += 1
            try expect(["("]); cI += 1
            try expect(["identifier"])
            preemptStartName = String(token.image)
            cI += 1
            if token.kind == "," {
                cI += 1
                try expect(["identifier"])
                preemptConstructName = String(token.image)
                cI += 1
            }
            try expect([")"]); cI += 1
        }
        try expect(["identifier"])
        let nonTerminalName = String(token.image)
        cI += 1
        
        let operatorKind = token.kind
        let hasDirectTerminalBody = productionStartsWithDirectTerminalBody(afterOperatorAt: cI)
        
        if (operatorKind == "-" || operatorKind == ":") && hasDirectTerminalBody {
            // direct terminal definition: ":" = silent, "-" = visible.
            // Structured ":" and "-" are handled below as recogniser-backed trivia / lexical
            // nonterminals.
            skip = (token.kind == ":")
            cI += 1
            switch token.kind {
            case "regex":
                // assign the name of the production to the regex
                terminalAlias = nonTerminalName
                _ = try regex()
                if isLiteralMunchAnnotation { grammar.terminals[nonTerminalName]?.isLiteralMunch = true }
                if let ps = preemptStartName { grammar.terminals[nonTerminalName]?.preemptStart = ps }
                if let pc = preemptConstructName { grammar.terminals[nonTerminalName]?.preemptConstruct = pc }
            case "literal":
                // A named literal terminal gets its OWN kind, named by the LHS — the same rule the
                // regex branch applies via `terminalAlias`. It used to register kind `"…"` (the
                // quoted form) and file the LHS in a `literalAliases` side table, so the name never
                // became a kind at all; that asymmetry between the two terminal shapes is gone.
                _ = literal(named: nonTerminalName)
            case "pragma" where token.stripped == "builder":
                // `@builder` — the terminal's scanner regex comes from the Swift
                // RegexBuilder library (GrammarRegexLibrary.swift), keyed by name.
                //   name - @builder .          → ApusRegexLibrary.patterns["name"]
                //   name - @builder(key) .     → ApusRegexLibrary.patterns["key"]
                _ = try regexBuilder(name: nonTerminalName)
                if isLiteralMunchAnnotation { grammar.terminals[nonTerminalName]?.isLiteralMunch = true }
                if let ps = preemptStartName { grammar.terminals[nonTerminalName]?.preemptStart = ps }
                if let pc = preemptConstructName { grammar.terminals[nonTerminalName]?.preemptConstruct = pc }
            default:
                try expect(["regex", "literal", "pragma"])
            }
            
            // reset
            terminalAlias = nil
            skip = false
            
            try expect(["."])
            cI += 1
            
            // Gated-transition annotation (=== "gate" [<<<] [>>> "push"]) retired
            // in the scanner-retirement commit. Scanner mode-stack and
            // `TokenPattern.transitions` are gone; LCNP per-terminal lex
            // makes mode gating unnecessary.
            
            
        } else {
            // production rule — `=` for emit, `:` for trivia, `-` for a lexical nonterminal
            // (body recognized by a GLL sub-parse, emitted as one token; references to it resolve
            // to a terminal — see GrammarNode.isLexicalToken).
            try expect(["=", ":", "-"])
            let isTrivia = token.kind == ":"
            let isLexical = token.kind == "-"
            
            // Collect signature actions (between nonterminal name and operator)
            let signatureActions = collectActions(at: cI)
            cI += 1
            // Actions between operator and body naturally land on the first ALT
            // node via sequence()'s collectActions(at: cI) — no separate locals
            // collection needed.
            if !isTrivia, !isLexical, grammar.startSymbol == "" {
                grammar.startSymbol = nonTerminalName
            }
            let node = try selection()
            let lhsNode: GrammarNode
            if let existing = grammar.nonTerminals[nonTerminalName] {
                var endOfList = existing
                while let next = endOfList.alt {
                    endOfList = next
                }
                endOfList.alt = node
                lhsNode = existing
            } else {
                lhsNode = GrammarNode(kind: .N, name: nonTerminalName, alt: node)
                grammar.nonTerminals[nonTerminalName] = lhsNode
            }
            if isTrivia {
                lhsNode.isTrivia = true
                markRecognizerBodySuppressesLeadingTrivia(node)
            }
            if isLexical {
                lhsNode.isLexicalToken = true
                markRecognizerBodySuppressesLeadingTrivia(node)
                // Register the name as a terminal so references in other productions resolve to
                // `.T` (a single token) rather than expanding the body inline. The TokenPattern is
                // a marker only — its match is computed by a GLL sub-parse (lexicalTokenRecognisers).
                if grammar.terminals[nonTerminalName] == nil {
                    var pat = TokenPattern(nonTerminalName, Regex { nonTerminalName }, false, false)
                    pat.isLexicalToken = true
                    grammar.terminals[nonTerminalName] = pat
                    _ = grammar.registerTerminal(nonTerminalName)
                }
            }
            if let sig = signatureActions.first {
                lhsNode.signature = sig
            }
            if let d = disambiguationAnnotation {
                lhsNode.disambiguation = d
            }
            if sameLineAnnotation {
                lhsNode.requiresSameLine = true
            }
            try expect(["."])
            cI += 1
            
        }
    }
    
    private func markRecognizerBodySuppressesLeadingTrivia(_ node: GrammarNode?) {
        guard let node else { return }
        switch node.kind {
        case .T, .TI, .C:
            node.suppressesLeadingTrivia = true
            markRecognizerBodySuppressesLeadingTrivia(node.seq)
        case .B, .EPS:
            markRecognizerBodySuppressesLeadingTrivia(node.seq)
        case .ALT:
            for symbol in node.bodySymbols {
                markRecognizerBodySuppressesLeadingTrivia(symbol)
            }
            markRecognizerBodySuppressesLeadingTrivia(node.alt)
        case .DO, .OPT, .POS, .KLN:
            markRecognizerBodySuppressesLeadingTrivia(node.alt)
            markRecognizerBodySuppressesLeadingTrivia(node.seq)
        case .N:
            // Do not cross into the referenced nonterminal's definition. This is the scoped
            // boundary: a structured recognizer may call a normal `=` payload, whose terminals
            // keep normal leading-trivia skipping, then resume exact matching in the recognizer body.
            markRecognizerBodySuppressesLeadingTrivia(node.seq)
        default:
            markRecognizerBodySuppressesLeadingTrivia(node.seq)
        }
    }
    
    /// True when a `:` / `-` RHS is the direct scanner-terminal shape:
    /// regex, literal, `@builder`, or `@builder(key)`, followed by the dot.
    /// Anything else is treated as structured syntax.
    private func productionStartsWithDirectTerminalBody(afterOperatorAt operatorIndex: Int) -> Bool {
        var i = operatorIndex + 1
        switch tokens[i].kind {
        case "regex", "literal":
            i += 1
        case "pragma" where tokens[i].stripped == "builder":
            i += 1
            if tokens[i].kind == "(" {
                i += 1
                guard tokens[i].kind == "identifier" || tokens[i].kind == "literal" else { return false }
                i += 1
                guard tokens[i].kind == ")" else { return false }
                i += 1
            }
        default:
            return false
        }
        return tokens[i].kind == "."
    }
    
    func message() {
        grammar.messages.append(token.stripped)
        cI += 1
    }
    
    func selection() throws -> GrammarNode {
        // skip an optional first "|" to enable compact grammar formatting of multiple alternates
        if token.kind == "|" { cI += 1 }
        
        let startOfAlternates = try sequence()
        var tmp = startOfAlternates
        while token.kind == "|" {
            cI += 1
            tmp.alt = try sequence()
            tmp = tmp.alt!
        }
        return startOfAlternates
    }
    
    /// Collect action tokens from the skipped tokens at the given visible-token index.
    /// Since action is a silent terminal, action tokens land in scanner.skippedTokens.
    private func collectActions(at index: Int) -> [String] {
        guard index < scanner.trivia.count else { return [] }
        return scanner.trivia[index]
            .filter { $0.kind == "action" }
            .map { $0.stripped }
    }
    
    func sequence() throws -> GrammarNode {
        // sequence = < layout | tokenLookaround | factor [ "?" | "*" | "+" ] > .
        // Actions are collected from skippedTokens at each position.
        let startOfSequence = GrammarNode(kind: .ALT, name: "")
        var termNode = startOfSequence
        
        // Alternate-level annotations, placed at the alternate's start (right after `=`,
        // `|`, or an opening `(`/`[`/`{`/`<`). They ALWAYS annotate this ALT node and
        // can appear in any order before the first factor.
        //
        // `@prefer` marks this alternate a WINNER (its siblings lose where they tile the
        // same span). `@avoid` marks this alternate a LOSER — the dual of `@prefer`. Its
        // rivals are its explicit siblings AND, when the enclosing group is an OPT/KLN,
        // that group's implicit empty (skip) branch. So `[ @avoid X ]` means "prefer the
        // skip", spelled as an annotation on the body alternate `X` rather than on the
        // bracket. The Oracle picks the mechanism by group shape (same-span `PreferRule`
        // for non-empty siblings; follower-pivot for the epsilon skip) — see
        // `registerPrefer` / the OPT/KLN walk.
        //
        // `@confinedTo(N)` / `@excludedFrom(N)` are containment predicates on this
        // alternate's span.
        //
        // `@cannotParse(N)` / `@canParse(N)` are parse predicates with NONTERMINAL
        // operands at this alternate start. Captured on this ALT node; the Oracle anchors
        // the prune on the alternate's first body symbol (yield start = alternate start).
        // Symbolic `>->`/`>+>` stays reserved for token lookaround.
        //
        // Node-level extent/associativity (`@longest`/`@shortest`/`@left`/`@right`) are
        // NOT here — they attach to the whole group, parsed before the LHS
        // (`production()`) or before the bracket (`factor()`).
        annotationLoop: while token.kind == "pragma" {
            switch token.stripped {
            case "prefer":
                startOfSequence.isPreferred = true
                cI += 1
            case "avoid":
                startOfSequence.isAvoided = true
                cI += 1
            case "confinedTo", "excludedFrom":
                let negated = token.stripped == "excludedFrom"
                cI += 1
                try expect(["("]); cI += 1
                try expect(["identifier"])
                if negated { startOfSequence.excludedFromContainers.append(String(token.image)) }
                else       { startOfSequence.confinedToContainers.append(String(token.image)) }
                cI += 1
                try expect([")"]); cI += 1
            case "cannotParse", "canParse":
                let negated = token.stripped == "cannotParse"
                cI += 1
                try expect(["("]); cI += 1
                repeat {
                    try expect(["identifier"])
                    startOfSequence.forwardPredicates.append(
                        ForwardPredicate(targetName: String(token.image), negated: negated)
                    )
                    cI += 1
                } while token.kind == "identifier"
                try expect([")"]); cI += 1
            default:
                break annotationLoop
            }
        }
        
        // leading actions (before first factor)
        termNode.actions = collectActions(at: cI)
        
        repeat {
            switch token.kind {
            case "<n>", "<s>", ">>|", ">n<", ">s<", "|<<":
                let layoutNode = layout()
                termNode.seq = layoutNode
                termNode = layoutNode
                termNode.actions = collectActions(at: cI)
            case ">+>", ">->", "<+<", "<-<":
                let lookaroundNode = try tokenLookaround(after: termNode)
                termNode.seq = lookaroundNode
                termNode = lookaroundNode
                termNode.actions = collectActions(at: cI)
            case "(", "<", "[", "epsilon", "empty", "identifier", "literal", "regex", "{", "pragma":
                // "pragma" here = a node-level group prefix (@longest/@shortest/@left/
                // @right before a bracket); factor() consumes it and attaches it to the
                // group. (@prefer/@avoid were consumed at sequence start; terminal-def
                // pragmas live in production().)
                var factorNode = try factor()
                switch token.kind {
                case "?", "*", "+":
                    let miniSeq = GrammarNode(kind: .ALT, name: "")
                    miniSeq.seq = factorNode
                    miniSeq.seq?.seq = GrammarNode(kind: .END, name: "")
                    
                    if token.kind == "?" { factorNode = GrammarNode(kind: .OPT, name: "", alt: miniSeq) }
                    if token.kind == "*" { factorNode = GrammarNode(kind: .KLN, name: "", alt: miniSeq) }
                    if token.kind == "+" { factorNode = GrammarNode(kind: .POS, name: "", alt: miniSeq) }

//                    switch token.kind {
//                    case "?":
//                        factorNode = GrammarNode(kind: .OPT, name: "", alt: miniSeq)
//                    case "*":
//                        factorNode = GrammarNode(kind: .KLN, name: "", alt: miniSeq)
//                    case "+":
//                        factorNode = GrammarNode(kind: .POS, name: "", alt: miniSeq)
//                    default:
//                        break
//                    }
//                    factorNode.alt = miniSeq
                    cI += 1
                default:
                    break
                }
                
                termNode.seq = factorNode
                termNode = factorNode
                termNode.actions = collectActions(at: cI)
            default:
                try expect(["(", "<", "<n>", "<s>", ">>|", ">n<", ">s<", ">+>", ">->", "<+<", "<-<", "[", "identifier", "literal", "regex", "epsilon", "empty", "{", "|<<"])
            }
            
        } while ["(", "<", "<n>", "<s>", ">>|", ">n<", ">s<", ">+>", ">->", "<+<", "<-<", "[", "epsilon", "empty", "identifier", "literal", "regex", "{", "|<<", "pragma"].contains(token.kind)
        
        termNode.seq = GrammarNode(kind: .END, name: "")
        // the .alt and .seq links of an END node are set in resolveEndNodeLinks()
        return startOfSequence
    }
    
    func layout() -> GrammarNode {
        let name = token.kind
        grammar.registerTerminal(name)
        cI += 1
        if ["<n>", "<s>", ">n<", ">s<"].contains(name) {
            return GrammarNode(kind: .B, name: name)
        } else {    // ">>|", "|<<"
            grammar.usesInjectedLayoutTokens = true
            return GrammarNode(kind: .T, name: name)
        }
    }
    
    func tokenLookaround(after previous: GrammarNode) throws -> GrammarNode {
        let head = token.kind
        let positive = head == ">+>" || head == "<+<"
        let isLookbehind = head == "<+<" || head == "<-<"
        cI += 1
        try expect(["("])
        cI += 1
        
        var kinds: Set<String> = []
        while token.kind == "literal" || token.kind == "identifier" {
            let kind = token.kind == "literal" ? String(token.image) : token.stripped
            if !token.stripped.isEmpty {
                let resolvedKind = kind == "EOF" ? "○" : kind
                if token.kind == "literal", grammar.terminals[resolvedKind] == nil {
                    let source = token.stripped.escapesRemoved
                    let regex = Regex { source }
                    grammar.terminals[resolvedKind] = TokenPattern(source, regex, true, false)
                    grammar.registerTerminal(resolvedKind)
                }
                kinds.insert(resolvedKind)
            }
            cI += 1
        }
        try expect([")"])
        cI += 1
        
        let name = "\(head)(\(kinds.sorted().joined(separator: " ")))"
        grammar.registerTerminal(name)
        let node = GrammarNode(kind: .B, name: name)
        if isLookbehind {
            node.boundaryPredicate = .tokenLookbehind(positive: positive, kinds: kinds, distance: 1)
        } else {
            node.boundaryPredicate = .tokenLookahead(positive: positive, kinds: kinds)
        }
        return node
    }
    
    //    func layout() throws -> GrammarNode? {
    //        switch token.kind {
    //        case ">>|", "|<<":
    //            let name = token.kind
    //            grammar.usesInjectedLayoutTokens = true
    //            grammar.registerTerminal(name)
    //            cI += 1
    //            return GrammarNode(kind: .T, name: name)
    //        case "<n>", "<s>", ">n<", ">s<":
    //            let name = token.kind
    //            grammar.registerTerminal(name)
    //            cI += 1
    //            return GrammarNode(kind: .B, name: name)
    //        default:
    //            return nil
    //        }
    //    }
    
    func regex() throws -> GrammarNode {
        // A named terminal (`-`/`:`) takes its kind from the LHS; an ANONYMOUS inline regex takes its
        // own pattern INCLUDING the delimiters (`/…/`) as its kind, mirroring the quoted form used
        // for anonymous literals. Content-naming also means two identical inline regexes share one
        // kind — the position-derived name they used to get (`L12P34`) made them distinct terminals
        // with identical patterns.
        let name = terminalAlias ?? String(token.image)
        
        if let definition = grammar.terminals[name] {
            if definition.isSkip != skip {
                Logger.parse.warning("redefinition of \(name, privacy: .public) as \(self.skip ? "skipped" : "not skipped")")
            }
        }
        do {
            // the token is a regex definition, try to initialize a Regex with it
            // Construct as AnyRegexOutput so regexes that include capturing groups (e.g. backreferences like `(#+)…\1`) don't fail the type check.
            // We only ever need the whole-match boundary in the hot path; captures are not consulted by the lexer.
            let regex = try Regex(String(token.stripped))
            grammar.terminals[name] = TokenPattern(String(token.image), regex, false, skip)
            grammar.registerTerminal(name)
        } catch {
            Logger.parse.error("grammar parse error: \(self.token.image, privacy: .public) is not a valid literal Regex \(error, privacy: .public)")
            throw ApusParserError.invalidRegex(image: String(token.image), error: error)
        }
        
        cI += 1
        return GrammarNode(kind: .T, name: name)
    }
    
    /// `@builder` terminal — resolve the scanner regex from `ApusRegexLibrary`
    /// (GrammarRegexLibrary.swift). Current token is the `@builder` pragma; an
    /// optional `(key)` overrides the default lookup key (= the terminal name).
    func regexBuilder(name: String) throws -> GrammarNode {
        cI += 1   // consume `@builder`
        var key = name
        if token.kind == "(" {
            cI += 1
            switch token.kind {
            case "literal":    key = token.stripped
            case "identifier": key = String(token.image)
            default:           try expect(["identifier", "literal"])
            }
            cI += 1
            try expect([")"]); cI += 1
        }
        guard let regex = ApusRegexLibrary.patterns[key] else {
            Logger.parse.error("@builder terminal \(name, privacy: .public) references unknown RegexBuilder '\(key, privacy: .public)' in ApusRegexLibrary.patterns")
            throw ApusParserError.unexpectedToken(explanation: "unknown @builder key '\(key)' for terminal '\(name)'")
        }
        grammar.terminals[name] = TokenPattern(name, regex, false, skip)
        grammar.registerTerminal(name)
        return GrammarNode(kind: .T, name: name)
    }
    
    /// `named` — the LHS of a `-`/`:` terminal definition, which becomes this token's kind.
    /// Nil for an ANONYMOUS inline literal, whose kind is its own pattern INCLUDING the delimiters
    /// (the full quoted form, e.g. `"operator"`). Quoting keeps the anonymous-literal kind namespace
    /// disjoint from the identifier namespace (nonterminals and named terminals), so an unquoted
    /// reference like `operator` in a production body can never collide with the literal
    /// `"operator"`. Anonymous literals sharing a pattern therefore share one kind; a named literal
    /// never merges with an anonymous one, even where both match the same text.
    func literal(named: String? = nil) -> GrammarNode {
        let name = named ?? String(token.image)
        // The unescaped literal CONTENT — what the lexer matches against input characters.
        let source = token.stripped.escapesRemoved
        
        if let definition = grammar.terminals[name] {
            if definition.isSkip != skip {
                Logger.parse.warning("parse warning: redefinition of \(name, privacy: .public) as \(self.skip ? "skipped" : "not skipped")")
            }
        } else {
            let regex = Regex { source }
            grammar.terminals[name] = TokenPattern(source, regex, true, skip)
            grammar.registerTerminal(name)
        }
        
        cI += 1
        return GrammarNode(kind: .T, name: name)
    }
    
    func epsilon() -> GrammarNode {
        cI += 1
        return GrammarNode(kind: .EPS, name: "ε")
    }
    
    func factor() throws -> GrammarNode {
        // Node-level extent/associativity prefix on a group: @longest/@shortest/@left/
        // @right immediately before a bracket annotates that whole bracket node,
        // mirroring the production-start form before a LHS (`@longest X = …`).
        // (@prefer/@avoid are alternate-level and handled in sequence().) It is only
        // meaningful before a bracket; the Oracle reads `disambiguation` on
        // bracket/nonterminal nodes only, so a stray prefix elsewhere is inert.
        var groupDisambiguation: Disambiguation? = nil
        if token.kind == "pragma", let d = Disambiguation(rawValue: token.stripped) {
            groupDisambiguation = d
            cI += 1
        }
        let node: GrammarNode
        switch token.kind {
        case "identifier":
            let name = token.stripped
            if grammar.terminals[name] != nil {
                if grammar.nonTerminals[name] != nil {
                    Logger.parse.error("grammar parse error: \(self.token.image) is both a terminal and a nonTerminal")
                }
                node = GrammarNode(kind: .T, name: name)
            } else {
                node = GrammarNode(kind: .N, name: name)
            }
            cI += 1
        case "literal":
            node = literal()
        case "epsilon", "empty":
            node = epsilon()
        case "regex":
            node = try regex()
        case "(":
            cI += 1
            node = GrammarNode(kind: .DO, name: "", alt: try selection())
            try expect([")"])
            cI += 1
        case "[":
            cI += 1
            // `@avoid`/`@prefer` right after `[` are NOT consumed here — they flow into
            // `selection()` → `sequence()` and land on the body ALT node, exactly like
            // after `=` or `|`. `[ @avoid X ]` therefore marks the alternate `X`, whose
            // implicit rival is the OPT's skip (ε); the Oracle keys the optional-skip off
            // that (see `registerPrefer` / the OPT/KLN walk in Oracle.swift).
            node = GrammarNode(kind: .OPT, name: "", alt: try selection())
            try expect(["]"])
            cI += 1
        case "{":
            cI += 1
            node = GrammarNode(kind: .KLN, name: "", alt: try selection())
            try expect(["}"])
            cI += 1
        case "<":
            cI += 1
            node = GrammarNode(kind: .POS, name: "", alt: try selection())
            try expect([">"])
            cI += 1
        default:
            try expect(["identifier", "literal", "epsilon", "empty", "regex", "(", "[", "{", "<"])
            fatalError("\(#function) expect() should have thrown - this line should never be reached")
        }
        
        // Attach a node-level extent/assoc prefix (parsed above) to the group node.
        if let d = groupDisambiguation {
            node.disambiguation = d
        }
        
        // check for exclusion annotation: ---("if" "while" ...)
        if token.kind == "---" {
            cI += 1
            try expect(["("])
            cI += 1
            while token.kind == "literal" {
                // Exclusion entries must match Token.kind values in the symbol table.
                // User-grammar literal terminals are now keyed by their full quoted form
                // (see literal()), so we record the same form here.
                let excluded = String(token.image)
                if !token.stripped.isEmpty {
                    node.exclude.insert(excluded)
                }
                cI += 1
            }
            try expect([")"])
            cI += 1
        }
        
        return node
    }
    
    func expect(_ expectedTokens : Set<String>) throws {
        var error = "expect \"\(token.kind)\" to be in \(expectedTokens)\n"
        if !expectedTokens.contains(token.kind) {
            error += "parse error: found \"\(token.kind)\" but expected one of \(expectedTokens)\n"
            error += "\(token.image), \(token.image.endIndex > scanner.input.endIndex)\n"
            let lineRange = scanner.input.lineRange(for: token.image.startIndex ..< token.image.endIndex)
            error += "\(scanner.input[lineRange])"
            let before = lineRange.lowerBound ..< token.image.startIndex
            for _ in 0 ..< scanner.input[before].count {
                error += "~"
            }
            for _ in 0 ..< token.image.count {
                error += "^"
            }
            Logger.grammar.error("\(error, privacy: .public)")
            throw ApusParserError.unexpectedToken(explanation: "Failed to parse grammar from symbol \(grammar.startSymbol)")
        }
    }
    
}
