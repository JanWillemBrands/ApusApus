//
//  GenerateParser.swift
//  ApusApus
//
//  Created by Johannes Brands on 26/12/2024.
//

import OSLog
import Foundation

class ParserGenerator {
    
    let parserFile: URL
    let grammar: Grammar
    
    init(outputFile: URL, grammar: Grammar) {
        self.parserFile = outputFile
        self.grammar = grammar
    }
    
    var content = #"""
        
        // MARK: - start of template code
        import Foundation
        import RegexBuilder
        
        var tokens: [Token] = []
        var trivia: [[Token]] = []
        var cI = 0
        var token: Token { tokens[cI] }

        func lineBreakCountBetweenTokens(at first: Int, and second: Int) -> Int {
            guard let input = tokens[first].image.base else { return 0 }
            let span = input[tokens[first].image.startIndex..<tokens[second].image.startIndex]
            var breaks = 0
            var prevWasCR = false
            for ch in span {
                let isCR = ch == "\r"
                let isLF = ch == "\n"
                if isCR || (isLF && !prevWasCR) { breaks += 1 }
                prevWasCR = isCR
            }
            return breaks
        }

        func hasInterTokenGap(at first: Int, and second: Int) -> Bool {
            tokens[first].image.endIndex < tokens[second].image.startIndex
        }

        func boundary(_ kind: String) {
            guard cI > 0 && cI < tokens.count else {
                fatalError("boundary '\(kind)' cannot be evaluated at token index \(cI)")
            }
            let left = cI - 1
            let right = cI
            switch kind {
            case "<s>":
                if !hasInterTokenGap(at: left, and: right) {
                    fatalError("expected spacing between tokens around '\(kind)'")
                }
            case "<n>":
                if lineBreakCountBetweenTokens(at: left, and: right) == 0 {
                    fatalError("expected line break between tokens around '\(kind)'")
                }
            case ">s<":
                if hasInterTokenGap(at: left, and: right) {
                    fatalError("expected adjacency between tokens around '\(kind)'")
                }
            case ">n<":
                if lineBreakCountBetweenTokens(at: left, and: right) > 0 {
                    fatalError("expected same line between tokens around '\(kind)'")
                }
            default:
                fatalError("unknown boundary token '\(kind)'")
            }
        }
        
        func expect(_ expected: String...) {
            if !expected.contains(token.kind) {
                let position = token.image.base.linePosition(of: token.image.startIndex)
                fatalError("\(position): expected \(expected) but found \"\(token.kind)\"")
            }
        }
        
        // MARK: - start of generated code
        
        """#
    
    func generate() throws {
        
        // Emit preamble actions (global code before everything)
        emit(actions: grammar.preamble)
        
        // TODO: check escapes etc.
        emit(dent: .NR, "let tokenPatterns: [String:TokenPattern] = [")
        for (kind, pattern) in grammar.terminals.sorted(by: { !$0.value.isLiteral && $1.value.isLiteral } ) {
            // The kind is a Swift string-literal KEY here, so it needs escaping like the source
            // does: an anonymous literal's kind carries its own quotes (`"{"`) and an anonymous
            // regex's kind its own delimiters and backslashes (`/\w+/`).
            let key = kind.escapesAdded
            if pattern.isLiteral {
                emit("\"", key, "\":\t(\"", pattern.source.escapesAdded, "\",\tRegex { \"", pattern.source.escapesAdded, "\" },\t", pattern.isLiteral, ",\t", pattern.isSkip, "),")
            } else {
                emit("\"", key, "\":\t(\"", pattern.source.escapesAdded, "\",\t", pattern.source, ",\t", pattern.isLiteral, ",\t", pattern.isSkip, "),")
            }
        }
        emit(dent: .LN, "]")
        
        for (name, node) in grammar.nonTerminals.sorted(by: { $0.key < $1.key }) {
            if let sig = node.signature {
                emit(dent: .NR, "func ", name, "() ", sig, " {")
            } else {
                emit(dent: .NR, "func ", name, "() throws {")
            }
            // Actions between "=" and body land on the first ALT node
            // and are emitted naturally by emitAlternatives.
            emitAlternatives(firstAlt: node.alt!)
            emit(dent: .LN, "}")
        }
        
        emit(dent: .NR, "func parse() throws {")
        emit("try \(grammar.startSymbol)()")
        emit("expect(\"$\")")
        emit(dent: .LN, "}")
        
        // Emit epilogue actions (global code after everything)
        emit(actions: grammar.epilogue)

        try content.write(to: parserFile, atomically: true, encoding: .utf8)
    }
    
    // Emits dispatch over an ALT chain.
    // Single alternate: emits directly.
    // Two or more: emits switch/case.
    private func emitAlternatives(firstAlt: GrammarNode, dispatched: Set<String>? = nil, defaultBreak: Bool = false) {
        // Collect all ALT nodes
        var alts: [GrammarNode] = []
        var current: GrammarNode? = firstAlt
        while let alt = current {
            alts.append(alt)
            current = alt.alt
        }
        
        if alts.count == 1 {
            // Single alternate: emit directly
            let prefix = emitActionsExtractingPrefix(alts[0].actions)
            emitSequence(alts[0].seq!, dispatched: dispatched, pendingPrefix: prefix)
        } else {
            // Multiple alternates: switch on token kind (grammar is LL(1))
            emit(dent: .NR, "switch token.kind {")
            var allTokens: Set<String> = []
            for alt in alts {
                let tokens = alt.first.subtracting([""])
                if tokens.isEmpty {
                    // Epsilon-only alternate: becomes default case
                    emit(dent: .LR, "default:")
                } else {
                    allTokens.formUnion(tokens)
                    emit(dent: .LR, "case \(commaList(tokens)):")
                }
                let prefix = emitActionsExtractingPrefix(alt.actions)
                emitSequence(alt.seq!, dispatched: tokens, pendingPrefix: prefix)
            }
            if !alts.contains(where: { $0.first.subtracting([""]).isEmpty }) {
                emit(dent: .LR, "default:")
                if defaultBreak {
                    emit("break")
                } else {
                    emit("expect(\(commaList(allTokens)))")
                }
            }
            emit(dent: .LN, "}")
        }
    }
    
    /// Walks a sequence via .seq links, emitting code for each node until END.
    /// When `dispatched` is non-nil, the first terminal in the sequence that matches
    /// a dispatched token emits `next()` instead of `expect()`, since the dispatch
    /// already confirmed the token kind.
    /// Supports prefix actions: if the last action before a symbol ends with `=`,
    /// it is combined with the symbol's generated code on one line.
    private func emitSequence(_ node: GrammarNode, dispatched: Set<String>? = nil, pendingPrefix: String? = nil) {
        var current: GrammarNode? = node
        var dispatched = dispatched
        var pendingPrefix = pendingPrefix
        while let n = current {
            switch n.kind {
            case .T, .TI, .C:
                if let tokens = dispatched, tokens.contains(n.name) {
                    dispatched = nil
                } else {
                    emit("expect(\"\(n.name.escapesAdded)\")")
                }
                if let prefix = pendingPrefix {
                    emit(prefix, " token")
                    pendingPrefix = nil
                }
                emit("cI += 1")
            case .B:
                dispatched = nil
                if let prefix = pendingPrefix {
                    emit(prefix, " token")
                    pendingPrefix = nil
                }
                emit("boundary(\"\(n.name.escapesAdded)\")")
            case .EPS:
                dispatched = nil
                pendingPrefix = nil
            case .N:
                dispatched = nil
                if let prefix = pendingPrefix {
                    emit(prefix, " try \(n.name)()")
                    pendingPrefix = nil
                } else {
                    emit("try \(n.name)()")
                }
            case .DO:
                dispatched = nil
                pendingPrefix = nil
                emitAlternatives(firstAlt: n.alt!)
            case .OPT:
                dispatched = nil
                pendingPrefix = nil
                let tokens = innerFirst(of: n)
                if altCount(from: n.alt!) > 1 {
                    emitAlternatives(firstAlt: n.alt!, defaultBreak: true)
                } else {
                    emit(dent: .NR, "if [\(commaList(tokens))].contains(token.kind) {")
                    emitAlternatives(firstAlt: n.alt!, dispatched: tokens)
                    emit(dent: .LN, "}")
                }
            case .KLN:
                dispatched = nil
                pendingPrefix = nil
                let tokens = innerFirst(of: n)
                emit(dent: .NR, "while [\(commaList(tokens))].contains(token.kind) {")
                emitAlternatives(firstAlt: n.alt!, dispatched: tokens)
                emit(dent: .LN, "}")
            case .POS:
                dispatched = nil
                pendingPrefix = nil
                let tokens = innerFirst(of: n)
                emit(dent: .NR, "repeat {")
                emitAlternatives(firstAlt: n.alt!)
                emit(dent: .LN, "} while [\(commaList(tokens))].contains(token.kind)")
            case .END:
                pendingPrefix = emitActionsExtractingPrefix(n.actions)
               return
            case .ALT:
                fatalError("ALT node encountered in \(#function)")
            case .EOS:
                return
            }
            pendingPrefix = emitActionsExtractingPrefix(n.actions)
            current = n.seq
        }
    }
    
    // MARK: - Prefix Action Helpers
    
    /// Detects whether an action string is a prefix action (ends with `=` but not `==`, `!=`, etc.)
    private func isPrefixAction(_ text: String) -> Bool {
        let trimmed = text.trimmingCharacters(in: .whitespacesAndNewlines)
        guard trimmed.hasSuffix("=") else { return false }
        for op in ["==", "!=", ">=", "<=", "+=", "-=", "*=", "/="] {
            if trimmed.hasSuffix(op) { return false }
        }
        return true
    }
    
    /// Emits all actions, but if the last one is a prefix action, returns it as pending.
    /// The caller is responsible for combining the pending prefix with the next symbol's code.
    private func emitActionsExtractingPrefix(_ actions: [String]) -> String? {
        guard !actions.isEmpty else { return nil }
        if isPrefixAction(actions.last!) {
            emit(actions: Array(actions.dropLast()))
            return actions.last!
        }
        emit(actions: actions)
        return nil
    }
    
    // MARK: - Helpers
    
    private func commaList(_ set: Set<String>) -> String {
        let escapedSet = set.sorted().map { "\"\($0.escapesAdded)\"" }
        return escapedSet.joined(separator: ", ")
    }
    
    private func altCount(from firstAlt: GrammarNode) -> Int {
        var count = 0
        var current: GrammarNode? = firstAlt
        while let alt = current {
            count += 1
            current = alt.alt
        }
        return count
    }
    
    /// Collects the FIRST tokens of a bracket's inner ALT chain,
    /// excluding epsilon. This avoids using the bracket node's own .first
    /// which has continuation tokens folded in.
    private func innerFirst(of bracket: GrammarNode) -> Set<String> {
        var result: Set<String> = []
        var current = bracket.alt
        while let alt = current {
            result.formUnion(alt.first.subtracting([""])) 
            current = alt.alt
        }
        return result
    }

    // IndentMode specifies the increase or decrease of indentation before and after emitting the items
    enum IndentMode { case NN, LN, NR, LR, RL }

    var indentation = 0
    
    func emit(dent: IndentMode = .NN, _ items: Any..., terminator: String = "\n") {
        switch dent {
        case .NN: break
        case .LN: indentation -= 1
        case .NR: break
        case .LR: indentation -= 1
        case .RL: indentation += 1
        }
        
        for _ in 0 ..< indentation {
            content.append("\t")
        }
        for item in items {
            content.append("\(item)")
        }
        content.append(terminator)
        
        switch dent {
        case .NN: break
        case .LN: break
        case .NR: indentation += 1
        case .LR: indentation += 1
        case .RL: indentation -= 1
        }
    }
    
    func emit(actions: [String]) {
        for action in actions {
            // 1. Split the action string into an array of lines,
            // preserving empty lines between text.
            var lines = action.components(separatedBy: "\n")
            guard !lines.isEmpty else { continue }

            // 2. Check if the FIRST line is only whitespace.
            // If so, remove it from the array.
            if let firstLine = lines.first, firstLine.allSatisfy({ $0.isWhitespace }) {
                lines.removeFirst()
            }

            // 3. Re-verify the array isn't empty after potential first-line removal,
            // then identify the last line to determine the stripping rule.
            guard let lastLine = lines.last else { continue }
            
            // 4. Rule Discovery: If the last line is pure whitespace (upto the trailing @, which was removed from the action),
            // its length is our limit. Otherwise, we strip ALL leading whitespace.
            let isOnlyWhitespace = !lastLine.isEmpty && lastLine.allSatisfy { $0.isWhitespace }
            let maxStripCount = isOnlyWhitespace ? lastLine.count : Int.max
            
            // 5. Select which lines to process.
            // If the last line was just whitespace (used for the count), exclude it from output.
            let linesToProcess = isOnlyWhitespace ? lines.dropLast() : ArraySlice(lines)
            
            for line in linesToProcess {
                var currentLine = line
                var removed = 0
                
                // 6. Strip leading whitespace character-by-character.
                // This stops if we hit a non-whitespace character OR reach the maxStripCount.
                while removed < maxStripCount, let first = currentLine.first, first.isWhitespace {
                    currentLine.removeFirst()
                    removed += 1
                }
                
                // 7. Send the processed line to the final output.
                emit(currentLine)
            }
        }
    }

}
