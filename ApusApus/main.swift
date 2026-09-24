//
//  main.swift
//  ApusApus
//
//  Created by Johannes Brands on 01/03/2024.
//

import OSLog
import Foundation

// The CLI parses ONE message, so the per-parse report is the whole point here.
// It defaults off for the test suites, which parse thousands — see `parseReports`.
parseReports = true

let grammarURL = URL(fileURLWithPath: #filePath)
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .appendingPathComponent("grammars/Swift")
//    .appendingPathComponent("grammars/layout")
//    .appendingPathComponent("grammars/apus")
//    .appendingPathComponent("grammars/Python/Python")
//    .appendingPathComponent("grammars/ScanModeTest")
//    .appendingPathComponent("grammars/CommentTest")
//    .appendingPathComponent("grammars/attributeHunt")
//    .appendingPathComponent("grammars/AfroozehHunt")
//    .appendingPathComponent("grammars/apusWithAction")
//    .appendingPathComponent("grammars/TortureSyntax")
//    .appendingPathComponent("grammars/test")
//    .appendingPathComponent("grammars/regex-operator")
//    .appendingPathComponent("grammars/tortureART")
//    .appendingPathComponent("grammars/tortureEBNF")
//    .appendingPathComponent("grammars/apusAmbiguous")
    .appendingPathExtension("apus")

let grammar: Grammar
do {
    let apusParser = try ApusParser(fromFile: grammarURL)
    do {
        grammar = try apusParser.parse(explicitStartSymbol: "")
    } catch {
        Logger.ui.error("failed to parse grammar: \(grammarURL, privacy: .public), error: \(error)")
        exit(1)
    }
} catch {
    Logger.ui.error("failed to scan grammar: \(grammarURL, privacy: .public), error: \(error)")
    exit(1)
}

let messageParser = MessageParser(grammar: grammar)

print("grammar: \(grammarURL.lastPathComponent), messages: \(grammar.messages.count)")
if grammar.messages.isEmpty {
    print("no messages found (^^^ blocks). nothing to parse")
}

for (mi, message) in grammar.messages.enumerated() {
    print("\n=== message \(mi+1)/\(grammar.messages.count): \(message.prefix(60)) ===")
    let input: String
    if message.hasPrefix("#") {
        let fileName = message.dropFirst().trimmingCharacters(in: .whitespacesAndNewlines)
        let messageFileURL = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .appendingPathComponent(fileName)
        do {
            input = try String(contentsOf: messageFileURL, encoding: .utf8)
        } catch {
            Logger.ui.error("failed to read message file: \(messageFileURL.lastPathComponent, privacy: .public)")
            continue
        }
    } else {
        input = String(message)
    }

    // use the AST to parse the message
    let start = clock()

    for _ in 0..<1 {
        messageParser.parse(input: input)
    }

    let end = clock()
    let cpuTime = Double(end - start) / Double(CLOCKS_PER_SEC)

    // Oracle: post-parse disambiguation (rules from grammar annotations)
//    Oracle(parser: messageParser, input: input).disambiguate()

    // Ambiguity-harvest driver (opt-in via APUS_SIG_DUMP=1). Runs the Oracle +
    // AST build and emits one canonical signature line per residual ambiguity:
    //   SIG <TAB> <messageIndex> <TAB> node <TAB> message <TAB> signature
    // The Phase-1 harvester (harvest_ambiguity.py) feeds all failing snippets as
    // `^^^` messages, runs this, and clusters the SIG lines into the signature table.
    if ProcessInfo.processInfo.environment["APUS_SIG_DUMP"] == "1" {
        Oracle(parser: messageParser, input: input).disambiguate()
        let sigBuilder = DerivationBuilder(parser: messageParser, input: input)
        _ = sigBuilder.buildAST()
        for d in sigBuilder.diagnostics {
            print("SIG\t\(mi)\t\(d.fingerprint)")
        }
    }
    var stats = "cpuTime, descriptorCount, crf.count, sizeOfSets, yieldCount\n"
    stats += "\(cpuTime), \(messageParser.descriptorCount), \(messageParser.crf.count), \(GrammarNode.sizeofSets), \(messageParser.yieldCount)\n"
    Logger.ui.info("\(stats, privacy: .public)")
//    print("tokenPatterns:")
//    for tp in grammar.terminals {
//        print(tp.key, tp.value.source)
//    }

//    do {
//        var keywords: [String] = []
//        var macro: [String] = []
//        var punctuation: [String] = []
//        for (key, value) in grammar.terminals {
//            if value.isLiteral {
//                if let first = key.first, first.isLetter {
//                    keywords.append(key)
//                } else if let first = key.first, first == "#" {
//                    macro.append(key)
//                } else{
//                    punctuation.append(key)
//                }
//            }
//        }
//        for k in keywords.sorted() {
//            print("\"\(k)\" ", terminator: "")
//        }
//        print()
//        for m in macro.sorted() {
//            print("\"\(m)\" ", terminator: "")
//        }
//        print()
//        for p in punctuation.sorted() {
//            print("\"\(p)\" ", terminator: "")
//        }
//    }
//    print(cpuTime, messageParser.descriptorCount, messageParser.crf.count)

    // Sort elements (if BSR is Comparable) then join
    //    // Global BSR set removed; to inspect yields, iterate per grammar node.
    //    // Example: print total distributed-yield cardinality used by stats.
    //    // Logger.parse.debug("yieldCount = \(messageParser.yieldCount)")

//    do {
//        let apus = try String(contentsOf: grammarURL, encoding: .utf8)
//        let html = convertApusToHTML(apus)
//        let htmlURL = grammarURL
//            .deletingPathExtension()
//            .appendingPathExtension("html")
//        try html.write(to: htmlURL, atomically: true, encoding: .utf8)
//        print("✅ Successfully wrote \(htmlURL)")
//    } catch {
//        print("❌ Error: \(error)")
//    }

    
    let enableGrammarToMD = true
    if enableGrammarToMD {
        let input = try String(contentsOf: grammarURL, encoding: .utf8)
        let markDown = convertApusToMD(input, title: "Hello")
        var markdownURL = grammarURL
        markdownURL.deletePathExtension()
        markdownURL.appendPathExtension("md")
        try markDown.write(to: markdownURL, atomically: true, encoding: .utf8)
    }
    
    
    let generateParser = true
    if generateParser && grammar.nonTerminals.count < 1000 && messageParser.crf.count < 1000 {
        let parserFile = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .appendingPathComponent("ApusApus-generated")
            .appendingPathComponent(grammar.startSymbol + "_parser")
            .appendingPathExtension("swift")
        var info = "LL1 is \(grammar.isLL1)\n"
        if grammar.isLL1 {
            let parserGenerator = ParserGenerator(outputFile: parserFile, grammar: grammar)
            try parserGenerator.generate()
            info += "LL1 recursive descent parser written to \(parserFile.lastPathComponent)\n"
        }
        Logger.ui.info("\(info, privacy: .public)")
    }

}
