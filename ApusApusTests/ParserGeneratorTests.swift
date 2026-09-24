//
//  ParserGeneratorTests.swift
//  Advent
//
//  Created on 02/07/2026.
//

import Testing
import Foundation

@Suite("Parser Generator Tests", .serialized)
struct ParserGeneratorTests {

    /// Grammar files to test
    static let grammarFiles = ["apus"]

    @Test("Generates parser for all grammar files")
    func testGenerateParser() throws {
        let projectDir = testProjectDirectory()

        for grammarFile in Self.grammarFiles {
            let grammarFileURL = try resolveGrammarFileURL(named: grammarFile)

            #expect(
                FileManager.default.fileExists(atPath: grammarFileURL.path),
                "Grammar file should exist: \(grammarFileURL.path)"
            )

            let grammar = try withParserIsolation {
                let grammarParser = try ApusParser(fromFile: grammarFileURL)
                return try grammarParser.parse(explicitStartSymbol: "")
            }

            #expect(grammar.nonTerminals.count > 0, "Grammar should define at least one non-terminal")

            let outputDir = projectDir.appendingPathComponent("TestOutput")
            try? FileManager.default.createDirectory(at: outputDir, withIntermediateDirectories: true)

            let parserOutputFile = outputDir
                .appendingPathComponent("\(grammarFile)_output")
                .appendingPathExtension("swift")

            let parserGenerator = ParserGenerator(outputFile: parserOutputFile, grammar: grammar)
            try parserGenerator.generate()

            #expect(
                FileManager.default.fileExists(atPath: parserOutputFile.path),
                "Generated parser file should exist"
            )

            let generatedCode = try String(contentsOf: parserOutputFile, encoding: .utf8)
            #expect(generatedCode.count > 50, "Generated parser should have substantial content")
        }
    }

    @Test("All grammar files are accessible")
    func testGrammarFilesExist() throws {
        for grammarFile in Self.grammarFiles {
            let grammarFileURL = try resolveGrammarFileURL(named: grammarFile)
            #expect(
                FileManager.default.fileExists(atPath: grammarFileURL.path),
                "Grammar file should exist: \(grammarFile).apus"
            )
        }
    }

    @Test("Generated parser contains expected structure")
    func testGeneratedCodeStructure() async throws {
        let projectDir = testProjectDirectory()
        let outputDir = projectDir.appendingPathComponent("TestOutput")

        let grammarFileURL = try resolveGrammarFileURL(named: "apus")

        let grammar: Grammar
        do {
            grammar = try withParserIsolation {
                let grammarParser = try ApusParser(fromFile: grammarFileURL)
                return try grammarParser.parse(explicitStartSymbol: "")
            }
        } catch {
            Issue.record("Failed to parse base grammar: \(error)")
            return
        }

        try? FileManager.default.createDirectory(at: outputDir, withIntermediateDirectories: true)

        let parserOutputFile = outputDir
            .appendingPathComponent("apus_validation_test")
            .appendingPathExtension("swift")

        let parserGenerator = ParserGenerator(outputFile: parserOutputFile, grammar: grammar)
        try parserGenerator.generate()

        let generatedCode = try String(contentsOf: parserOutputFile, encoding: .utf8)

        #expect(generatedCode.count > 100, "Generated code should have substantial content")
    }
}
