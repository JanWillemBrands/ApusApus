//
//  LanguageGrammarTests.swift
//  AdventTests
//
//  Tests that load real .apus grammar files and parse their embedded ^^^ messages.
//  Each message is a separate parameterized test case.
//

import Testing
import Foundation

@Suite("Language Grammar Tests", .serialized)
struct LanguageGrammarTests {

    @Suite("Python Grammar", .serialized)
    struct PythonGrammar {
        static let fixtureResult = Result { try loadLanguageFixture("grammars/Python/Python") }

        @Test("fixture loads")
        func fixtureLoads() throws {
            let fixture = try Self.fixtureResult.get()
            #expect(!fixture.cases.isEmpty, "Python fixture has no messages")
        }

        @Test("parse messages sequentially")
        func parseMessagesSequentially() throws {
            let fixture = try Self.fixtureResult.get()
            for tc in fixture.cases {
                let matched = try parseLanguageMessage(fixture, message: tc.message)
                #expect(matched, "Message \(tc.index) failed: \(tc.message.prefix(60))")
            }
        }
    }

    @Suite("APUS Grammar", .serialized)
    struct APUSGrammar {
        static let fixtureResult = Result { try loadLanguageFixture("apus") }

        @Test("fixture loads")
        func fixtureLoads() throws {
            let fixture = try Self.fixtureResult.get()
            #expect(!fixture.cases.isEmpty, "APUS fixture has no messages")
        }

        @Test("parse messages sequentially")
        func parseMessagesSequentially() throws {
            let fixture = try Self.fixtureResult.get()
            for tc in fixture.cases {
                let matched = try parseLanguageMessage(fixture, message: tc.message)
                #expect(matched, "Message \(tc.index) failed: \(tc.message.prefix(60))")
            }
        }
    }

    @Suite("Swift Grammar", .serialized)
    struct SwiftGrammar {
        static let fixtureResult = Result { try loadLanguageFixture("Swift") }

        @Test("fixture loads")
        func fixtureLoads() throws {
            let fixture = try Self.fixtureResult.get()
            #expect(!fixture.cases.isEmpty, "Swift fixture has no messages")
        }

        @Test("parse messages sequentially")
        func parseMessagesSequentially() throws {
            let fixture = try Self.fixtureResult.get()
            for tc in fixture.cases {
                let matched = try parseLanguageMessage(fixture, message: tc.message)
                #expect(matched, "Message \(tc.index) failed: \(tc.message.prefix(60))")
            }
        }
    }
}
