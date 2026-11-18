//
//  HandMatcherTests.swift
//  ApusApusTests
//
//  The hand-written matchers in `ApusRegexLibrary.matchers` replace their regexes in the lexer
//  for speed (see the comment above `ApusRegexLibrary.matchers`). The regexes stay the specification: this suite checks
//  that every matcher gives the same end as its regex at every scalar position of a corpus.
//

import Testing
import Foundation

@Suite("Hand-written matchers agree with their regexes")
struct HandMatcherTests {

    /// Cases where the operator rules interact (comment openers, `*/`, `->`, specials, dots) and
    /// the Unicode edges of the identifier and operator classes.
    static let tricky = """
        a+b a+=b x!!y x?.y a->b a-->b a->>b -> ->// x*//c x*/ */ a*/b */*/ **/ a /*c*/ b ... ..< .?.
        .? .! .?? .x =/0/ ^^/re/ ==/ !== &&& &= ?? ??= !x ?x = ! ? & .. . ./ ./* .// .*/ +*/ +*/* +*//
        /= //x /*x $0 $12 $a $1a2 $$ $_ $é #if #sourceLocation #_ #é #1 _ _a a$b `x` ünïcødé é\u{301}x
        𝑥 Ⅻ ⚽ ⚽️ \u{F8FF}x \u{F900} x\u{180E}y →← ∑x √2 ※ ⁂ 〈x〉 〡〢 ⁀x ⁔ x\u{200D}y \u{FE0F}
        \u{E0100} a\u{0300} +\u{0300} .\u{20D0} -> ->-
        """

    /// The tricky cases plus real Swift: the lexer and parser sources (operators, comments, `#`,
    /// `$`, Unicode in doc comments).
    static func corpus() throws -> [String] {
        var texts = [tricky]
        for file in ["Lexer.swift", "MessageParser.swift", "SwiftGrammarRegexLibrary.swift", "Grammar.swift"] {
            let url = testSourceDirectory().appendingPathComponent(file)
            texts.append(try String(contentsOf: url, encoding: .utf8))
        }
        return texts
    }

    static let keys = ApusRegexLibrary.matchers.keys.sorted()

    @Test(arguments: keys)
    func matcherAgreesWithRegex(key: String) throws {
        let matcher = try #require(ApusRegexLibrary.matchers[key])
        let regex = try #require(ApusRegexLibrary.patterns[key], "matcher \(key) has no regex")
        var disagreements: [String] = []
        for text in try Self.corpus() {
            let input = MatcherInput(text)
            let scalars = text.unicodeScalars
            var i = scalars.startIndex
            while i < scalars.endIndex {
                let start = text.position(of: i)
                let expected = text[i...].prefixMatch(of: regex).map { text.position(of: $0.range.upperBound) }.flatMap { $0 > start ? $0 : nil }
                let actual = matcher(input, start)
                if expected != actual, disagreements.count < 10 {
                    func length(_ end: CharPosition?) -> String { end.map { "\($0 - start) bytes" } ?? "no match" }
                    let context = String(scalars[i...].prefix(12)).debugDescription
                    disagreements.append("at \(context): regex \(length(expected)), matcher \(length(actual))")
                }
                scalars.formIndex(after: &i)
            }
        }
        #expect(disagreements.isEmpty, "\(key) disagrees with its regex:\n\(disagreements.joined(separator: "\n"))")
    }
}
