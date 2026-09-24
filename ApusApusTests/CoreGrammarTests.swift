//
//  CoreGrammarTests.swift
//  AdventTests
//
//  Core grammar parsing tests: literals, sequences, selection, EBNF brackets,
//  nonterminal indirection, recursion, ambiguity, named grammars, empty constructs,
//  regex terminals, and self-parsing.
//

import Testing
import Foundation

@Suite("Core Grammar Tests", .serialized)
struct CoreGrammarTests {

    // MARK: - Literals and Sequences

    @Suite("Literals and Sequences", .serialized)
    struct LiteralsAndSequences {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"S = "x"."#,
                pass: ["x"],
                fail: ["y", "xx", ""],
                label: "single literal"
            ),
            TestCase(
                grammar: #"S = "a" "b"."#,
                pass: ["ab"],
                fail: ["a", "ba", ""],
                label: "two-literal sequence"
            ),
            TestCase(
                grammar: #"S = "a" "b" "c" "d"."#,
                pass: ["abcd"],
                fail: ["abc", "abcde"],
                label: "four-literal sequence"
            ),
            TestCase(
                grammar: #"S = "a" ""."#,
                pass: ["a"],
                label: "literal then epsilon"
            ),
            TestCase(
                grammar: #"S = ""."#,
                pass: [""],
                fail: ["x"],
                label: "epsilon only"
            ),
            TestCase(
                grammar: #"S = "" "" "x"."#,
                pass: ["x"],
                label: "epsilon epsilon literal"
            ),
            TestCase(
                grammar: #"S = "x" "x"."#,
                pass: ["xx"],
                fail: ["x", "xxx"],
                label: "repeated literal sequence"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Selection (Alternation)

    @Suite("Selection", .serialized)
    struct Selection {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"S = "a" | "b"."#,
                pass: ["a", "b"],
                fail: ["c", "ab", ""],
                label: "simple alternation"
            ),
            TestCase(
                grammar: #"S = "x" | "x"."#,
                pass: ["x"],
                fail: ["y"],
                label: "ambiguous alternation"
            ),
            TestCase(
                grammar: #"S = "a" | "b". S = "c"."#,
                pass: ["a", "b", "c"],
                fail: ["d"],
                label: "decomposed selection"
            ),
            TestCase(
                grammar: #"S = "a" | "c" "d"."#,
                pass: ["a", "cd"],
                fail: ["c", "d"],
                label: "alternation different lengths"
            ),
            TestCase(
                grammar: #"S = ("a" | "b") | "c"."#,
                pass: ["a", "b", "c"],
                fail: ["d"],
                label: "nested alternation"
            ),
            TestCase(
                grammar: #"S = "x" | ""."#,
                pass: ["x", ""],
                label: "literal or empty"
            ),
            TestCase(
                grammar: #"S = "" | "b"."#,
                pass: ["", "b"],
                label: "empty or literal"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - EBNF Brackets (Groups, Options, Closures)

    @Suite("EBNF Brackets", .serialized)
    struct EBNFBrackets {
        static let cases: [TestCase] = [
            // Groups
            TestCase(grammar: #"S = ("a")."#, pass: ["a"], fail: ["b", ""], label: "group"),
            TestCase(grammar: #"S = ((("a")))."#, pass: ["a"], label: "nested groups"),
            TestCase(grammar: #"S = "x" ("x" | "x") "x"."#, pass: ["xxx"], label: "group in sequence"),
            TestCase(grammar: #"S = ("x" | "x") "x"."#, pass: ["xx"], label: "group leading"),
            TestCase(grammar: #"S = "x" ("x" | "x")."#, pass: ["xx"], label: "group trailing"),
            TestCase(grammar: #"S = ( "a" "b" | "a" "b" ) "c"."#, pass: ["abc"], label: "ambiguous group"),

            // Options
            TestCase(grammar: #"S = ["x"]."#, pass: ["x", ""], fail: ["xx"], label: "option"),
            TestCase(grammar: #"S = [["a"]]."#, pass: ["a", ""], label: "nested option"),
            TestCase(grammar: #"S = ["x"] "a"."#, pass: ["xa", "a"], label: "option then literal"),
            TestCase(grammar: #"S = "x" ["x"]."#, pass: ["x", "xx"], label: "literal then option"),
            TestCase(grammar: #"S = ["x"] "x"."#, pass: ["x", "xx"], label: "option then same literal"),
            TestCase(
                grammar: #"S = ["a"] ["b"] ["c"]."#,
                pass: ["abc", "ab", "ac", "bc", "a", "b", "c", ""],
                label: "three options"
            ),
            TestCase(
                grammar: #"S = ["a" | "b"] ["c"]."#,
                pass: ["a", "b", "c", "ac", "bc", ""],
                label: "option with alternation"
            ),

            // Kleene closure
            TestCase(grammar: #"S = {"x"}."#, pass: ["", "x", "xx", "xxx"], label: "kleene closure"),
            TestCase(grammar: #"S = "x" {"x"}."#, pass: ["x", "xx", "xxx"], fail: [""], label: "literal then closure"),
            TestCase(grammar: #"S = {"x"} "x"."#, pass: ["x", "xx", "xxx"], fail: [""], label: "closure then literal"),
            TestCase(grammar: #"S = {{"x"}}."#, pass: ["", "x", "xx"], label: "nested closure"),
            TestCase(grammar: #"S = {{"x"}} "a"."#, pass: ["a", "xa", "xxa"], label: "nested closure then literal"),
            TestCase(grammar: #"S = {"x"} {"x"}."#, pass: ["", "x", "xx", "xxx"], label: "two closures ambiguous"),
            TestCase(grammar: #"S = "a" {"x"} "c"."#, pass: ["ac", "axc", "axxc"], label: "closure in sequence"),
            TestCase(grammar: #"S = { "a" } "b"."#, pass: ["b", "ab", "aab"], label: "closure halt"),
            TestCase(
                grammar: #"S = {"a"} "x" {"b" | "c"}."#,
                pass: ["x", "ax", "xb", "xc", "axbc"],
                label: "two closures with alternation"
            ),

            // Positive closure
            TestCase(grammar: #"S = <"x">."#, pass: ["x", "xx", "xxx"], fail: [""], label: "positive closure"),
            TestCase(grammar: #"S = <"x" | "x">."#, pass: ["x", "xx"], label: "positive closure ambiguous"),
            TestCase(grammar: #"S = <"x"> <"x">."#, pass: ["xx", "xxx"], label: "two positive closures"),
            TestCase(grammar: #"S = <"a"> "b"."#, pass: ["ab", "aab"], fail: ["b", ""], label: "positive closure halt"),

            // Bracket first/follow tests
            TestCase(grammar: #"S = "a" ("b") "c"."#, pass: ["abc"], label: "group first/follow"),
            TestCase(grammar: #"S = "a" ["b"] "c"."#, pass: ["abc", "ac"], label: "option first/follow"),
            TestCase(grammar: #"S = "a" {"b"} "c"."#, pass: ["ac", "abc", "abbc"], label: "closure first/follow"),
            TestCase(grammar: #"S = "a" <"b"> "c"."#, pass: ["abc", "abbc"], fail: ["ac"], label: "positive closure first/follow"),

            // Bracket sequences (fifo tests)
            TestCase(grammar: #"S = ["a" "b"]."#, pass: ["ab", ""], fail: ["a"], label: "option sequence"),
            TestCase(grammar: #"S = {"a" "b"}."#, pass: ["", "ab", "abab"], fail: ["a"], label: "closure sequence"),
            TestCase(grammar: #"S = <"a" "b">."#, pass: ["ab", "abab"], fail: ["", "a"], label: "positive closure sequence"),
            TestCase(grammar: #"S = {"a" ["b"]}."#, pass: ["", "a", "ab", "aab", "abab"], label: "closure with optional tail"),

            // Nullable bracket bodies
            TestCase(grammar: #"S = { "x" | "" }."#, pass: ["", "x", "xx"], label: "kleene with nullable body"),
            TestCase(grammar: #"S = < "x" | "" >."#, pass: ["x", "xx", ""], label: "positive closure with nullable body"),

            // Nullable bracket sequences
            TestCase(grammar: #"S = ("a") ("b") ("c")."#, pass: ["abc"], label: "group sequence"),
            TestCase(grammar: #"S = {"a"} {"b"} {"c"}."#, pass: ["", "a", "b", "c", "abc"], label: "closure sequence nullable"),
            TestCase(
                grammar: #"S = <"a"> <"b"> <"c">."#,
                pass: ["abc", "aabbc"],
                fail: ["", "ab", "ac", "bc"],
                label: "positive closure sequence"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Nonterminal Indirection

    @Suite("Indirection", .serialized)
    struct Indirection {
        static let cases: [TestCase] = [
            TestCase(grammar: #"S = N. N = "a"."#, pass: ["a"], fail: ["b"], label: "simple indirection"),
            TestCase(grammar: #"S = N. N = ["a"]."#, pass: ["", "a"], label: "nullable option indirection"),
            TestCase(grammar: #"S = N. N = {"a"}."#, pass: ["", "a", "aaa"], label: "nullable closure indirection"),
            TestCase(grammar: #"S = "a" N. N = ["a"]."#, pass: ["a", "aa"], label: "nullable leading"),
            TestCase(grammar: #"S = N "a". N = ["a"]."#, pass: ["a", "aa"], label: "nullable trailing"),
            TestCase(grammar: #"S = N N. N = "a"."#, pass: ["aa"], label: "shared nonterminal"),
            TestCase(grammar: #"S = N | N. N = "a"."#, pass: ["a"], label: "shared selection"),
            TestCase(grammar: #"S = N | N. N = ["a"]."#, pass: ["", "a"], label: "shared nullable selection"),
            TestCase(grammar: #"S = N "a" | N "a". N = "a"."#, pass: ["aa"], label: "shared tail"),
            TestCase(grammar: #"S = "a" N | "a" N. N = "a"."#, pass: ["aa"], label: "shared head"),
            TestCase(grammar: #"S = A B. A = "a". B = "b"."#, pass: ["ab"], label: "two nonterminals"),
            TestCase(grammar: #"S = X X X. X = "x"."#, pass: ["xxx"], label: "three shared nonterminals"),
            TestCase(grammar: #"S = "x" X "x" | "x" X "x". X = "x"."#, pass: ["xxx"], label: "ambiguous wrapped nonterminal"),
            TestCase(grammar: #"S = ( ["x"] | ["x"] ) "x"."#, pass: ["x", "xx"], label: "ambiguous optional in group"),
            TestCase(
                grammar: #"S = A "b" | A "c". A = ["a"]."#,
                pass: ["b", "c", "ab", "ac"],
                label: "nullable nonterminal selection"
            ),
            TestCase(
                grammar: #"S = A "b" | A "c". A = "a" | ""."#,
                pass: ["b", "c", "ab", "ac"],
                label: "nullable nonterminal alternation"
            ),
            TestCase(
                grammar: #"S = A "b" | A "c". A = "a"."#,
                pass: ["ab", "ac"],
                fail: ["b", "c"],
                label: "non-nullable nonterminal selection"
            ),
            TestCase(grammar: #"S = A B. A = ["a"]. B = ["b"]."#, pass: ["", "a", "b", "ab"], label: "two nullable nonterminals"),
            TestCase(grammar: #"S = X "a" | X "b". X = "x"."#, pass: ["xa", "xb"], label: "nonterminal instance different follow"),
            TestCase(grammar: #"S = X. X = "x"."#, pass: ["x"], label: "simple nonterminal"),
            TestCase(grammar: #"S = A. A = "a" | "b" | "c"."#, pass: ["a", "b", "c"], fail: ["d"], label: "nonterminal with three alternates"),
            TestCase(grammar: #"S = { "a" {"b"} "c" }."#, pass: ["", "ac", "abc", "abbc", "acabc"], label: "nested closure in closure"),
            TestCase(grammar: #"S = { "a" B "c" }. B = { "b" }."#, pass: ["", "ac", "abc", "abbc", "acabc"], label: "nonterminal closure in closure"),
            TestCase(grammar: #"S = { "x" X "x" }. X = { "x" }."#, pass: ["", "xx", "xxx", "xxxx"], label: "ambiguous nested closures"),
            TestCase(grammar: #"S = T "t". T = "a" | "b" | "c"."#, pass: ["at", "bt", "ct"], fail: ["t", "dt"], label: "nonterminal prefix"),
            TestCase(grammar: #"S = { T ["a"] }. T = "t"."#, pass: ["", "t", "ta", "tta", "tata"], label: "closure with nullable tail nonterminal"),
            TestCase(grammar: #"S = T "a" T "b". T = ["t"]."#, pass: ["ab", "tab", "atb", "tatb"], label: "nonterminal follow gathering"),
            TestCase(
                grammar: #"S = A B C. A = "a" | "". B = "b" | "". C = "c" | ""."#,
                pass: ["", "a", "b", "c", "ab", "ac", "bc", "abc"],
                label: "three nullable nonterminals"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Recursion

    @Suite("Recursion", .serialized)
    struct Recursion {
        static let cases: [TestCase] = [
            TestCase(grammar: #"S = "x" | "x" S."#, pass: ["x", "xx", "xxx"], label: "right recursion"),
            TestCase(grammar: #"S = "x" S | "x"."#, pass: ["x", "xx", "xxx"], label: "right recursion reversed"),
            TestCase(grammar: #"S = "x" | S "x"."#, pass: ["x", "xx", "xxx"], label: "left recursion"),
            TestCase(grammar: #"S = S "x" | "x"."#, pass: ["x", "xx", "xxx"], label: "left recursion reversed"),
            TestCase(grammar: #"S = S "x" | ""."#, pass: ["", "x", "xx"], label: "left recursion nullable"),
            TestCase(grammar: #"S = "x" S | ""."#, pass: ["", "x", "xx"], label: "right recursion nullable"),
            TestCase(grammar: #"S = "x" [S]."#, pass: ["x", "xx", "xxx"], fail: [""], label: "right recursion optional"),
            TestCase(grammar: #"S = ["x" S]."#, pass: ["", "x", "xx"], label: "right recursion zero optional"),
            TestCase(grammar: #"S = [S "x"]."#, pass: ["", "x", "xx"], label: "left recursion zero optional"),
            TestCase(
                grammar: #"S = "a" S "a" | "a"."#,
                pass: ["a", "aaa", "aaaaa"],
                fail: ["aa", "aaaa"],
                label: "odd brackets"
            ),
            TestCase(grammar: #"S = ["a" S "a"]."#, pass: ["", "aa", "aaaa"], fail: ["a", "aaa"], label: "even brackets"),
            TestCase(grammar: #"S = S "a" | S "b" | ""."#, pass: ["", "a", "b", "ab", "ba", "aab"], label: "left recursion two alts"),
            TestCase(
                grammar: #"S = A. A = "a" B | "c". B = "b" A | "d"."#,
                pass: ["c", "ad", "abc", "abad", "ababc"],
                fail: ["", "a", "b", "ab"],
                label: "mutual recursion"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Ambiguity

    @Suite("Ambiguity", .serialized)
    struct Ambiguity {
        static let cases: [TestCase] = [
            TestCase(grammar: #"S = ["a"] ["a"]."#, pass: ["", "a", "aa"], label: "ambiguous option sequence"),
            TestCase(grammar: #"S = {"a"} {"a"}."#, pass: ["", "a", "aa", "aaa"], label: "ambiguous closure sequence"),
            TestCase(grammar: #"S = <"a"> <"a">."#, pass: ["aa", "aaa"], fail: ["", "a"], label: "ambiguous positive closure sequence"),
            TestCase(grammar: #"S = ["a"] | ["a"]."#, pass: ["", "a"], label: "ambiguous nullable selection"),
            TestCase(grammar: #"S = "b" | S S."#, pass: ["b", "bb", "bbb"], label: "highly ambiguous (ART torture half)"),
            TestCase(grammar: #"S = "x" | S S | S S S."#, pass: ["x", "xx", "xxx"], label: "highly ambiguous (Binsbergen G3)"),
            TestCase(grammar: #"S = "x" | S S."#, pass: ["x", "xx", "xxx"], label: "Binsbergen G3 two-way"),
            TestCase(grammar: #"S = "x" | S S S."#, pass: ["x", "xxx"], fail: ["xx"], label: "Binsbergen G3 three-way"),
            TestCase(grammar: #"S = <<"a">>."#, pass: ["a", "aa"], fail: [""], label: "nested double positive closure"),
            TestCase(grammar: #"S = ["a"] | ["b"] | ["c"]."#, pass: ["", "a", "b", "c"], fail: ["d"], label: "nullable triple alternation"),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Named Grammars from Literature

    @Suite("Named Grammars", .serialized)
    struct NamedGrammars {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"S = "b" S | A S "d" | "". A = "a"."#,
                pass: ["", "b", "ad", "aadd", "bad", "baadd"],
                label: "Cappers thesis G3"
            ),
            TestCase(
                grammar: #"S = "a" S | "a" S "d" | ""."#,
                pass: ["", "a", "aad", "aa"],
                label: "Cappers thesis G5"
            ),
            TestCase(
                grammar: #"S = "a" S "b" | "a" S "c" | "a"."#,
                pass: ["a", "aab", "aac"],
                fail: ["", "ab"],
                label: "Alfroozeh G0"
            ),
            TestCase(
                grammar: #"S = "a" | S "b" | S ["b"] C. C = "c"."#,
                pass: ["a", "ab", "ac", "abc", "abb"],
                label: "Alfroozeh Hunt"
            ),
            TestCase(
                grammar: #"S = "a" A B | "a" A "b". A = "a" | "c" | "". B = "b" | B "c" | ""."#,
                pass: ["aab"],
                label: "Binsbergen G1"
            ),
            TestCase(
                grammar: #"S = A C "a" B | A B "a" "a". A = "a" A | "a". B = "b" B | "b". C = "b" C | "c"."#,
                pass: ["aabbaa"],
                label: "Binsbergen G2"
            ),
            TestCase(grammar: #"S = "a" B "c" | "a" B "c". B = "b"."#, pass: ["abc"], label: "ambiguous shared prefix nonterminal"),
            TestCase(
                grammar: #"S = "a" ("a" "b" | "a") ("b" "c" | "c")."#,
                pass: ["aabc", "aac"],
                label: "Scott & Johnstone EBNF two derivations"
            ),
            TestCase(
                grammar: #"S = "b" S93 | "a" S93 "c" | "". S93 = "b" S93 | "a" S93 "c" | ""."#,
                pass: ["", "b", "ac", "aacc", "aaaccc"],
                fail: ["aac"],
                label: "matched brackets Cappers G3 (recursive)"
            ),
            TestCase(
                grammar: #"S = "a" S | "a" S "c" | ""."#,
                pass: ["", "a", "aac"],
                label: "ambiguous brackets Cappers G5 (recursive)"
            ),
            TestCase(grammar: #"S = ( ("a" | "a") | "a" ) | "a"."#, pass: ["a"], label: "deeply nested ambiguous alternation"),
            TestCase(grammar: #"S = ((("a") "a") "a") "a"."#, pass: ["aaaa"], label: "deeply nested groups"),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Empty Constructs

    @Suite("Empty Constructs", .serialized)
    struct EmptyConstructs {
        static let cases: [TestCase] = [
            TestCase(grammar: #""#, illegalGrammar: true, label: "empty grammar"),
            TestCase(grammar: #"."#, illegalGrammar: true, label: "no rule"),
            TestCase(grammar: #"S = ."#, illegalGrammar: true, label: "empty sequence"),
            TestCase(grammar: #"S = |."#, illegalGrammar: true, label: "empty selection"),
            TestCase(grammar: #"S = ()."#, illegalGrammar: true, label: "empty group"),
            TestCase(grammar: #"S = []."#, illegalGrammar: true, label: "empty option"),
            TestCase(grammar: #"S = {}."#, illegalGrammar: true, label: "empty closure"),
            TestCase(grammar: #"S = <>."#, illegalGrammar: true, label: "empty positive closure"),
            TestCase(grammar: #"S = N."#, illegalGrammar: true, label: "undefined production rule"),
            TestCase(grammar: #"S = "a" ""."#, pass: ["a"], label: "epsilon before end-of-string"),
            TestCase(
                grammar: #"S = "x". S = "xx". S = "xxx"."#,
                pass: ["x", "xx", "xxx"],
                fail: ["", "xxxx"],
                label: "multiple definitions"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Regex Terminals

    @Suite("Regex", .serialized)
    struct Regex {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"S = "a" /u+/ "b"."#,
                pass: ["aub", "auub", "auuub"],
                fail: ["ab"],
                label: "inline regex"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Token kinds
    //
    // One naming rule for both terminal shapes: a NAMED terminal (`-`/`:`) takes its kind
    // from the LHS; an ANONYMOUS inline terminal takes its own pattern INCLUDING delimiters
    // (`"…"` / `/…/`). Named literals used to be the exception — they registered the quoted
    // form as the kind and filed the LHS in a `literalAliases` side table, so the name never
    // became a kind. No grammar in the repo exercised that path, hence these tests.

    @Suite("Token kinds", .serialized)
    struct TokenKinds {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"fBrace - "{" . S = fBrace "x"."#,
                pass: ["{x", "{ x"],
                fail: ["x", "{"],
                label: "named literal terminal is referenceable"
            ),
            TestCase(
                // Named and anonymous never merge, so the same text can carry two kinds on
                // purpose — the `regexOpenSlash`/`regexCloseSlash` pattern in Swift.apus.
                grammar: #"fBrace - "{" . S = fBrace "{"."#,
                pass: ["{{", "{ {"],
                fail: ["{"],
                label: "named literal and anonymous literal coexist"
            ),
            TestCase(
                grammar: #"openTick - "`" . closeTick - "`" . S = openTick /[a-z]+/ closeTick."#,
                pass: ["`ab`"],
                fail: ["`ab", "ab`"],
                label: "two named literals over one character"
            ),
            TestCase(
                // Anonymous regexes sharing a pattern share one kind (content-naming); they
                // used to get distinct position-derived names for identical patterns.
                grammar: #"S = /u+/ "-" /u+/."#,
                pass: ["u-u", "uu-uuu"],
                fail: ["u-", "-u"],
                label: "repeated anonymous regex"
            ),
            TestCase(
                grammar: #"dash : "-" . S = "a" "b"."#,
                pass: ["ab", "a-b", "-ab", "a--b"],
                fail: ["ba"],
                label: "named literal as skipped trivia"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }

        @Test("named terminal's kind is its LHS, anonymous terminal's kind is its pattern")
        func kindNaming() throws {
            let grammar = try parseGrammar(#"fBrace - "{" . number - /[0-9]+/ . S = fBrace number "}" /x+/."#)

            #expect(grammar.terminals["fBrace"] != nil, "named literal should register its LHS as a kind")
            #expect(grammar.terminals["number"] != nil, "named regex should register its LHS as a kind")
            #expect(grammar.terminals[#""}""#] != nil, "anonymous literal's kind is its quoted pattern")
            #expect(grammar.terminals["/x+/"] != nil, "anonymous regex's kind is its delimited pattern")

            // The named literal does NOT also register the quoted form — that was the alias behaviour.
            #expect(grammar.terminals[#""{""#] == nil, "named literal should not register the quoted form")

            // `source` is the text the lexer matches: unescaped content for a literal,
            // the undelimited pattern for a regex.
            #expect(grammar.terminals["fBrace"]?.source == "{")
            #expect(grammar.terminals["fBrace"]?.isLiteral == true)
            #expect(grammar.terminals["number"]?.isLiteral == false)
        }
    }

    // MARK: - Structured trivia non-terminal

    @Suite("TriviaNonTerminal", .serialized)
    struct TriviaNonTerminal {
        static let cases: [TestCase] = [
            TestCase(
                // Structured `nested : ...` is a trivia non-terminal: its recogniser runs as
                // a recursive sub-parse during skipTrivia. Nested `<…>` blocks
                // count as trivia and get consumed before matching `x`.
                grammar: #"nested : "<" { /[^<>]/ | nested } ">" . S = "x"."#,
                pass: ["x", "<>x", "<a>x", "<<a>>x", "<<<a>>>x", "<a><b>x"],
                fail: ["<x", "x<", "<a>"],
                label: "nested-bracket trivia via structured colon"
            ),
            TestCase(
                grammar: #"pair : /a/ /b/ . S = "x"."#,
                pass: ["x", "abx"],
                fail: ["ax", "bx"],
                label: "structured colon requires whole RHS to be one skipped recognizer"
            ),
        ]

        @Test(arguments: cases)
        func test(_ tc: TestCase) throws {
            try runTestCase(tc)
        }
    }

    // MARK: - Mixed layout scopes

    @Suite("MixedLayoutScopes", .serialized)
    struct MixedLayoutScopes {
        static let cases: [TestCase] = [
            TestCase(
                grammar: #"island - "a" "b" "c" . S = island ."#,
                pass: ["abc"],
                fail: ["a bc", "ab c", "a b c", "a b c extra"],
                label: "structured dash lexical island preserves trivia"
            ),
            TestCase(
                // Structured `-` is a visible lexical island: ordinary terminals preserve
                // trivia, but entering an `=` payload still gives the payload normal Swift-like
                // trivia skipping before `id` and `)`.
                grammar: #"island - "a" payload "c" . S = island . payload = "b" ."#,
                pass: ["abc", "a bc"],
                fail: ["ab c", "a b c"],
                label: "equals callee inside lexical island skips only within callee"
            ),
            TestCase(
                grammar: #"S = island . island - "a" "b" "c" ."#,
                illegalGrammar: true,
                label: "structured dash terminal must be defined before use"
            ),
            TestCase(
                // Miniature interpolation shape. The interpolation close lives inside the `=`
                // payload so Swift-style trivia before `)` is skipped there. After `)` the
                // structured `-` island resumes immediately, so spaces before `tail` are content.
                grammar: #"""
                    quote - /"/ .
                    stringText - /[^"\\]+/ .
                    id - /[A-Za-z_][A-Za-z_0-9]*/ .
                    stringIsland - quote { stringText | interpolation } quote .
                    S = stringIsland .
                    interpolation = /\\\(/ payload .
                    payload = id ")" .
                    """#,
                pass: [
                    #""hello""#,
                    #""hello \(name) tail""#,
                    #""hello \( name ) tail""#,
                    #""hello \( name )tail ""#,
                    #""hello \( name )   tail""#,
                ],
                fail: [
                    #""hello \( name tail""#,
                    #""hello \( name ) tail" extra"#,
                ],
                label: "mini string interpolation over current lexical island mixed-scope behavior"
            ),
        ]

        @Test(arguments: cases)
        func currentBehavior(_ tc: TestCase) throws {
            try runTestCase(tc)
        }

        @Test("structured dash body terminals suppress leading trivia")
        func structuredDashMarksBodyTerminals() throws {
            let parser = try ApusParser(fromString: #"whitespace : /\s+/. island - "a" "b" "c" . S = island ."#)
            let grammar = try parser.parse()
            guard let island = grammar.nonTerminals["island"] else {
                Issue.record("missing island nonterminal")
                return
            }
            let body = island.alt?.bodySymbols ?? []
            let bodyNames = body.map(\.name)
            let allSuppressLeadingTrivia = body.allSatisfy { $0.suppressesLeadingTrivia }
            #expect(bodyNames == [#""a""#, #""b""#, #""c""#])
            #expect(allSuppressLeadingTrivia)
        }
    }

    // MARK: - Oracle Disambiguation
    //
    // Moved to `OracleDisambiguationTests.swift` (suite `Oracle Disambiguation`),
    // where the top-level pragma tests are extracted alongside the new
    // nested-cluster tests. See `Oracle Disambiguation Unification.md`.

    // MARK: - Self-parsing (APUS grammar)

    @Suite("Self-parsing", .serialized)
    struct SelfParsing {

        @Test("APUS grammar parses itself")
        func apusSelfParse() throws {
            let grammar = try loadGrammarFile(named: "apus")
            #expect(grammar.nonTerminals.count > 0, "Should define nonterminals")
        }
    }
}
