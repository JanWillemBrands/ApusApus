//
//  LL1DetectionTests.swift
//  AdventTests
//
//  Tests that the LL(1) property detector correctly classifies grammars.
//

import Testing
import Foundation

@Suite("LL1 Detection", .serialized)
struct LL1DetectionTests {

    static let ll1Cases: [TestCase] = [
        TestCase(grammar: #"S = "a"."#, label: "single literal"),
        TestCase(grammar: #"S = "a" "b"."#, label: "two-literal sequence"),
        TestCase(grammar: #"S = ""."#, label: "epsilon only"),
        TestCase(grammar: #"S = "a" | "b"."#, label: "simple alternation"),
        TestCase(grammar: #"S = "a" | "b" | "c"."#, label: "three alternates"),
        TestCase(grammar: #"S = "a" | ""."#, label: "nullable alternate"),
        TestCase(grammar: #"S = "a" ["b"] "c"."#, label: "option disjoint"),
        TestCase(grammar: #"S = ["b"] "c"."#, label: "option then different literal"),
        TestCase(grammar: #"S = {"a"} "b"."#, label: "closure disjoint"),
        TestCase(grammar: #"S = <"a"> "b"."#, label: "positive closure disjoint"),
        TestCase(grammar: #"S = <"a">."#, label: "positive closure"),
        TestCase(grammar: #"S = ("a" | "b") "c"."#, label: "group disjoint alternates"),
        TestCase(grammar: #"S = ["a" | "b"] "c"."#, label: "option with alternation"),
        TestCase(grammar: #"S = A B. A = "a". B = "b"."#, label: "two nonterminals"),
        TestCase(grammar: #"S = A. A = "a" | "b"."#, label: "nonterminal chain"),
        TestCase(
            grammar: #"S = E. E = T {"+" T}. T = "(" E ")" | "num"."#,
            label: "right-recursive expressions"
        ),
        TestCase(
            grammar: ###"""
                statement = "if" "(" E ")" matched ["else" tail] | "other".
                matched = "if" "(" E ")" matched "else" matched | "other".
                tail = "if" "(" E ")" tail | "other".
                E = "e".
                """###,
            label: "dangling else resolved"
        ),
        TestCase(
            grammar: #"S = E SP. SP = "" | "+" S. E = "num" | "(" S ")"."#,
            label: "right-recursive sum primed"
        ),
        TestCase(
            grammar: #"S = E {"+" E}. E = "num" | "(" S ")"."#,
            label: "EBNF sum repetition"
        ),
        TestCase(
            grammar: ###"""
                Expr = Term {("+" | "-") Term}.
                Term = Factor {("*" | "/") Factor}.
                Factor = "num" | "(" Expr ")".
                """###,
            label: "layered precedence"
        ),
        TestCase(
            grammar: ###"""
                Prog = "{" Stmts "}".
                Stmts = Stmt Stmts | "".
                Stmt = "id" "=" Expr ";" | "if" "(" Expr ")" Stmt.
                Expr = "id" Etail.
                Etail = "+" Expr | "-" Expr | "".
                """###,
            label: "mini-language statements"
        ),
        TestCase(
            grammar: #"S = "IDENT" "(" ["IDENT" {"," "IDENT"}] ")"."#,
            label: "func call optional args"
        ),
        TestCase(
            grammar: ###"""
                Expr = Term {"+" Term}.
                Term = Factor {"*" Factor}.
                Factor = "INT" | "(" Expr ")".
                """###,
            label: "left-associative precedence"
        ),
        TestCase(
            grammar: ###"""
                integer = ["+" | "-"] digit {digit}.
                digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9".
                """###,
            label: "signed integer"
        ),
        TestCase(
            grammar: #"S = A B C. A = "a" | "". B = "b" | "". C = "c" | ""."#,
            label: "three nullable nonterminals"
        ),
        TestCase(grammar: #"S = {"a"} {"b"}."#, label: "two different closures nullable overlap"),
        TestCase(
            grammar: #"S = A "a". A = B D. B = "b" | "". D = "d" | ""."#,
            label: "multiple nullables disjoint"
        ),
        TestCase(
            grammar: ###"""
                S = intlist | intset.
                intlist = integer {"," integer}.
                intset = "{" [intlist] "}".
                integer = "num".
                """###,
            label: "list vs set"
        ),
        TestCase(grammar: #"r = "" | "A" r."#, label: "nullable recursive sequence"),
        TestCase(
            grammar: ###"""
                Expr   = Term {("+"|"-") Term}.
                Term   = Factor {("*"|"/") Factor}.
                Factor = "num" | "(" Expr ")" | "-" Factor.
                """###,
            label: "unary/binary minus overlap"
        ),
        TestCase(
            grammar: ###"""
                Expr = Term {BinOp Term} | UnOp Expr.
                Term = "num" | "(" Expr ")".
                BinOp = "+" | "-".
                UnOp = "-" | "+".
                """###,
            label: "unary/binary same-level conflict"
        ),
        TestCase(grammar: #"S = {"a"} "b" {"a"}."#, label: "sandwich repetitions"),
        TestCase(grammar: #"S = "(" S ")" S | ""."#, label: "balanced parens with nullable tail"),
        TestCase(
            grammar: #"S = A. A = "a" B | "c". B = "b" A | "d"."#,
            label: "mutual recursion LL(1)"
        ),
    ]

    static let nonLL1Cases: [TestCase] = [
        TestCase(grammar: #"S = "a" | "a"."#, label: "duplicate alternate"),
        TestCase(grammar: #"S = "a" "b" | "a" "c"."#, label: "shared prefix"),
        TestCase(grammar: #"S = "x" | S "x"."#, label: "left recursion"),
        TestCase(grammar: #"S = "x" | "x" S."#, label: "right recursion"),
        TestCase(grammar: #"S = A "b" | A "c". A = ["a"]."#, label: "nullable nonterminal selection"),
        TestCase(grammar: #"S = ["a"] "a"."#, label: "option then same literal"),
        TestCase(grammar: #"S = {"a"} "a"."#, label: "closure then same literal"),
        TestCase(grammar: #"S = {"a"} {"a"}."#, label: "two same closures"),
        TestCase(grammar: #"S = "b" | S S."#, label: "highly ambiguous (ART torture)"),
        TestCase(grammar: #"S = "x" | S S | S S S."#, label: "Binsbergen G3"),
        TestCase(
            grammar: ###"""
                S = A.
                A = B D A | "a".
                B = D | "b".
                D = "d" | "".
                """###,
            label: "nullable propagation"
        ),
        TestCase(
            grammar: ###"""
                S = "if" "(" E ")" S
                  | "if" "(" E ")" S "else" S
                  | "other".
                E = "e".
                """###,
            label: "dangling else"
        ),
        TestCase(
            grammar: ###"""
                statement = matched | unmatched.
                matched = "if" "(" E ")" matched "else" matched | "other".
                unmatched = "if" "(" E ")" statement
                         | "if" "(" E ")" matched "else" unmatched.
                E = "e".
                """###,
            label: "matched unmatched"
        ),
        TestCase(
            grammar: ###"""
                Stat = "if" Exp "then" Stat MoreIf.
                MoreIf = "else" Stat "end" | "".
                Exp = "e".
                """###,
            label: "if-then optional else"
        ),
        TestCase(grammar: #"List = List "," "item" | "item"."#, label: "left-recursive list"),
        TestCase(
            grammar: ###"""
                stmt = assign ";" | func_call ";".
                assign = "IDENT" "=" Expr.
                func_call = "IDENT" "(" arglist ")".
                Expr = "e".
                arglist = "a".
                """###,
            label: "assignment or call"
        ),
        TestCase(
            grammar: ###"""
                Expr = Expr Op Expr | "(" Expr ")" | "Number".
                Op = "+" | "*".
                """###,
            label: "natural left-recursive expr"
        ),
        TestCase(grammar: #"Expr = Expr "+" Expr | Expr "*" Expr | "INT"."#, label: "ambiguous operator"),
        TestCase(
            grammar: ###"""
                Expr = Expr "+" Term | Term.
                Term = Term "*" Factor | Factor.
                Factor = "INT" | "(" Expr ")".
                """###,
            label: "left-recursive precedence"
        ),
        TestCase(
            grammar: ###"""
                Stmt = "id" "=" Expr ";" | "id" "(" ArgList ")".
                Expr = "e".
                ArgList = "a".
                """###,
            label: "common prefix needs factoring"
        ),
        TestCase(
            grammar: ###"""
                digit = /[0-9]/.
                Float = Fract [Exp] [Suffix] | {digit} Exp [Suffix].
                Fract = {digit} "." <digit> | <digit> ".".
                Exp = "e" ["+" | "-"] <digit>.
                Suffix = "f" | "l".
                """###,
            label: "floating-point overlapping alternatives"
        ),
        TestCase(
            grammar: ###"""
                Expr = "(" Expr ")" ExprP | "Number".
                ExprP = Op Expr ExprP | "".
                Op = "+" | "*".
                """###,
            label: "left-recursion eliminated tail conflict"
        ),
        TestCase(
            grammar: #"S = A "z". A = B "y" | "x". B = S "w" | "v"."#,
            label: "indirect left recursion cycle"
        ),
        TestCase(grammar: #"S = A "b". A = "b" | ""."#, label: "tiny nullable prefix conflict"),
        TestCase(grammar: #"S = "a" S "a" | "b" | ""."#, label: "symmetric recursion conflict"),
        TestCase(
            grammar: #"S = "(" [E {"," E} [","]] ")" . E = "id"."#,
            label: "optional trailing comma"
        ),
    ]

    @Test("LL(1) grammars detected correctly", arguments: ll1Cases)
    func testLL1(_ tc: TestCase) throws {
        let grammar = try parseGrammar(tc.grammar)
        #expect(grammar.isLL1 == true, "\(tc.label): expected LL(1) for grammar: \(tc.grammar)")
    }

    @Test("Non-LL(1) grammars detected correctly", arguments: nonLL1Cases)
    func testNonLL1(_ tc: TestCase) throws {
        let grammar = try parseGrammar(tc.grammar)
        #expect(grammar.isLL1 == false, "\(tc.label): expected non-LL(1) for grammar: \(tc.grammar)")
    }

}
