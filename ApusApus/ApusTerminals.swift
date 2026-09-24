//
//  ApusTerminals.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.03.11.
//

import OSLog
import RegexBuilder

let apusTerminals: [String:TokenPattern] = [
    "whitespace":   TokenPattern(#"\s+"#,                   /\s+/,                              false, true),
    "linecomment":  TokenPattern(#"//.*"#,                  /\/\/.*/,                           false, true),
    "blockcomment": TokenPattern(#"/\*(?s).*?\*/"#,         /\/\*(?s).*?\*\//,                  false, true),
    "identifier":   TokenPattern(#"\p{XID_Start}\p{XID_Continue}*"#, /\p{XID_Start}\p{XID_Continue}*/,   false, false),
    "literal":      TokenPattern(#""(?:[^"\\]|\\.)+""#,     /\"(?:[^\"\\]|\\.)+\"/,             false, false),
    "regex":        TokenPattern(#"/(?!\*)(?:[^\/\\]|\\.)+/"#,    /\/(?!\*)(?:[^\/\\]|\\.)+\//,             false, false),
    "action":       TokenPattern(#"'(?:[^'\\]|\\.)*'"#,     /'(?:[^'\\]|\\.)*'/,                false, true),
    "message":      TokenPattern(#"\^\^\^(?:(?s).*?)(?=\^\^\^|$)"#,
                                                /\^\^\^(?:(?s).*?)(?=\^\^\^|$)/,    false, false),
    "pragma":       TokenPattern(#"@\p{XID_Start}\p{XID_Continue}*"#, /@\p{XID_Start}\p{XID_Continue}*/, false, false),

    "empty":        TokenPattern("\"\"",                    Regex { "\"\"" },                   true,  false),
    "epsilon":      TokenPattern("ε",                       Regex { "ε" },                      true,  false),

    ".":            TokenPattern(".",                       Regex { "." },                      true,  false),
    ":":            TokenPattern(":",                       Regex { ":" },                      true,  false),
    "=":            TokenPattern("=",                       Regex { "=" },                      true,  false),
    "-":            TokenPattern("-",                       Regex { "-" },                      true,  false),
    "|":            TokenPattern("|",                       Regex { "|" },                      true,  false),
    "(":            TokenPattern("(",                       Regex { "(" },                      true,  false),
    ")":            TokenPattern(")",                       Regex { ")" },                      true,  false),
    "[":            TokenPattern("[",                       Regex { "[" },                      true,  false),
    "]":            TokenPattern("]",                       Regex { "]" },                      true,  false),
    "{":            TokenPattern("{",                       Regex { "{" },                      true,  false),
    "}":            TokenPattern("}",                       Regex { "}" },                      true,  false),
    "<":            TokenPattern("<",                       Regex { "<" },                      true,  false),
    ">":            TokenPattern(">",                       Regex { ">" },                      true,  false),
    "?":            TokenPattern("?",                       Regex { "?" },                      true,  false),
    "*":            TokenPattern("*",                       Regex { "*" },                      true,  false),
    "+":            TokenPattern("+",                       Regex { "+" },                      true,  false),
    "---":          TokenPattern("---",                     Regex { "---" },                    true,  false),
    ">>|":          TokenPattern(">>|",                     Regex { ">>|" },                    true,  false),
    "|<<":          TokenPattern("|<<",                     Regex { "|<<" },                    true,  false),
    // Directional-polarity lookahead/lookbehind annotations (unified scheme):
    //   >…>  forward (lookahead)   <…<  backward (lookbehind)   middle +/- = polarity.
    // Single-token distance only (the earlier `…2` two-token variants were dropped, unused).
    ">+>":          TokenPattern(">+>",                     Regex { ">+>" },                    true,  false),   // positive lookahead:  next token MUST be in set
    ">->":          TokenPattern(">->",                     Regex { ">->" },                    true,  false),   // negative lookahead:  next token MUST NOT be in set
    "<+<":          TokenPattern("<+<",                     Regex { "<+<" },                    true,  false),   // positive lookbehind: prev token MUST be in set
    "<-<":          TokenPattern("<-<",                     Regex { "<-<" },                    true,  false),   // negative lookbehind: prev token MUST NOT be in set
    ",":            TokenPattern(",",                       Regex { "," },                      true,  false),
    ">n<":          TokenPattern(">n<",                     Regex { ">n<" },                    true,  false),
    ">s<":          TokenPattern(">s<",                     Regex { ">s<" },                    true,  false),
    "<n>":          TokenPattern("<n>",                     Regex { "<n>" },                    true,  false),
    "<s>":          TokenPattern("<s>",                     Regex { "<s>" },                    true,  false),
]





// alternative definitions using RegexBuilder
let whitespaceRegex = Regex {
    OneOrMore {
        .whitespace
    }
}
let linecommentRegex = Regex {
    "//"
    ZeroOrMore {
        .anyNonNewline
    }
}
let blockcommentRegex = Regex {
    "/*"
    ZeroOrMore(.reluctant) {
        .any
    }
    "*/"
}
// recommended identifier syntax following https://unicode.org/reports/tr31/
let identifierRegex = Regex {
    /\p{XID_Start}/
    ZeroOrMore {
        /\p{XID_Continue}/
    }
}
let literalRegex = Regex {
    "\""
    ZeroOrMore {
        ChoiceOf {
            // any character that is not a '"' or a backward slash '\'
            CharacterClass(.anyOf("\"\\").inverted)
            // a backward slash '\' followed by single character, to escape '"' or '\', but catches more than legal escapes
            /\\./
        }
    }
    "\""
}
let regexRegex = Regex {
    "/"
    ZeroOrMore {
        ChoiceOf {
            // any character that is not a forward slash '/' or a backward slash '\'
            CharacterClass(.anyOf("/\\").inverted)
            // a backward slash '\' followed by single character, to escape '/' or '\', but catches more than legal escapes
            /\\./
        }
    }
    "/"
}
let actionRegex = Regex {
    "@"
    ZeroOrMore {
        ChoiceOf {
            // any character that is not a '@' or a backward slash '\'
            CharacterClass(.anyOf("@\\").inverted)
            // a backward slash '\' followed by single character, to escape '@' or '\', but catches more than legal escapes
            /\\./
        }
    }
    "@"
}
let messageRegex = Regex {
    /\^\^\^/
    ZeroOrMore(.reluctant) {
        .any
    }
    Lookahead {
        ChoiceOf {
            /\^\^\^/
            Anchor.endOfSubject
        }
    }
}

enum TokenType: String, CustomStringConvertible, CaseIterable {
    case endOfString            = "○"    // BLACK CIRCLE U+25CF
    case epsilon                = "ε"
    case fullStop               = "."
    case colon                  = ":"
    case equalsSign             = "="
    case verticalLine           = "|"
    case leftParenthesis        = "("
    case rightParenthesis       = ")"
    case leftSquareBracket      = "["
    case rightSquareBracket     = "]"
    case leftCurlyBracket       = "{"
    case rightCurlyBracket      = "}"
    case lessThanSign           = "<"
    case greaterThanSign        = ">"
    case questionMark           = "?"
    case asterisk               = "*"
    case plusSign               = "+"
    case whitespace             = "whitespace"
    case linecomment            = "linecomment"
    case blockcomment           = "blockcomment"
    case identifier             = "identifier"
    case literal                = "literal"
    case regex                  = "regex"
    case action                 = "action"
    case message                = "message"
    
    var description: String {self.rawValue}
}

typealias TokenRegex = (kind: TokenType, regex: Regex<Substring>)  // legacy / unused — keep as Substring to avoid wrapping every literal in this list

let tokenRegexes: [TokenRegex] = [
    (.epsilon,                      /[εϵԐԑ𝛆𝛜𝜀𝜖𝜺𝝐𝝴𝞊𝞮𝟄]/ ),
    (.fullStop,                     Regex { "." } ),
    (.colon,                        Regex { ":" } ),
    (.equalsSign,                   Regex { "=" } ),
    (.verticalLine,                 Regex { "|" } ),
    (.leftParenthesis,              Regex { "(" } ),
    (.rightParenthesis,             Regex { ")" } ),
    (.leftSquareBracket,            Regex { "[" } ),
    (.rightSquareBracket,           Regex { "]" } ),
    (.leftCurlyBracket,             Regex { "{" } ),
    (.rightCurlyBracket,            Regex { "}" } ),
    (.lessThanSign,                 Regex { "<" } ),
    (.greaterThanSign,              Regex { ">" } ),
    (.questionMark,                 Regex { "?" } ),
    (.asterisk,                     Regex { "*" } ),
    (.plusSign,                     Regex { "+" } ),
    (.whitespace,                   whitespaceRegex ),
    (.linecomment,                  linecommentRegex ),
    (.blockcomment,                 blockcommentRegex ),
    (.identifier,                   identifierRegex ),
    (.literal,                      literalRegex ),
    (.regex,                        regexRegex ),
    (.action,                       actionRegex ),
    (.message,                      messageRegex ),
]
