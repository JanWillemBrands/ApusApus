# ApusApus

Swifty grammars.

### Grammars for Dummies

The formal grammar for the sentence `Mary has a little lamb.` can be written as:

    sentence = "Mary has a little lamb." 

The recurring spaces between the words can be separated

    space    = " "
    sentence = "Mary" space "has" space "a" space "little" space "lamb."

but we usualy care more about the words than the spaces between them, so let's make the spaces transparent.

    space    : " "
    sentence = "Mary" "has" "a" "little" "lamb."

To capture that Mary's brother John also has a litte lamb, we can write:

    space    : " "
    person   = "Mary" | "John"
    sentence =  person "has" "a" "little" "lamb."

In fact, many people have little lambs, and people's names are typically capitalized.

    space    : " "
    person   = '[A-Z][a-z]*'
    sentence = person "has" "a" "little" "lamb."

We could then generalize this into

    space    : " "
    person   = '[A-Z][a-z]*'
    word     = '"[a-z]+"'
    sentence = person { word } "."

but we'd loose a lot of meaning. First of all, nonsense sentences like `rock you wow.` are correct in this grammar. And a more subtle effect is that a space before a `.` is now also allowed.  So, the price of a more general grammar is that meaning is lost.  To bring it back we can make the grammar more specific and also annotate it with helpful instructions (and comments):

    space     : " "                // TODO: handle tabs and new lines
    person    = '[A-Z][a-z]+'
    word      = '"[a-z]+"'
    adjective = "little" | "red"
    noun      = "lamb" | "car"
    sentence  = person { word } 
                adjective
                noun               @ check that the adjective isn't "red" when the noun is "lamb" @
                "."                @ check that the preceding character isn't a space @

The sentence `Mary has a little lamb.` still matches this latest grammar version. And the grammar rules and annotations can be further enriched to enable automatic generation of a complete parser.


### A few Implementation Details

The prime job of a parser is to recognize valid sentences. It does so by matching the input text with items from the grammar, in the correct order. The texts `"lamb"` and `"little"` in the grammar will directly match those in `Mary has a little lamb.` but for the things between single quotes it's a bit more complicated. However

    number = '\d+'

is just a shorthand version of the grammar rule (except that our space rule would interfere again). 

    number = ( "0"|"1"|"2"|"3"|"4"|"5"|"6"|"7"|"8"|"9" ) { "0"|"1"|"2"|"3"|"4"|"5"|"6"|"7"|"8"|"9" }

so the parser fundamentally still matches pieces of the input text to the literal texts in the grammar. The shorthand notation is an example of a regular expression which can be efficienly implemented in a finite state machine. A scanner builds this FSM from all the texts that appear in the grammar.  For Mary's grammar the list is

    literal      " ", "little", "red", "lamb", "car", "."
    general      '[A-Z][a-z]+' , '"[a-z]+"'

A scanner will chop the input text into pieces that match one of the 8 patterns in the list (if multiple pattterns match the longest match is chosen).  The scanner offers these pieces, called tokens, to the parser as a tuple (type: String, image: String). The first element called `type` uniquely identifies each of the 8 patterns, the second element called `image` is the part of the input text that is the match for that token type.  The sentence `Mary has a little lamb.` is broken down into the following token list

    type: '[A-Z][a-z]+'     image: "Mary"
    type: " "               image: " "
    type: '"[a-z]+"'        image: "has"
    type: " "               image: " "
    type: '"[a-z]+"'        image: "a"
    type: " "               image: " "
    type: "little"          image: "little"
    type: " "               image: " "
    type: "lamb"            image: "lamb"
    type: "."               image: "."

A parser generator will gather all these patterns from the grammar. Traditionally these patterns are identified in code in an enumeration or by an integer index, but since these patterns are static strings we'll rely on the hashing mechanisms that Swift provides. The token type will be the input image including the single or double quote marks. This ensures that all token types will unique. 
The token type indexes a dictionary that stores the matching patterns and whether the pattern represents a literal and whether it is transparent.
```swift
    typealias TokenPattern = (pattern: String, isLiteral: Bool, isTransparent: Bool)
    let maryTokenPatterns: [String:TokenPattern] = [
        #"\" \""#:           (#" "#,             true,  true),    
        #"\"little\""#:      (#"little"#,        true,  false),    
        #"\"red\""#:         (#"red"#,           true,  false),    
        #"\"lamb\""#:        (#"lamb"#,          true,  false),    
        #"\"car\""#:         (#"car"#,           true,  false),    
        #"\".\""#:           (#"."#,             true,  false),    
        #"'[A-Z][a-z]+'"#:   (#"[A-Z][a-z]+"#,   false, false),
        #"'\"[a-z]+\"'"#:    (#"\"[a-z]+\""#,    false, false), ]
```

The grammar will be used to build an Abstract Syntax Tree with nodes that correspond to the usual EBNF constructs. 
```swift
    class Node {
        enum Kind {
            case SEQ(head: Node, tail: Node)
            case ALT(left: Node, right: Node)
            case OPT(inside: Node)
            case REP(inside: Node)
            case NTM(name: String, link: Node)
            case TRM(type: String)
        }
        var kind: Kind
        var first: Set<String>
        var follow: Set<String>
    }
```
The AST has leaf nodes TRM for terminals of the literal and general types and REF non-terminals.
The AST has a binary SEQ type for sequences and a binary ALT type for alternative.
The AST has a group type for the 1...1 0...1 0... 1... iterations corresponding to () [] {} <> or () ()? ()* ()+ notation.
The grammar rules are stored in a dictionary that maps rule names to the corresponding AST nodes. Vice versa, REF nodes in the AST store a name that can be used as an index in the dictionary. With numbers representing the nodes, Mary's grammar becomes 

    let dictionary: [String:Node] = [
        space:     00
        person:    10
        word:      20
        adjective: 30
        noun:      40
        sentence:  50

    00 TRM " "

    10 TRM '[A-Z][a-z]+'

    20 TRM '"[a-z]+"'

    30 ALT
     31 TRM "little"
     32 TRM "red"

    40 ALT
     41 TRM "lamb"
     42 TRM "car"

    50 SEQ
     51 NTM person 10
     52 SEQ
      53 GRP true true
       54 NTM word 20
      55 SEQ
       56 NTM adjective 30
       57 SEQ
        58 NTM noun 40
        59 TRM "."

The AST can be used to either parse the input text directly or to generate Swift code that implements a parser program that needs to be compiled.  The parser consumes tokens whenever the token type matches the TRM node type, and reports an error otherwise.

A naive parser could try all possible paths through the AST to try and match the input text but that could be exponentionally difficult. A very much simplified approach is to select the path through the AST based on the value of the last read token and first/follow sets that are pre-computed.  If at every choice point (ALT or GRP node) there is only one choice possible (because the first sets of the alternatives are disjoint) then the grammar is LL(1) and parsing will be as fast as can be. 

The AST nodes contain first and follow sets.

Grammars are often LL(1) but for a few exceptions. If, however, the current token matches more than one possible path, the parser needs to spawn a copy of itself and pursue both options. This can be very inefficient unless case is taken to re-use previusly walked paths and share the stack storage. GSS

If grammars are ambiguous then there is more than one way to parse a valid sentence. For example: the grammar `S = { "." } { "." }` may match the sentence `.....` in six possible ways, depending on how greedy the iterations behave. A GLL parser will store all of these possible matches in a parse forrest, which is an efficient way to store multiple parse trees.

### A Better Way

So far so good, but this traditional approach to parsers for real languages will span many pages and the lines used for annotations outnumber the lines for the grammar proper. Those annotations are written in Swift and would benefit from IDE support. So, inspired by SwiftUI, let's flip it around and write the grammar in a DSL defined by Swift itself.

elements: literal string, generative string, reference, sequence, selection, repetition, grouping
```swift
    struct grammar: Grammar {
        var body: some Grammar {
            Rule "space" { " " }
            Rule "person" { '[A-Z][a-z]+' }
            "word") { '"[a-z]+"' }
            Rule("adjective") {
                Alternative {
                "little" | "red"
                }
            Rule("noun") {
                "lamb" | "car"
                }
            Rule("sentence") {
                person { word } 
                adjective          { let adj = token.image }
                noun               { if noun.image == "lamb" && adj = "red" { 
                                         print("lambs can't be red")
                                     }
                "."                { if token.previous.kind == "space" { 
                                         print("dots shall not follow spaces")
                                     }
                                   }
                }
        }
    }
```



First of all, the grammar rules are declared as structs:
```swift
    struct grammar: Grammar {
        var body: some Grammar {
            Rule("space")
            Rule("person")
            Rule("word")
            Rule("adjective")
            Rule("noun")
            Rule("sentence")
        }
    }
    struct Rule: Grammar {
        var name: String
        var isSilent = false
        var body: some Grammar {
            Alternative()
    }
    struct Alternative: Grammar {
```
alternatives: [Production]
up to 10 as per SwiftUI functionbuilder


Second, the annotations are changed into closures:






