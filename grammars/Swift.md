# Swift 6.4 Grammar

### Grammar of a top-level declaration
_top-level-declaration → statements?_

```apus
shebang - /#!.*/ .
topLevelDeclaration = shebang? statements? .
```


## Whitespace and Comment

### Grammar of whitespace
_whitespace → whitespace-item whitespace?_
_whitespace-item → line-break_
_whitespace-item → inline-space_
_whitespace-item → comment_
_whitespace-item → multiline-comment_
_whitespace-item → U+0000, U+000B, or U+000C_
_line-break → U+000A_
_line-break → U+000D_
_line-break → U+000D followed by U+000A_
_inline-spaces → inline-space inline-spaces?_
_inline-space → U+0009 or U+0020_
_comment → //  comment-text line-break_
_multiline-comment → **/\*** multiline-comment-text **\*/**_
_comment-text → comment-text-item comment-text?_
_comment-text-item → **Any** Unicode scalar value except U+000A or U+000D_
_multiline-comment-text → multiline-comment-text-item multiline-comment-text?_
_multiline-comment-text-item → multiline-comment_
_multiline-comment-text-item → comment-text-item_
_multiline-comment-text-item → **Any** Unicode scalar value except **/\*** or **\*/**_

```apus
whitespace          : /[\u{0000}\u{0009}\u{000A}\u{000B}\u{000C}\u{000D}\u{0020}\u{00A0}\u{FEFF}]+/ .

comment             : /\/\/.*\r?\n?/ .

multilineComment    : "/*" { /(?s)(?:[^*\/]|\*(?!\/)|\/(?!\*))+/ | multilineComment } "*/" .
```


## Identifiers

### Grammar of an identifier
_identifier → identifier-head identifier-characters?_
_identifier → \` identifier-head identifier-characters? \`_
_identifier → implicit-parameter-name_
_identifier → property-wrapper-projection_
_identifier-list → identifier | identifier **,** identifier-list_
_identifier-head → Upper- or lowercase letter A through Z_
_identifier-head → **\_**_
_identifier-head → U+00A8, U+00AA, U+00AD, U+00AF, U+00B2–U+00B5, or U+00B7–U+00BA_
_identifier-head → U+00BC–U+00BE, U+00C0–U+00D6, U+00D8–U+00F6, or U+00F8–U+00FF_
_identifier-head → U+0100–U+02FF, U+0370–U+167F, U+1681–U+180D, or U+180F–U+1DBF_
_identifier-head → U+1E00–U+1FFF_
_identifier-head → U+200B–U+200D, U+202A–U+202E, U+203F–U+2040, U+2054, or U+2060–U+206F_
_identifier-head → U+2070–U+20CF, U+2100–U+218F, U+2460–U+24FF, or U+2776–U+2793_
_identifier-head → U+2C00–U+2DFF or U+2E80–U+2FFF_
_identifier-head → U+3004–U+3007, U+3021–U+302F, U+3031–U+303F, or U+3040–U+D7FF_
_identifier-head → U+F900–U+FD3D, U+FD40–U+FDCF, U+FDF0–U+FE1F, or U+FE30–U+FE44_
_identifier-head → U+FE47–U+FFFD_
_identifier-head → U+10000–U+1FFFD, U+20000–U+2FFFD, U+30000–U+3FFFD, or U+40000–U+4FFFD_
_identifier-head → U+50000–U+5FFFD, U+60000–U+6FFFD, U+70000–U+7FFFD, or U+80000–U+8FFFD_
_identifier-head → U+90000–U+9FFFD, U+A0000–U+AFFFD, U+B0000–U+BFFFD, or U+C0000–U+CFFFD_
_identifier-head → U+D0000–U+DFFFD or U+E0000–U+EFFFD_
_identifier-character → decimal-digit_
_identifier-character → U+0300–U+036F, U+1DC0–U+1DFF, U+20D0–U+20FF, or U+FE20–U+FE2F_
_identifier-character → identifier-head_
_identifier-characters → identifier-character identifier-characters?_
_implicit-parameter-name → $ decimal-digits_
_property-wrapper-projection → $ identifier-characters_

```apus
@literalMunch
identifier                  - @builder .

escapedIdentifier           - @builder .

implicitParameterName       - /\$[0-9]+/ .

propertyWrapperProjection   - @builder .

memberName =
    | identifier ---( "_" )
    | escapedIdentifier
    | propertyWrapperProjection
    .
softIdentifier =
    | identifier ---( "_" "let" "var" "inout" )
    | escapedIdentifier
    | propertyWrapperProjection
    .
hardIdentifier =
    | identifier ---( "_" "Any" "as" "associatedtype" "break" "case" "catch" "class" "continue" "default" "defer" "deinit" "do"
                      "else" "enum" "extension" "fallthrough" "false" "fileprivate" "for" "func" "guard" "if" "import" "in" "init"
                      "inout" "internal" "is" "let" "nil" "operator" "precedencegroup" "private" "protocol" "public" "repeat"
                      "rethrows" "return" "self" "Self" "static" "struct" "subscript" "super" "switch" "throw" "throws" "true"
                      "try" "typealias" "var" "where" "while" )
    | escapedIdentifier
    | propertyWrapperProjection
    .
expressionIdentifier =
    | identifier ---( "_" "Any" "as" "associatedtype" "break" "case" "catch" "class" "continue" "default" "defer" "deinit" "do"
                      "else" "enum" "extension" "fallthrough" "false" "fileprivate" "for" "func" "guard" "if" "import" "in" "init"
                      "inout" "internal" "is" "let" "nil" "operator" "precedencegroup" "private" "protocol" "public" "repeat"
                      "rethrows" "return" "self" "Self" "static" "struct" "subscript" "super" "switch" "throw" "throws" "true"
                      "try" "typealias" "var" "where" "while" "await" )
    | escapedIdentifier
    | propertyWrapperProjection
    .
argumentLabelName =
    | identifier ---( "_" "inout" )
    | escapedIdentifier
    | propertyWrapperProjection
    .
identifierList = hardIdentifier { "," hardIdentifier } .
```


## Literals

### Grammar of a literal
_literal → numeric-literal | string-literal | regular-expression-literal | boolean-literal | nil-literal_
_numeric-literal → signed-integer-literal | signed-floating-point-literal_
_boolean-literal → **true** | **false**_
_nil-literal → **nil**_

### Grammar of an integer literal
_signed-integer-literal → **-**? integer-literal_
_integer-literal → binary-literal_
_integer-literal → octal-literal_
_integer-literal → decimal-literal_
_integer-literal → hexadecimal-literal_
_binary-literal → 0b binary-digit binary-literal-characters?_
_binary-digit → Digit 0 or 1_
_binary-literal-character → binary-digit | **\_**_
_binary-literal-characters → binary-literal-character binary-literal-characters?_
_octal-literal → 0o octal-digit octal-literal-characters?_
_octal-digit → Digit 0 through 7_
_octal-literal-character → octal-digit | **\_**_
_octal-literal-characters → octal-literal-character octal-literal-characters?_
_decimal-literal → decimal-digit decimal-literal-characters?_
_decimal-digit → Digit 0 through 9_
_decimal-digits → decimal-digit decimal-digits?_
_decimal-literal-character → decimal-digit | **\_**_
_decimal-literal-characters → decimal-literal-character decimal-literal-characters?_
_hexadecimal-literal → 0x hexadecimal-digit hexadecimal-literal-characters?_
_hexadecimal-digit → Digit 0 through 9, a through f, or A through F_
_hexadecimal-literal-character → hexadecimal-digit | **\_**_
_hexadecimal-literal-characters → hexadecimal-literal-character hexadecimal-literal-characters?_

### Grammar of a floating-point literal
_signed-floating-point-literal → **>** **-**? floating-point-literal floating-point-literal → decimal-literal decimal-fraction? decimal-exponent?_
_floating-point-literal → hexadecimal-literal hexadecimal-fraction? hexadecimal-exponent_
_decimal-fraction → **.** decimal-literal_
_decimal-exponent → floating-point-e sign? decimal-literal_
_hexadecimal-fraction → **.** hexadecimal-digit hexadecimal-literal-characters?_
_hexadecimal-exponent → floating-point-p sign? decimal-literal_
_floating-point-e → e | E_
_floating-point-p → p | P_
_sign → + | **-**_

```apus
decimalDigits                   - /[0-9]+/ .

binaryLiteral                   - /0b[0-1][0-1_]*/ .
octalLiteral                    - /0o[0-7][0-7_]*/ .
decimalLiteral                  - /[0-9][0-9_]*/ .
hexadecimalLiteral              - /0x[0-9a-fA-F][0-9a-fA-F_]*/ .
integerLiteral =
    | binaryLiteral
    | octalLiteral
    | decimalLiteral
    | hexadecimalLiteral
    .
signedIntegerLiteral            = [ "-" >s< ] integerLiteral .
```

```apus
decimalFloatingPointLiteral     - /[0-9][0-9_]*(?:\.[0-9][0-9_]*(?:[eE][+-]?[0-9][0-9_]*)?|[eE][+-]?[0-9][0-9_]*)/ .
hexadecimalFloatingPointLiteral - /0x[0-9a-fA-F][0-9a-fA-F_]*(?:\.[0-9a-fA-F][0-9a-fA-F_]*)?(?:[pP][+-]?[0-9][0-9_]*)/ .
floatingPointLiteral =
    | decimalFloatingPointLiteral
    | hexadecimalFloatingPointLiteral
    .
signedFloatingPointLiteral = [ "-" >s< ] floatingPointLiteral .

numericLiteral = signedIntegerLiteral | signedFloatingPointLiteral .

booleanLiteral = "true" | "false" .

nilLiteral = "nil" .

literal =
    | numericLiteral
    | stringLiteral
    | regularExpressionLiteral
    | booleanLiteral
    | nilLiteral
    .
```


## Strings

### Grammar of a string literal
_string-literal → static-string-literal | interpolated-string-literal_
_string-literal-opening-delimiter → extended-string-literal-delimiter? "_
_string-literal-closing-delimiter → " extended-string-literal-delimiter?_
_static-string-literal → string-literal-opening-delimiter quoted-text? string-literal-closing-delimiter_
_static-string-literal → multiline-string-literal-opening-delimiter multiline-quoted-text? multiline-string-literal-closing-delimiter_
_multiline-string-literal-opening-delimiter → extended-string-literal-delimiter? """_
_multiline-string-literal-closing-delimiter → """ extended-string-literal-delimiter?_
_extended-string-literal-delimiter → **#** extended-string-literal-delimiter?_
_quoted-text → quoted-text-item quoted-text?_
_quoted-text-item → escaped-character_
_quoted-text-item → **Any** Unicode scalar value except ", \\, U+000A, or U+000D_
_multiline-quoted-text → multiline-quoted-text-item multiline-quoted-text?_
_multiline-quoted-text-item → escaped-character_
_multiline-quoted-text-item → **Any** Unicode scalar value except **\\**_
_multiline-quoted-text-item → escaped-newline_
_interpolated-string-literal → string-literal-opening-delimiter interpolated-text? string-literal-closing-delimiter_
_interpolated-string-literal → multiline-string-literal-opening-delimiter multiline-interpolated-text? multiline-string-literal-closing-delimiter_
_interpolated-text → interpolated-text-item interpolated-text?_
_interpolated-text-item → \\( expression **)** | quoted-text-item_
_multiline-interpolated-text → multiline-interpolated-text-item multiline-interpolated-text?_
_multiline-interpolated-text-item → \\( expression **)** | multiline-quoted-text-item_
_escape-sequence → **\\** extended-string-literal-delimiter_
_escaped-character → escape-sequence 0 | escape-sequence **\\** | escape-sequence t | escape-sequence n | escape-sequence r | escape-sequence " | escape-sequence '_
_escaped-character → escape-sequence u **{** unicode-scalar-digits **}**_
_unicode-scalar-digits → Between one and eight hexadecimal digits_
_escaped-newline → escape-sequence inline-spaces? line-break_

```apus
singleLineStringLiteral                         - @builder .
extendedSinglelineStringLiteral                 - @builder .

multilineStringLiteral                          - @builder .
extendedMultilineStringLiteral                  - @builder .

interpolatedStringLiteralHead                   - @builder .
interpolatedStringLiteralPart                   - @builder .
interpolatedStringLiteralTail                   - @builder .

extendedInterpolatedStringLiteralHead           - @builder .
extendedInterpolatedStringLiteralPart           - @builder .
extendedInterpolatedStringLiteralTail           - @builder .

multilineInterpolatedStringLiteralHead          - @builder .
multilineInterpolatedStringLiteralPart          - @builder .
multilineInterpolatedStringLiteralTail          - @builder .

extendedMultilineInterpolatedStringLiteralHead  - @builder .
extendedMultilineInterpolatedStringLiteralPart  - @builder .
extendedMultilineInterpolatedStringLiteralTail  - @builder .

stringLiteral =
    | staticStringLiteral
    | interpolatedStringLiteral
    .
staticStringLiteral =
    | singleLineStringLiteral
    | multilineStringLiteral
    | @excludedFrom(availableAttribute) extendedSinglelineStringLiteral
    | @excludedFrom(availableAttribute) extendedMultilineStringLiteral
    .
interpolatedStringLiteral =
    | singleLineInterpolatedStringLiteral
    | multilineInterpolatedStringLiteral
    .
@sameLine
singleLineInterpolatedStringLiteral =
    | interpolatedStringLiteralHead functionCallArgumentList? { interpolatedStringLiteralPart functionCallArgumentList? } interpolatedStringLiteralTail
    | extendedInterpolatedStringLiteralHead functionCallArgumentList? { extendedInterpolatedStringLiteralPart functionCallArgumentList? } extendedInterpolatedStringLiteralTail
    .
multilineInterpolatedStringLiteral =
    | multilineInterpolatedStringLiteralHead functionCallArgumentList? { multilineInterpolatedStringLiteralPart functionCallArgumentList? } multilineInterpolatedStringLiteralTail
    | extendedMultilineInterpolatedStringLiteralHead functionCallArgumentList? { extendedMultilineInterpolatedStringLiteralPart functionCallArgumentList? } extendedMultilineInterpolatedStringLiteralTail
    .
```


## Regular Expressions

### Grammar of a regular expression literal
_regular-expression-literal → regular-expression-literal-opening-delimiter regular-expression regular-expression-literal-closing-delimiter_
_regular-expression → **Any** regular expression_
_regular-expression-literal-opening-delimiter → extended-regular-expression-literal-delimiter? /_
_regular-expression-literal-closing-delimiter → / extended-regular-expression-literal-delimiter?_
_extended-regular-expression-literal-delimiter → **#** extended-regular-expression-literal-delimiter?_

```apus
regexSlash           - /\// .

regexEscape          - /\\[^\r\n]/ .
regexNonOperatorAtom - /[^\/\\\[\]\(\)\r\n\u{20}\u{09}\+\-\*%&\|\^~<>=!\?\.#;:,]/ .
tabbedPlainRegularExpressionLiteral - /\/(?:\\[^\r\n]|[^\/\\\r\n])*\u{09}(?:\\[^\r\n]|[^\/\\\r\n])*\// .
regexBodyNoTab       - /(?:(?:\\[^\r\n]|[^\/\\\r\n\u{09}\u{20}])(?:\\[^\r\n]|[^\/\\\r\n\u{09}])*(?:\\[^\r\n]|[^\/\\\r\n\u{09}\u{20}])|(?:\\[^\r\n]|[^\/\\\r\n\u{09}\u{20}]))/ .

regexSpaceAtom       - /[\u{20}]/ .
regexClassAtom       - /[^\\\]\r\n\u{09}]/ .

regexOperatorChar    - /[-+*%|^~<>=!?&.]/ .

extendedRegularExpressionLiteral - @builder .

plainRegularExpressionLiteral =
    | @cannotParse(tabbedPlainRegularExpressionLiteral)
          >n< <-< ( "true" "false" "nil" "self" "Self" "super" "Any" "func" "operator"
                identifier escapedIdentifier implicitParameterName propertyWrapperProjection binaryLiteral octalLiteral
                decimalLiteral hexadecimalLiteral decimalFloatingPointLiteral hexadecimalFloatingPointLiteral
                regexSlash extendedRegularExpressionLiteral
                "_" ")" "]" "}" ">" closeAngle forceMark optionalMark "->" "..." "." "@" )
          regexSlash >s< regexBody >s< regexSlash
    | <n> regexSlash >s< regexBody >s< regexSlash
    .

regexBody           = regexBodyNoTab .
regexItem           = regexEscape
                    | regexCharacterClass
                    | regexGroup
                    | "("
                    | regexNonOperatorAtom
                    | regexOperatorChar
                    | "#" | ":" | ";" | "," | "]" .

regexGroup          = "(" { >n< ( regexSpaceAtom | regexItem ) } >n< ")" .
regexCharacterClass = "[" >n< ( regexEscape | regexClassAtom ) { >n< ( regexEscape | regexClassAtom ) } >n< "]" .

regexScannerAtom    - /[^\/\\\r\n\u{20}\u{09}\(\)]/ .

tryScanOperatorAsRegexLiteral = @cannotParse(tabbedPlainRegularExpressionLiteral)
                               >n< <-< ( "true" "false" "nil" "self" "Self" "super" "Any"
                                          "func" "operator"
                                          identifier escapedIdentifier implicitParameterName propertyWrapperProjection
                                          binaryLiteral octalLiteral decimalLiteral hexadecimalLiteral
                                          decimalFloatingPointLiteral hexadecimalFloatingPointLiteral
                                          regexSlash extendedRegularExpressionLiteral
                                          "_" ")" "]" "}"
                                          ">" closeAngle
                                          forceMark
                                          optionalMark
                                          "->" "..." "." "@" )
                               regexSlash >s< tryScanOperatorAsRegexLiteralBody >s< regexSlash .
tryScanOperatorAsRegexLiteralBody   = tryScanOperatorAsRegexLiteralItem { >n< regexSpaceAtom? >n< tryScanOperatorAsRegexLiteralItem } .
tryScanOperatorAsRegexLiteralItem   = regexEscape | tryScanOperatorAsRegexLiteralGroup | "(" | regexScannerAtom .
tryScanOperatorAsRegexLiteralGroup  = "(" { >n< ( regexSpaceAtom | tryScanOperatorAsRegexLiteralItem ) } >n< ")" .

regularExpressionLiteral            = plainRegularExpressionLiteral .
regularExpressionLiteral            = <-< ( "true" "false" "nil" "self" "Self" "super" "Any" "func" "operator"
                                            identifier escapedIdentifier implicitParameterName propertyWrapperProjection
                                            binaryLiteral octalLiteral decimalLiteral hexadecimalLiteral
                                            decimalFloatingPointLiteral hexadecimalFloatingPointLiteral
                                            regexSlash extendedRegularExpressionLiteral
                                            ")" "]" "}" ">" "->" "..." "." "@" )
                                      extendedRegularExpressionLiteral .
```


## Operators

### Grammar of operators
_**operator** → operator-head operator-characters?_
_**operator** → dot-operator-head dot-operator-characters_
_operator-head → / | **=** | **-** | + | **!** | **\*** | % | < | **>** | **&** | | | ^ | **~** | **?**_
_operator-head → U+00A1–U+00A7_
_operator-head → U+00A9 or U+00AB_
_operator-head → U+00AC or U+00AE_
_operator-head → U+00B0–U+00B1_
_operator-head → U+00B6, U+00BB, U+00BF, U+00D7, or U+00F7_
_operator-head → U+2016–U+2017_
_operator-head → U+2020–U+2027_
_operator-head → U+2030–U+203E_
_operator-head → U+2041–U+2053_
_operator-head → U+2055–U+205E_
_operator-head → U+2190–U+23FF_
_operator-head → U+2500–U+2775_
_operator-head → U+2794–U+2BFF_
_operator-head → U+2E00–U+2E7F_
_operator-head → U+3001–U+3003_
_operator-head → U+3008–U+3020_
_operator-head → U+3030_
_operator-character → operator-head_
_operator-character → U+0300–U+036F_
_operator-character → U+1DC0–U+1DFF_
_operator-character → U+20D0–U+20FF_
_operator-character → U+FE00–U+FE0F_
_operator-character → U+FE20–U+FE2F_
_operator-character → U+E0100–U+E01EF_
_operator-characters → operator-character operator-characters?_
_dot-operator-head → **.**_
_dot-operator-character → **.** | operator-character_
_dot-operator-characters → dot-operator-character dot-operator-characters?_
_infix-operator → **operator**_
_prefix-operator → **operator**_
_postfix-operator → **operator**_

```apus
@literalMunch @preempt(regexSlash, tryScanOperatorAsRegexLiteral)
nonArrowOperatorToken   - @builder .

@literalMunch
dotOperator             - @builder .
```

```apus
operator                = @cannotParse( regularExpressionLiteral ) nonArrowOperatorToken .
operator                = dotOperator .

postfixOperatorToken    - @builder .

operatorName            - @builder .

@preempt(openAngle)
functionNameOperator    - @builder .

openAngle       - /</ .
closeAngle      - />/ .
optionalMark    - /\?/ .
forceMark       - /!/ .

keyPathDot      - /\./ .
keyPathMarkRunStart - /[?!](?=[?!])/ .
keyPathMarkRunOptional - /\?(?=[?!])/ .
keyPathMarkRunForce    - /!(?=[?!])/ .
keyPathDotSubscriptStart - /\.(?=\[)/ .

infixOperator   = operator | "&" .

prefixOperator  = operator .

postfixOperator = postfixOperatorToken
                | dotOperator .
```


## Types

### Grammar of a type
_type → function-type_
_type → array-type_
_type → dictionary-type_
_type → type-identifier_
_type → tuple-type_
_type → optional-type_
_type → implicitly-unwrapped-optional-type_
_type → protocol-composition-type_
_type → opaque-type_
_type → boxed-protocol-type_
_type → metatype-type_
_type → any-type_
_type → self-type_
_type → **(** type **)**_

```apus
type =
    | functionType
    | arrayType
    | inlineArrayType
    | dictionaryType
    | placeholderType
    | typeIdentifier
    | tupleType
    | optionalType
    | implicitlyUnwrappedOptionalType
    | protocolCompositionType
    | opaqueType
    | boxedProtocolType
    | @prefer metatypeType
    | packExpansionType
    | selfMemberType
    | anyType
    | "(" tupleTypeElement ")"
    | suppressedType
    | parameterModifier type
    | attribute type
    .

suppressedType =
    | <s> "~" >s< type
    | <+< ( "(" "[" "{" "," ";" ":" "as" "is" forceMark optionalMark ) >s< "~" >s< type
    .
```


### Grammar of a type annotation
_type-annotation → **:** attributes? type_

```apus
typeAnnotation = ":" resultType .
resultType = type .
resultType = namedOpaqueReturnType .
namedOpaqueReturnType = genericParameterClause type .
```


### Grammar of a type identifier
_type-identifier → type-name generic-argument-clause? | type-name generic-argument-clause? **.** type-identifier_
_type-name → identifier_

```apus
placeholderType = "_" .

typeIdentifier  =
    | typeName typeGenericArgumentClause?
    | typeIdentifier "." >n< >-> ( "Type" "Protocol" ) typeName typeGenericArgumentClause?
    .

typeName =
    | hardIdentifier
    | selfType
    | moduleSelector identifier ---( "_" )
    .

moduleSelector = @excludedFrom(valueBindingPattern) hardIdentifier "::" >n< .
```


### Grammar of a tuple type
_tuple-type → **(** **)** | **(** tuple-type-element **,** tuple-type-element-list **)**_
_tuple-type-element-list → tuple-type-element | tuple-type-element **,** tuple-type-element-list_
_tuple-type-element → element-name type-annotation | type_
_element-name → identifier_

```apus
tupleType               = "(" ")"
                        | "(" tupleTypeElement "," tupleTypeElementList ","? ")" .
tupleTypeElementList    = tupleTypeElement { "," tupleTypeElement } .

tupleTypeElement        = elementName typeAnnotation | type .
elementName             = identifier ---( "_" ) | escapedIdentifier | "_" .
```


### Grammar of a function type
_function-type → attributes? function-type-argument-clause **async**? throws-clause? **->** type_
_function-type-argument-clause → **(** **)**_
_function-type-argument-clause → **(** function-type-argument-list **...**? **)**_
_function-type-argument-list → function-type-argument | function-type-argument **,** function-type-argument-list_
_function-type-argument → attributes? parameter-modifier? type | argument-label type-annotation_
_argument-label → identifier_
_throws-clause → **throws** | **throws** **(** type **)**_

```apus
functionType                = functionTypeArgumentClause "async"? throwsClause? "->" type .

functionTypeArgumentClause  = "(" ")" | "(" functionTypeArgumentList "..."? ","? ")" .

functionTypeArgumentList    = functionTypeArgument { "," functionTypeArgument } .

functionTypeArgument        = type | externalArgumentLabel? localArgumentLabel typeAnnotation .

externalArgumentLabel       = softIdentifier | "_" .
localArgumentLabel          = softIdentifier | "_" .

throwsClause                = "throws" [ "(" type ")" ] .

declarationThrowsClause     = throwsClause | "rethrows" .
```


### Grammar of an array type
_array-type → **[** type **]**_

```apus
arrayType       = "[" type "]" .

inlineArrayType = "[" genericArgument >n< "of" genericArgument "]" .
```


### Grammar of a dictionary type
_dictionary-type → **[** type **:** type **]**_

```apus
dictionaryType  = "[" type ":" type "]" .

simpleType      = typeIdentifier | tupleType | arrayType | inlineArrayType | dictionaryType
                | optionalType | implicitlyUnwrappedOptionalType | metatypeType | selfMemberType
                | anyType
                | "(" tupleTypeElement ")" .
```


### Grammar of an optional type
_optional-type → type **?**_

```apus
optionalType    = simpleType >s< optionalMark .
```


### Grammar of an implicitly unwrapped optional type
_implicitly-unwrapped-optional-type → type **!**_

```apus
implicitlyUnwrappedOptionalType = simpleType >s< forceMark .
```


### Grammar of a protocol composition type
_protocol-composition-type → type-identifier **&** protocol-composition-continuation_
_protocol-composition-continuation → type-identifier | protocol-composition-type_

```apus
protocolCompositionType = protocolCompositionElement "&" protocolCompositionContinuation .
protocolCompositionContinuation = protocolCompositionElement | protocolCompositionType .
protocolCompositionElement = "~"? typeIdentifier | anyType .
```


### Grammar of an opaque type
_opaque-type → **some** type_

```apus
opaqueType = "some" type .
```


### Grammar of a boxed protocol type
_boxed-protocol-type → **any** type_

```apus
boxedProtocolType = "any" >-> ( "inout" "borrowing" "consuming" "isolated" "sending" "nonisolated" "dependsOn"
                                "_const" "__shared" "__owned"  )
                    type .
```


### Grammar of a metatype type
_metatype-type → type **.** **Type** | type **.** **Protocol**_

```apus
metatypeType = simpleType "." >n< ( "Type" | "Protocol" ) .
```

_SE-0393 pack expansion / pack element TYPE. Two nonterminals because swift-syntax has two_
_nodes: \`PackExpansionType(repeatKeyword:, repetitionPattern:)\` wrapping_
_\`PackElementType(eachKeyword:, pack:)\`. \`**repeat** **each** T\` **in** \`(**\_** value: **repeat** **each** T)\`._

```apus
packExpansionType = "repeat" packElementType .
packElementType   = "each" type .
```

_\`T.**self**\` **in** TYPE position — swift-syntax \`MemberType\` with a \`**self**\` name, e.g. the cast type **in**_
_\`value **as**? Foo.**self**\`. The base **is** \`simpleType\`, not \`typeIdentifier\`, because MEASURED:_
_value **as** A<B>?.**self**  →  MemberType(baseType: OptionalType(IdentifierType(A, <B>)), name: **self**)_
_so an **optional** (and **any** other simple-type **postfix**) may carry the \`.**self**\`. While this sat on_
_\`typeIdentifier\` the optional-based form had no type derivation at all, which **is** why_
_\`value **as**!A<B>?.**self**\` and \`value **as** A<B>?.**self**\` built NO tree, and \`value **as**? Foo.**self**\` built a_
_\`MissingType\` — the alternate existed but no converter **case** matched it._

```apus
selfMemberType = simpleType "." >n< "self" .
```


### Grammar of an Any type
_any-type → **Any**_

```apus
anyType      = "Any" .
```


### Grammar of a Self type
_self-type → **Self**_

```apus
selfType     = "Self" .
```


### Grammar of a type inheritance clause
_type-inheritance-clause → **:** type-inheritance-list_
_type-inheritance-list → attributes? ~? type-identifier | attributes? ~? type-identifier **,** type-inheritance-list_

```apus
typeInheritanceClause   = ":" typeInheritance { "," typeInheritance } .
typeInheritance         = attributes? "~"? "nonisolated"? typeIdentifier .
typeInheritance         = classRestrictionType .
classRestrictionType    = "class" .
```


## Expressions

### Grammar of an expression
_expression → try-operator? await-operator? prefix-expression infix-expressions?_

```apus
expression = tryOperator? awaitOperator? conditionalExpression coercingOperator? .
expression = tryOperator? awaitOperator? prefixExpression infixExpressions? .
```


### Grammar of a prefix expression
_prefix-expression → prefix-operator? postfix-expression_
_prefix-expression → in-out-expression_

```apus
@longest
prefixExpression    = @shortest [ prefixOperator >s< ] postfixExpression .
prefixExpression    = "!" >s< postfixExpression .
prefixExpression    = inOutExpression .
prefixExpression    = keyPathExpression .
prefixExpression    = packExpansionExpression .
packExpansionExpression = "repeat" packElementExpression .
packElementExpression   = "each" <s> postfixExpression .
prefixExpression    = "consume" >->( "(" "[" "." ) <s> >n< prefixExpression .
prefixExpression    = "borrow"  >->( "(" "[" "." ) <s> >n< prefixExpression .
prefixExpression    = "copy"    >->( "(" "[" "." ) <s> >n< prefixExpression .
prefixExpression    = @prefer "unsafe"  <s> >n< prefixExpression .
```


### Grammar of an in-out expression
_in-out-expression → **&** primary-expression_

```apus
inOutExpression     = "&" >s< postfixExpression .
```


### Grammar of a try expression
_try-operator → **try** | **try** **?** | **try** **!**_

```apus
tryOperator =
    | "try" <s>
    | "try" >s< >-> ( forceMark optionalMark )
    | "try" >s< "?"
    | "try" >s< "!"
    .
```


### Grammar of an await expression
_await-operator → **await**_

```apus
awaitOperator =
    | "await" <s>
    | "await" >s< >+> ( "(" "[" "." )
    .
```


### Grammar of an infix expression
_infix-expression → infix-operator prefix-expression_
_infix-expression → assignment-operator try-operator? await-operator? prefix-expression_
_infix-expression → conditional-operator try-operator? await-operator? prefix-expression_
_infix-expression → type-casting-operator_
_infix-expressions → infix-expression infix-expressions?_

```apus
@longest
infixExpression = @cannotParse( genericArgumentClause ) >s< ( postfixOperatorToken | dotOperator | "&" ) >s< tryOperator? awaitOperator? prefixExpression .
infixExpression = <s> infixOperator <s> tryOperator? awaitOperator? prefixExpression .
infixExpression = arrowExpr tryOperator? awaitOperator? prefixExpression .
infixExpression = assignmentOperator expression .
infixExpression = conditionalOperator expression .
infixExpression = typeCastingOperator .
infixExpressions = infixExpression infixExpressions? .

arrowExpr = typeEffectSpecifiers? "->" >->( "async" "throws" "rethrows" ) .
typeEffectSpecifiers = "async" | "async" throwsClause | throwsClause .

conditionInfixExpression = >s< infixOperator >s< tryOperator? awaitOperator? prefixExpression .
conditionInfixExpression = <s> infixOperator <s> tryOperator? awaitOperator? prefixExpression .
conditionInfixExpression = conditionalOperator expression .
conditionInfixExpression = typeCastingOperator .
conditionInfixExpressions = conditionInfixExpression conditionInfixExpressions? .

conditionExpression = tryOperator? awaitOperator? conditionalExpression coercingOperator?
                    | tryOperator? awaitOperator? prefixExpression conditionInfixExpressions? .
```


### Grammar of an assignment operator
_assignment-operator → **=**_

```apus
assignmentOperator = <s> "=" <s>
                   | >s< "=" >s< .
```


### Grammar of a conditional operator
_conditional-operator → **?** expression **:**_

```apus
conditionalOperator = <s> "?" expression ":" .
```


### Grammar of a type-casting operator
_type-casting-operator → **is** type_
_type-casting-operator → **as** type_
_type-casting-operator → **as** **?** type_
_type-casting-operator → **as** **!** type_

```apus
typeCastingOperator = "is" type
                    | "as" type
                    | "as" >s< optionalMark type
                    | "as" >s< forceMark type .

coercingOperator    = "as" type
                    | "as" >s< optionalMark type
                    | "as" >s< forceMark type .
```


### Grammar of a primary expression
_primary-expression → identifier generic-argument-clause?_
_primary-expression → literal-expression_
_primary-expression → self-expression_
_primary-expression → superclass-expression_
_primary-expression → conditional-expression_
_primary-expression → closure-expression_
_primary-expression → parenthesized-expression_
_primary-expression → tuple-expression_
_primary-expression → implicit-member-expression_
_primary-expression → wildcard-expression_
_primary-expression → macro-expansion-expression_
_primary-expression → key-path-expression_
_primary-expression → selector-expression_
_primary-expression → key-path-string-expression_

```apus
primaryExpression = genericIdentifier .
genericIdentifier = expressionIdentifier | expressionIdentifier genericArgumentClause .

primaryExpression = moduleGenericIdentifier .

moduleGenericIdentifier = moduleSelector identifier ---( "_" )
                        | moduleSelector identifier ---( "_" ) genericArgumentClause .
primaryExpression = moduleSelector propertyWrapperProjection .
primaryExpression = hardIdentifier "(" argumentNames ")" .
primaryExpression = implicitParameterName .
primaryExpression = literalExpression .
primaryExpression = selfExpression .
primaryExpression = superclassExpression .
primaryExpression = closureExpression .
primaryExpression = @prefer @cannotParse( parenthesisedSpecifierType ) parenthesizedExpression .
primaryExpression = tupleExpression .
primaryExpression = implicitMemberExpression .
primaryExpression = wildcardExpression .
primaryExpression = macroExpansionExpression .
primaryExpression = selfType .
primaryExpression = anyType .
primaryExpression = "(" moduleSelector? operator ")" .
primaryExpression = attribute type .
primaryExpression = inlineArrayType .
@longest
primaryExpression = boxedProtocolType .
primaryExpression = "(" functionType ")" .
primaryExpression = parenthesisedSpecifierType .
parenthesisedSpecifierType = "(" parenthesisedTypeSpecifier type ")" .

nonLiteralPrimary = genericIdentifier | moduleGenericIdentifier | moduleSelector propertyWrapperProjection
                  | hardIdentifier "(" argumentNames ")" | implicitParameterName
                  | selfExpression | superclassExpression | closureExpression
                  | parenthesizedExpression | tupleExpression | implicitMemberExpression
                  | wildcardExpression | macroExpansionExpression
                  | selfType | anyType | "(" moduleSelector? operator ")"
                  | attribute type | boxedProtocolType | "(" functionType ")" .
```


### Grammar of a literal expression
_literal-expression → literal_
_literal-expression → array-literal | dictionary-literal | playground-literal_
_array-literal → **[** array-literal-items? ,? **]**_
_array-literal-items → array-literal-item | array-literal-item **,** array-literal-items_
_array-literal-item → expression_
_dictionary-literal → **[** dictionary-literal-items ,? **]** | **[** **:** **]**_
_dictionary-literal-items → dictionary-literal-item | dictionary-literal-item **,** dictionary-literal-items_
_dictionary-literal-item → expression **:** expression_
_playground-literal → **#colorLiteral** **(** red **:** expression **,** green **:** expression **,** blue **:** expression **,** alpha **:** expression **)**_
_playground-literal → **#fileLiteral** **(** resourceName **:** expression **)**_
_playground-literal → **#imageLiteral** **(** resourceName **:** expression **)**_

```apus
literalExpression   = literal | arrayLiteral | dictionaryLiteral .

arrayLiteral        = "[" arrayLiteralItems? ","? "]" .
arrayLiteralItems   = arrayLiteralItem { "," arrayLiteralItem } .

arrayLiteralItem    = @prefer @cannotParse( parenthesisedTypeSpecifier ) expression .
arrayLiteralItem    = typeExpression .
typeExpression      = type .

dictionaryLiteral           = "[" dictionaryLiteralItems ","? "]" | "[" ":" "]" .
dictionaryLiteralItems      = dictionaryLiteralItem { "," dictionaryLiteralItem } .
dictionaryLiteralItem       = dictionaryLiteralElement ":" dictionaryLiteralElement .
dictionaryLiteralElement    = @prefer expression .
dictionaryLiteralElement    = typeExpression .
```


### Grammar of a self expression
_self-expression → **self** | self-method-expression | self-subscript-expression | self-initializer-expression_
_self-method-expression → **self** **.** identifier_
_self-subscript-expression → **self** **[** function-call-argument-list **]**_
_self-initializer-expression → **self** **.** **init**_

```apus
selfExpression          = "self" .
```


### Grammar of a superclass expression
_superclass-expression → superclass-method-expression | superclass-subscript-expression | superclass-initializer-expression_
_superclass-method-expression → **super** **.** identifier_
_superclass-subscript-expression → **super** **[** function-call-argument-list **]**_
_superclass-initializer-expression → **super** **.** **init**_

```apus
superclassExpression    = "super" .
```


### Grammar of a conditional expression
_conditional-expression → if-expression | switch-expression_
_if-expression → **if** condition-list **{** statement **}** if-expression-tail_
_if-expression-tail → **else** if-expression_
_if-expression-tail → **else** **{** statement **}**_
_switch-expression → **switch** expression **{** switch-expression-cases **}**_
_switch-expression-cases → switch-expression-case switch-expression-cases?_
_switch-expression-case → case-label statement_
_switch-expression-case → default-label statement_

```apus
conditionalExpression   = ifExpression | switchExpression .
```

```apus
ifExpression        = "if" >-> ( "{" ) conditionList codeBlock elseClause? .
elseClause          = "else" codeBlock | "else" ifExpression .

switchExpression    = "switch" >-> ( "{" ) expression "{" switchCases? "}" .

switchCases         = switchCase switchCases? .
switchCase          = caseLabel statements? .
switchCase          = defaultLabel statements? .
switchCase          = conditionalSwitchCase .
```

```apus
caseLabel           = switchCaseAttribute? "case" caseItemList ":" .
caseItemList        = matchPattern whereClause? { "," matchPattern whereClause? } .

defaultLabel        = switchCaseAttribute? "default" ":" .

switchCaseAttribute = "@" >s< attributeName .

whereClause         = "where" whereExpression .
whereExpression     = conditionExpression .

conditionalSwitchCase = switchIfDirectiveClause switchElseifDirectiveClauses? switchElseDirectiveClause? endifDirective .
switchIfDirectiveClause = ifDirective compilationCondition switchCases? .
switchElseifDirectiveClauses = switchElseifDirectiveClause switchElseifDirectiveClauses? .
switchElseifDirectiveClause = elseifDirective compilationCondition switchCases? .
switchElseDirectiveClause = elseDirective switchCases? .
```


### Grammar of a closure expression
_closure-expression → **{** attributes? closure-signature? statements? **}**_
_closure-signature → capture-list? closure-parameter-clause **async**? throws-clause? function-result? **in**_
_closure-signature → capture-list **in**_
_closure-parameter-clause → **(** **)** | **(** closure-parameter-list ,? **)** | identifier-list_
_closure-parameter-list → closure-parameter | closure-parameter **,** closure-parameter-list_
_closure-parameter → closure-parameter-name type-annotation?_
_closure-parameter → closure-parameter-name type-annotation **...**_
_closure-parameter-name → identifier_
_capture-list → **[** capture-list-items ,? **]**_
_capture-list-items → capture-list-item | capture-list-item **,** capture-list-items_
_capture-list-item → capture-specifier? identifier_
_capture-list-item → capture-specifier? identifier **=** expression_
_capture-list-item → capture-specifier? self-expression_
_capture-specifier → **weak** | **unowned** | **unowned**(**safe**) | **unowned**(**unsafe**)_

```apus
closureExpression       = samelineOpenedClosure
                        | @excludedFrom(conditionExpression) @excludedFrom(trailingClosures)
                          newlineOpenedClosure .
samelineOpenedClosure   = "{" >n< closureSignature? statements? "}" .
newlineOpenedClosure    = "{" <n> closureSignature? statements? "}" .

closureSignature = attributes? captureList? closureParameterClause "async"? throwsClause? functionResult? "in" .
closureSignature = attributes? captureList "in" .
closureSignature = attributes "in" .

closureParameterClause      = "(" ")"
                            | "(" closureParameterList ","? ")"
                            | closureShorthandNameList .

closureShorthandNameList    = closureParameterName { "," closureParameterName } .
closureParameterList        = closureParameter { "," closureParameter } .

closureParameter            = attributes? @shortest [ parameterDeclarationModifiers ] closureParameterNames typeAnnotation? .
closureParameter            = attributes? [ parameterDeclarationModifiers ] closureParameterNames typeAnnotation "..." .
closureParameterNames       = externalParameterName closureParameterName | closureParameterName .
closureParameterName        = hardIdentifier | "_" .

captureList         = "[" "]"
                    | "[" captureListItems ","? "]" .
captureListItems    = captureListItem { "," captureListItem } .
captureListItem     = captureSpecifier? hardIdentifier
                    | captureSpecifier? hardIdentifier assignmentOperator expression
                    | captureSpecifier? selfExpression .
captureSpecifier    = "weak" | "unowned" | "unowned" "(" "safe" ")" | "unowned" "(" "unsafe" ")" .
```


### Grammar of an implicit member expression
_implicit-member-expression → **.** identifier_
_implicit-member-expression → **.** identifier **.** postfix-expression_

```apus
implicitMemberExpression = "." moduleSelector? memberName .
implicitMemberExpression = "." moduleSelector? memberName "." >n< postfixExpression .
```


### Grammar of a parenthesized expression
_parenthesized-expression → **(** expression **)**_

```apus
parenthesizedExpression = "(" expression ")" .
```


### Grammar of a tuple expression
_tuple-expression → **(** **)** | **(** tuple-element **,** tuple-element-list ,? **)**_
_tuple-element-list → tuple-element | tuple-element **,** tuple-element-list_
_tuple-element → expression | identifier **:** expression_

```apus
tupleExpression     = "(" ")"
                    | "(" softIdentifier ":" expression ","? ")"
                    | "(" tupleElement "," tupleElementList ","? ")" .
tupleElementList    = tupleElement { "," tupleElement } .
tupleElement        = expression | softIdentifier ":" expression .
```


### Grammar of a wildcard expression
_wildcard-expression → **\_**_

```apus
wildcardExpression = "_" .
```


### Grammar of a macro-expansion expression
_macro-expansion-expression → **#** identifier generic-argument-clause? function-call-argument-clause? trailing-closures?_

```apus
@longest
macroExpansionExpression = macroHead genericArgumentClause? [ >n< functionCallArgumentClause ] trailingClosures? .
```


### Grammar of a key-path expression
_key-path-expression → **\\** type? **.** key-path-components_
_key-path-components → key-path-component | key-path-component **.** key-path-components_
_key-path-component → identifier key-path-postfixes? | key-path-postfixes_
_key-path-postfixes → key-path-postfix key-path-postfixes?_
_key-path-postfix → **?** | **!** | **self** | **[** function-call-argument-list **]**_

```apus
keyPathExpression = @prefer "\\" keyPathRootType keyPathComponents .
keyPathExpression = @prefer "\\" keyPathRootType keyPathExpressionStop .
keyPathExpression =         "\\" >+> ( keyPathDot ) keyPathComponents .

@longest
keyPathRootType = keyPathRootBase keyPathRootOptionals? .
keyPathRootBase = metatypeType
                | typeName typeGenericArgumentClause
                | typeName >-> ( openAngle )
                | tupleType
                | arrayType
                | inlineArrayType
                | dictionaryType
                | anyType
                | keyPathRootSuppressed
                | "(" tupleTypeElement ")" .
keyPathRootSuppressed = "~" keyPathRootBase .
keyPathRootOptionals = keyPathRootOptional { keyPathRootOptional } .
keyPathRootOptional = >s< optionalMark .
keyPathRootOptional = >s< forceMark .

keyPathComponents = keyPathProperty { keyPathProperty } keyPathExpressionStop .
keyPathComponents = keyPathProperty { keyPathProperty } keyPathPivot keyPathBareTail? keyPathBareStop .
keyPathComponents = keyPathPivotFirst keyPathBareTail? keyPathBareStop .

keyPathExpressionStop = >-> ( keyPathMarkRunStart keyPathDot ) .
keyPathBareStop = >-> ( keyPathMarkRunStart keyPathDotSubscriptStart ) .

keyPathProperty = "." >n< keyPathMemberName .

keyPathPivotFirst = keyPathDot >s< optionalMark .
keyPathPivotFirst = keyPathDot >s< forceMark .
keyPathPivotFirst = "." >n< "[" functionCallArgumentList? "]" .
keyPathPivotFirst = "[" functionCallArgumentList? "]" .
keyPathPivotFirst = keyPathMarkRunOperator .
keyPathPivotFirst = <s> forceMark .
keyPathPivot = keyPathPivotFirst .
keyPathPivot = >s< optionalMark .
keyPathPivot = >s< forceMark .

keyPathMarkRunOperator = <s> keyPathMarkRunOptional .
keyPathMarkRunOperator = <s> keyPathMarkRunForce .

keyPathBareTail = keyPathBareComponent { keyPathBareComponent } .
keyPathBareComponent = keyPathProperty .
keyPathBareComponent = >s< optionalMark .
keyPathBareComponent = keyPathMarkRunOperator .
keyPathBareComponent = >s< forceMark .
keyPathBareComponent = <s> forceMark .
keyPathBareComponent = "[" functionCallArgumentList? "]" .

keyPathMemberName = moduleSelector? softIdentifier .
keyPathMemberName = decimalDigits .
keyPathMemberName = moduleSelector? softIdentifier genericArgumentClause .
keyPathMemberName = moduleSelector? softIdentifier "(" keyPathArgumentLabels ")" .
keyPathArgumentLabels = keyPathArgumentLabel { keyPathArgumentLabel } .
keyPathArgumentLabel = identifier ---( "inout" "_" ) ":" .
keyPathArgumentLabel = "_" ":" .
```


### Grammar of a selector expression
_selector-expression → **#selector** **(** expression **)**_
_selector-expression → **#selector** **(** getter: expression **)**_
_selector-expression → **#selector** **(** setter: expression **)**_


### Grammar of a key-path string expression
_key-path-string-expression → **#keyPath** **(** expression **)**_

### Grammar of a postfix expression
_postfix-expression → primary-expression_
_postfix-expression → postfix-expression postfix-operator_
_postfix-expression → function-call-expression_
_postfix-expression → initializer-expression_
_postfix-expression → explicit-member-expression_
_postfix-expression → postfix-self-expression_
_postfix-expression → subscript-expression_
_postfix-expression → forced-value-expression_
_postfix-expression → optional-chaining-expression_

```apus
postfixExpression = primaryExpression .

postfixExpression = @prefer postfixExpression >s< postfixOperator <s>
                  | postfixExpression >s< postfixOperatorToken
                    >+> ( "." ")" "]" "}" "," ";" ":" EOF )
                  | postfixExpression >s< dotOperator          >+> ( "." ")" "]" "}" "," ";" ":" EOF ) .
postfixExpression = functionCallExpression .
postfixExpression = initializerExpression .
postfixExpression = explicitMemberExpression .
postfixExpression = subscriptExpression .
postfixExpression = forcedValueExpression .
postfixExpression = optionalChainingExpression .

nonLiteralPostfix = nonLiteralPrimary
                  | postfixExpression >s< postfixOperator <s>
                  | postfixExpression >s< postfixOperatorToken >+> ( "." ")" "]" "}" "," ";" ":" EOF )
                  | postfixExpression >s< dotOperator          >+> ( "." ")" "]" "}" "," ";" ":" EOF )
                  | functionCallExpression | initializerExpression | explicitMemberExpression
                  | subscriptExpression | forcedValueExpression | optionalChainingExpression .
```


### Grammar of a function call expression
_function-call-expression → postfix-expression function-call-argument-clause_
_function-call-expression → postfix-expression function-call-argument-clause? trailing-closures_
_function-call-argument-clause → **(** **)** | **(** function-call-argument-list ,? **)**_
_function-call-argument-list → function-call-argument | function-call-argument **,** function-call-argument-list_
_function-call-argument → expression | identifier **:** expression_
_function-call-argument → **operator** | identifier **:** **operator**_
_trailing-closures → closure-expression labeled-trailing-closures?_
_labeled-trailing-closures → labeled-trailing-closure labeled-trailing-closures?_
_labeled-trailing-closure → identifier **:** closure-expression_

```apus
functionCallExpression = postfixExpression >n< functionCallArgumentClause .
functionCallExpression = @prefer postfixExpression functionCallArgumentClause >n< trailingClosures
                       | nonLiteralPostfix >n< trailingClosures .
functionCallExpression = collectionLiteralCallee >n< trailingClosures .
collectionLiteralCallee = arrayLiteral | dictionaryLiteral .

functionCallArgumentClause = "(" ")" | "(" functionCallArgumentList ","? ")" .
functionCallArgumentList = functionCallArgument { "," functionCallArgument } .

functionCallArgument = expression
                     | argumentLabel ":" expression .
functionCallArgument = operator
                     | argumentLabel ":" operator .
functionCallArgument = moduleSelector operator
                     | argumentLabel ":" moduleSelector operator .

argumentLabel = argumentLabelName | "_" .

trailingClosures = @cannotParse(willSetDidSetBlock accessorBlockBrace) closureExpression labeledTrailingClosures
                 | @cannotParse(willSetDidSetBlock accessorBlockBrace) closureExpression >-> ( "else" ) .
labeledTrailingClosures = labeledTrailingClosure labeledTrailingClosures? .
labeledTrailingClosure = trailingClosureLabel ":" closureExpression .

trailingClosureLabel = identifier ---( "_" "let" "var" "inout" "default" ) | "_" .
```


### Grammar of an initializer expression
_initializer-expression → postfix-expression **.** **init**_
_initializer-expression → postfix-expression **.** **init** **(** argument-names **)**_

```apus
initializerExpression = "init" >-> ( "{" ) .
```


### Grammar of an explicit member expression
_explicit-member-expression → postfix-expression **.** decimal-digits_
_explicit-member-expression → postfix-expression **.** identifier generic-argument-clause?_
_explicit-member-expression → postfix-expression **.** identifier **(** argument-names **)**_
_explicit-member-expression → postfix-expression conditional-compilation-block_
_argument-names → argument-name argument-names?_
_argument-name → identifier **:**_

```apus
explicitMemberExpression = postfixExpression "." >n< decimalDigits .
explicitMemberExpression = postfixExpression "." >n< moduleSelector? memberName .
explicitMemberExpression = postfixExpression "." >n< moduleSelector? memberName genericArgumentClause .
explicitMemberExpression = postfixExpression "." >n< moduleSelector? memberName "(" argumentNames ")" .
explicitMemberExpression = postfixExpression postfixConditionalCompilationBlock .

argumentNames = argumentName argumentNames? .
argumentName = ( softIdentifier | "_" ) ":" .
```


### Grammar of a postfix self expression
_postfix-self-expression → postfix-expression **.** **self**_

### Grammar of a subscript expression
_subscript-expression → postfix-expression **[** function-call-argument-list **]**_

```apus
subscriptExpression = postfixExpression >n< "[" functionCallArgumentList? "]" .
```


### Grammar of a forced-value expression
_forced-value-expression → postfix-expression **!**_

```apus
forcedValueExpression = postfixExpression >s< forceMark .
```


### Grammar of an optional-chaining expression
_optional-chaining-expression → postfix-expression **?**_

```apus
optionalChainingExpression = postfixExpression >s< optionalMark .
```


## Statements

### Grammar of a statement
_statement → expression ;?_
_statement → declaration ;?_
_statement → loop-statement ;?_
_statement → branch-statement ;?_
_statement → labeled-statement ;?_
_statement → control-transfer-statement ;?_
_statement → defer-statement ;?_
_statement → do-statement ;?_
_statement → compiler-control-statement_
_statements → statement statements?_

```apus
statement = @cannotParse(declaration attributes) expression .
statement = declaration .

statement = @prefer @confinedTo(initializerBody) >+> ( "init" ) expression .
statement = loopStatement .
statement = branchStatement .
statement = labeledStatement .
statement = controlTransferStatement .
statement = deferStatement .
statement = doStatement .
statement = compilerControlStatement .
statement = yieldStatement .
statement = discardStatement .

yieldStatement = "yield" >-> ( "(" "[" "." ) <s> >n< expression .

discardStatement = "discard" >-> ( "(" "[" "." ) <s> >n< expression .

statements = statement ";"? .
statements = statement statementSeparator statements .
statementSeparator = <n> | ";" .
```


### Grammar of a loop statement
_loop-statement → for-in-statement_
_loop-statement → while-statement_
_loop-statement → repeat-while-statement_

```apus
loopStatement = forInStatement .
loopStatement = whileStatement .
loopStatement = repeatWhileStatement .
```


### Grammar of a for-in statement
_for-in-statement → **for** **case**? pattern **in** expression where-clause? code-block_

```apus
forInStatement = "for" "try"? "await"? "unsafe"? "case" matchPattern "in" expression whereClause? codeBlock .
forInStatement = "for" "try"? "await"? "unsafe"? bindingPattern "in" expression whereClause? codeBlock .
forInStatement = "for" "try"? "await"? "unsafe"? ( "var" | "let" ) bindingPattern "in" expression whereClause? codeBlock .
```


### Grammar of a while statement
_while-statement → **while** condition-list code-block_
_condition-list → condition | condition **,** condition-list_
_condition → expression | availability-condition | case-condition | optional-binding-condition_
_case-condition → **case** pattern initializer_
_optional-binding-condition → **let** pattern initializer? | **var** pattern initializer?_

```apus
whileStatement = "while" >-> ( "{" ) conditionList codeBlock .

conditionList = condition { "," condition } .

condition = conditionExpression
          | availabilityCondition
          | caseCondition
          | missingIntroducerWildcardCondition
          | optionalBindingCondition .

caseCondition = "case" matchPattern initializer .

missingIntroducerWildcardCondition = "_" initializer .

optionalBindingCondition = "let" bindingPattern initializer? | "var" bindingPattern initializer? .
```


### Grammar of a repeat-while statement
_repeat-while-statement → **repeat** code-block **while** expression_

```apus
repeatWhileStatement = "repeat" codeBlock "while" >-> ( "{" ) conditionExpression .
```


### Grammar of a branch statement
_branch-statement → if-statement_
_branch-statement → guard-statement_
_branch-statement → switch-statement_

### Grammar of an if statement
_if-statement → **if** condition-list code-block else-clause?_
_else-clause → **else** code-block | **else** if-statement_

### Grammar of a switch statement
_switch-statement → **switch** expression **{** switch-cases? **}**_
_switch-cases → switch-case switch-cases?_
_switch-case → case-label statements_
_switch-case → default-label statements_
_switch-case → conditional-switch-case_
_case-label → attributes? **case** case-item-list **:**_
_case-item-list → pattern where-clause? | pattern where-clause? **,** case-item-list_
_default-label → attributes? **default** **:**_
_where-clause → **where** where-expression_
_where-expression → expression_
_conditional-switch-case → switch-if-directive-clause switch-elseif-directive-clauses? switch-else-directive-clause? endif-directive_
_switch-if-directive-clause → if-directive compilation-condition switch-cases?_
_switch-elseif-directive-clauses → elseif-directive-clause switch-elseif-directive-clauses?_
_switch-elseif-directive-clause → elseif-directive compilation-condition switch-cases?_
_switch-else-directive-clause → else-directive switch-cases?_

```apus
branchStatement = guardStatement .
```


### Grammar of a guard statement
_guard-statement → **guard** condition-list **else** code-block_

```apus
guardStatement = "guard" >-> ( "{" ) conditionList "else" codeBlock .
```


### Grammar of a labeled statement
_labeled-statement → statement-label loop-statement_
_labeled-statement → statement-label if-statement_
_labeled-statement → statement-label switch-statement_
_labeled-statement → statement-label do-statement_
_statement-label → label-name **:**_
_label-name → identifier_

```apus
labeledStatement = statementLabel loopStatement .
labeledStatement = statementLabel conditionalExpression .
labeledStatement = statementLabel doStatement .

statementLabel = labelName ":" .
labelName = hardIdentifier .
```


### Grammar of a control transfer statement
_control-transfer-statement → break-statement_
_control-transfer-statement → continue-statement_
_control-transfer-statement → fallthrough-statement_
_control-transfer-statement → return-statement_
_control-transfer-statement → throw-statement_

```apus
controlTransferStatement = breakStatement
                         | continueStatement
                         | fallthroughStatement
                         | returnStatement
                         | throwStatement .
```


### Grammar of a break statement
_break-statement → **break** label-name?_

```apus
breakStatement = "break" labelName? .
```


### Grammar of a continue statement
_continue-statement → **continue** label-name?_

```apus
continueStatement = "continue" labelName? .
```


### Grammar of a fallthrough statement
_fallthrough-statement → **fallthrough**_

```apus
fallthroughStatement = "fallthrough" .
```


### Grammar of a return statement
_return-statement → **return** expression?_

```apus
returnStatement = "return" expression? .
```


### Grammar of a throw statement
_throw-statement → **throw** expression_

```apus
throwStatement = "throw" expression .
```


### Grammar of a defer statement
_defer-statement → **defer** code-block_

```apus
deferStatement = "defer" codeBlock .
```


### Grammar of a do statement
_do-statement → **do** throws-clause? code-block catch-clauses?_
_catch-clauses → catch-clause catch-clauses?_
_catch-clause → **catch** catch-pattern-list? code-block_
_catch-pattern-list → catch-pattern | catch-pattern **,** catch-pattern-list_
_catch-pattern → pattern where-clause?_

```apus
doStatement = "do" throwsClause? codeBlock catchClauses? .
catchClauses = catchClause catchClauses? .
catchClause = "catch" catchPatternList? codeBlock .

catchPatternList = catchPattern { "," catchPattern } .

catchPattern = matchPattern whereClause? .
catchPattern = whereClause .
```


### Grammar of a compiler control statement
_compiler-control-statement → conditional-compilation-block_
_compiler-control-statement → line-control-statement_
_compiler-control-statement → diagnostic-statement_

```apus
compilerControlStatement = conditionalCompilationBlock .
compilerControlStatement = lineControlStatement .
```


### Grammar of a conditional compilation block
_conditional-compilation-block → if-directive-clause elseif-directive-clauses? else-directive-clause? endif-directive_
_if-directive-clause → if-directive compilation-condition statements?_
_elseif-directive-clauses → elseif-directive-clause elseif-directive-clauses?_
_elseif-directive-clause → elseif-directive compilation-condition statements?_
_else-directive-clause → else-directive statements?_
_if-directive → **#if**_
_elseif-directive → **#elseif**_
_else-directive → **#else**_
_endif-directive → **#endif**_
_compilation-condition → platform-condition_
_compilation-condition → identifier_
_compilation-condition → boolean-literal_
_compilation-condition → **(** compilation-condition **)**_
_compilation-condition → **!** compilation-condition_
_compilation-condition → compilation-condition **&&** compilation-condition_
_compilation-condition → compilation-condition **||** compilation-condition_
_platform-condition → os **(** operating-system **)**_
_platform-condition → arch **(** architecture **)**_
_platform-condition → swift **(** >= swift-version **)** | swift **(** < swift-version **)**_
_platform-condition → compiler **(** >= swift-version **)** | compiler **(** < swift-version **)**_
_platform-condition → canImport **(** import-path **)**_
_platform-condition → targetEnvironment **(** environment **)**_
_operating-system → macOS | iOS | watchOS | tvOS | visionOS | Linux | Windows_
_architecture → arm | arm64 | i386 | wasm32 | x86\_64_
_swift-version → decimal-digits swift-version-continuation?_
_swift-version-continuation → **.** decimal-digits swift-version-continuation?_
_environment → simulator | macCatalyst_

```apus
conditionalCompilationBlock = ifDirectiveClause elseifDirectiveClauses? elseDirectiveClause? endifDirective .

postfixConditionalCompilationBlock = postfixIfDirectiveClause postfixElseifDirectiveClauses? postfixElseDirectiveClause? endifDirective .
postfixIfDirectiveClause = ifDirective compilationCondition <n> postfixIfBody? .
postfixElseifDirectiveClauses = postfixElseifDirectiveClause postfixElseifDirectiveClauses? .
postfixElseifDirectiveClause = elseifDirective compilationCondition <n> postfixIfBody? .
postfixElseDirectiveClause = elseDirective postfixIfBody? .
postfixIfBody = postfixExpression .
postfixIfBody = postfixNestedBlocks .
postfixNestedBlocks = postfixConditionalCompilationBlock postfixNestedBlocks? .

ifDirectiveClause = ifDirective compilationCondition >->( "." ) <n> statements? .
ifDirectiveClause = <-< ( identifier implicitParameterName propertyWrapperProjection binaryLiteral octalLiteral decimalLiteral hexadecimalLiteral decimalFloatingPointLiteral hexadecimalFloatingPointLiteral "true" "false" "nil" ")" "]" forceMark optionalMark ) ifDirective compilationCondition >+>( "." ) <n> statements? .
elseifDirectiveClauses = elseifDirectiveClause elseifDirectiveClauses? .
elseifDirectiveClause = elseifDirective compilationCondition >->( "." ) <n> statements? .
elseifDirectiveClause = <-< ( identifier implicitParameterName propertyWrapperProjection binaryLiteral octalLiteral decimalLiteral hexadecimalLiteral decimalFloatingPointLiteral hexadecimalFloatingPointLiteral "true" "false" "nil" ")" "]" forceMark optionalMark ) elseifDirective compilationCondition >+>( "." ) <n> statements? .
elseDirectiveClause = elseDirective >->( "." ) statements? .
elseDirectiveClause = <-< ( identifier implicitParameterName propertyWrapperProjection binaryLiteral octalLiteral decimalLiteral hexadecimalLiteral decimalFloatingPointLiteral hexadecimalFloatingPointLiteral "true" "false" "nil" ")" "]" forceMark optionalMark ) elseDirective >+>( "." ) statements? .
ifDirective = "#if" .
elseifDirective = "#elseif" .
elseDirective = "#else" <n> .
endifDirective = "#endif" <n> .

compilationCondition = hardIdentifier .
compilationCondition = booleanLiteral .
compilationCondition = "(" compilationCondition ")" .
compilationCondition = forceMark >s< >-> ( forceMark ) compilationCondition .
compilationCondition = prefixOperator >s< compilationCondition .
compilationCondition = compilationCondition "&&" compilationCondition .
compilationCondition = compilationCondition "||" compilationCondition .
compilationCondition = hardIdentifier functionCallArgumentClause .
```


### Grammar of a line control statement
_line-control-statement → **#sourceLocation** **(** **file**: file-path **,** **line**: line-number **)**_
_line-control-statement → **#sourceLocation** **(** **)**_
_line-number → A decimal integer greater than zero_
_file-path → static-string-literal_

```apus
lineNumber - /0*[1-9][0-9]*/ .

lineControlStatement = "#sourceLocation" "(" ")" .
lineControlStatement = "#sourceLocation" "(" "file" ":" filePath "," "line" ":" lineNumber ")" .

filePath = staticStringLiteral .
```


### Grammar of an availability condition
_availability-condition → **#available** **(** availability-arguments **)**_
_availability-condition → **#unavailable** **(** availability-arguments **)**_
_availability-arguments → availability-argument | availability-argument **,** availability-arguments_
_availability-argument → platform-name platform-version_
_availability-argument → **\***_
_platform-name → iOS | iOSApplicationExtension_
_platform-name → macOS | macOSApplicationExtension_
_platform-name → macCatalyst | macCatalystApplicationExtension_
_platform-name → watchOS | watchOSApplicationExtension_
_platform-name → tvOS | tvOSApplicationExtension_
_platform-name → visionOS | visionOSApplicationExtension_
_platform-version → decimal-digits_
_platform-version → decimal-digits **.** decimal-digits_
_platform-version → decimal-digits **.** decimal-digits **.** decimal-digits_

```apus
availabilityCondition = "#available" "(" availabilityArguments ")" .
availabilityCondition = "#unavailable" "(" availabilityArguments ")" .
availabilityArguments = availabilityArgument { "," availabilityArgument } .
availabilityArgument = platformName platformVersion? .
availabilityArgument = "*" .

platformName = hardIdentifier .
platformVersion = decimalDigits .
platformVersion = decimalDigits "." >n< decimalDigits .
platformVersion = decimalDigits "." >n< decimalDigits "." >n< decimalDigits .
```


## Declarations

### Grammar of a declaration
_declaration → import-declaration_
_declaration → constant-declaration_
_declaration → variable-declaration_
_declaration → typealias-declaration_
_declaration → function-declaration_
_declaration → enum-declaration_
_declaration → struct-declaration_
_declaration → class-declaration_
_declaration → actor-declaration_
_declaration → protocol-declaration_
_declaration → initializer-declaration_
_declaration → deinitializer-declaration_
_declaration → extension-declaration_
_declaration → subscript-declaration_
_declaration → macro-declaration_
_declaration → operator-declaration_
_declaration → precedence-group-declaration_

```apus
declaration = importDeclaration .
declaration = constantDeclaration .
declaration = variableDeclaration .
declaration = typealiasDeclaration .
declaration = functionDeclaration .
declaration = enumDeclaration .
declaration = structDeclaration .
declaration = classDeclaration .
declaration = actorDeclaration .
declaration = protocolDeclaration .
declaration = initializerDeclaration .
declaration = bodylessInitializerDeclaration .
declaration = deinitializerDeclaration .
declaration = extensionDeclaration .
declaration = subscriptDeclaration .
declaration = macroDeclaration .
declaration = operatorDeclaration .
declaration = precedenceGroupDeclaration .
declaration = associatedTypeDeclaration .
declaration = usingDeclaration .
memberDeclaration = declaration | freestandingMacroExpansionDeclaration .
declaration = @confinedTo(memberDeclaration) enumCaseDeclaration .
declaration = macroExpansionDeclaration .

macroExpansionDeclaration = attributes declarationModifiers? macroHead genericArgumentClause? [ >n< functionCallArgumentClause ] trailingClosures? .
macroExpansionDeclaration = declarationModifiers macroHead genericArgumentClause? [ >n< functionCallArgumentClause ] trailingClosures? .
freestandingMacroExpansionDeclaration = macroHead genericArgumentClause? [ >n< functionCallArgumentClause ] trailingClosures? .
poundName - @builder .
macroHead = poundName ---( "#_" "#available" "#unavailable" "#if" "#elseif" "#else" "#endif" "#sourceLocation" ) .
macroHead = "#" >s< propertyWrapperProjection .
macroHead = "#" >s< moduleSelector identifier ---( "_" ) .

usingDeclaration = "using" >n< ( attribute | softIdentifier ) .
```


### Grammar of a code block
_code-block → **{** statements? **}**_

```apus
codeBlock = "{" statements? "}" .
```


### Grammar of an import declaration
_import-declaration → attributes? **import** import-kind? import-path_
_import-kind → **typealias** | **struct** | **class** | **enum** | **protocol** | **let** | **var** | **func**_
_import-path → identifier | identifier **.** import-path_

```apus
importDeclaration = attributes? declarationModifiers? "import" importKind? importPath .
importDeclaration = attributes? "import" importKind moduleSelector ( hardIdentifier | operatorName ) .

importKind = "typealias" | "struct" | "class" | "enum" | "protocol" | "let" | "var" | "func" .
importPath = hardIdentifier { "." hardIdentifier } .
```


### Grammar of a constant declaration
_constant-declaration → attributes? declaration-modifiers? **let** pattern-initializer-list_
_pattern-initializer-list → pattern-initializer | pattern-initializer **,** pattern-initializer-list_
_pattern-initializer → pattern initializer?_
_initializer → **=** expression_

```apus
constantDeclaration = attributes? declarationModifiers? "let" patternInitializerList .

patternInitializerList = patternInitializer { "," patternInitializer } .

patternInitializer = bindingPattern initializer? .
patternInitializer = bindingPattern initializer? initializedAccessorBlock .
initializer = assignmentOperator expression .
```


### Grammar of a variable declaration
_variable-declaration → variable-declaration-head pattern-initializer-list_
_variable-declaration → variable-declaration-head variable-name type-annotation code-block_
_variable-declaration → variable-declaration-head variable-name type-annotation getter-setter-block_
_variable-declaration → variable-declaration-head variable-name type-annotation getter-setter-keyword-block_
_variable-declaration → variable-declaration-head variable-name initializer willSet-didSet-block_
_variable-declaration → variable-declaration-head variable-name type-annotation initializer? willSet-didSet-block_
_variable-declaration-head → attributes? declaration-modifiers? **var**_
_variable-name → identifier_
_getter-setter-block → code-block_
_getter-setter-block → **{** getter-clause setter-clause? **}**_
_getter-setter-block → **{** setter-clause getter-clause **}**_
_getter-clause → attributes? mutation-modifier? **get** code-block_
_setter-clause → attributes? mutation-modifier? **set** setter-name? code-block_
_setter-name → **(** identifier **)**_
_getter-setter-keyword-block → **{** getter-keyword-clause setter-keyword-clause? **}**_
_getter-setter-keyword-block → **{** setter-keyword-clause getter-keyword-clause **}**_
_getter-keyword-clause → attributes? mutation-modifier? **get**_
_setter-keyword-clause → attributes? mutation-modifier? **set**_
_willSet-didSet-block → **{** willSet-clause didSet-clause? **}**_
_willSet-didSet-block → **{** didSet-clause willSet-clause? **}**_
_willSet-clause → attributes? **willSet** setter-name? code-block_
_didSet-clause → attributes? **didSet** setter-name? code-block_

```apus
variableDeclaration = variableDeclarationHead patternInitializerList .
variableDeclaration = variableDeclarationHead variableName initializer willSetDidSetBlock .
variableDeclaration = variableDeclarationHead variableName typeAnnotation initializer? willSetDidSetBlock .

variableDeclarationHead = attributes? declarationModifiers? "var" .
variableName = hardIdentifier | "_" .

getterSetterBlock = codeBlock .
accessorBlockBrace = "{" accessorClauseList "}" .
getterSetterBlock = @prefer accessorBlockBrace .

initializedAccessorBlock = @cannotParse(accessorBlockBrace willSetDidSetBlock) codeBlock .
initializedAccessorBlock = @prefer "{" accessorClauseListNoInit "}" .
initializedAccessorBlock = @prefer "{" initAccessorClause accessorClauseList? "}" .

initializedAccessorBlock = @cannotParse(accessorBlockBrace) accessorBlockBrace .

accessorClauseListNoInit = accessorClauseEntryNoInit accessorClauseListNoInit? .
accessorClauseEntryNoInit = getterClause | setterClause | coroutineAccessorClause .

getterClause = attributes? accessorModifiers? "get" accessorEffects? codeBlock? .
setterClause = attributes? accessorModifiers? "set" setterName? accessorEffects? codeBlock? .
setterName = "(" hardIdentifier ")" .

accessorClauseList = accessorClauseEntry accessorClauseList? .
accessorClauseEntry = getterClause | setterClause | initAccessorClause | coroutineAccessorClause .
initAccessorClause = attributes? "init" setterName? accessorEffects? codeBlock .
coroutineAccessorClause = attributes? accessorModifiers? coroutineSpecifier accessorEffects? codeBlock .
coroutineSpecifier = "_read" | "read" | "_modify" | "modify" | "borrow" | "mutate" .

accessorModifiers = accessorModifier accessorModifiers? .
accessorModifier = "__consuming" | "consuming" | "borrowing" | "mutating" | "nonmutating" | "yielding" .

willSetDidSetBlock = "{" willSetClause didSetClause? "}"
                   | "{" didSetClause willSetClause? "}" .

willSetClause = attributes? "willSet" setterName? accessorEffects? codeBlock .
didSetClause = attributes? "didSet" setterName? accessorEffects? codeBlock .

accessorEffects = "throws" | "async" "throws"? .
```


### Grammar of a type alias declaration
_typealias-declaration → attributes? access-level-modifier? **typealias** typealias-name generic-parameter-clause? typealias-assignment_
_typealias-name → identifier_
_typealias-assignment → **=** type_

```apus
typealiasDeclaration = attributes? declarationModifiers? "typealias" typealiasName genericParameterClause? typealiasAssignment .
typealiasName = hardIdentifier .
typealiasAssignment = assignmentOperator type .
```


### Grammar of a function declaration
_function-declaration → function-head function-name generic-parameter-clause? function-signature generic-where-clause? function-body?_
_function-head → attributes? declaration-modifiers? **func**_
_function-name → identifier | **operator**_
_function-signature → parameter-clause **async**? throws-clause? function-result?_
_function-signature → parameter-clause **async**? **rethrows** function-result?_
_function-result → **->** attributes? type_
_function-body → code-block_
_parameter-clause → **(** **)** | **(** parameter-list ,? **)**_
_parameter-list → parameter | parameter **,** parameter-list_
_parameter → external-parameter-name? local-parameter-name parameter-type-annotation default-argument-clause?_
_parameter → external-parameter-name? local-parameter-name parameter-type-annotation_
_parameter → external-parameter-name? local-parameter-name parameter-type-annotation **...**_
_external-parameter-name → identifier_
_local-parameter-name → identifier_
_parameter-type-annotation → **:** attributes? parameter-modifier? type_
_parameter-modifier → **inout** | **borrowing** | **consuming** default-argument-clause → **=** expression_

```apus
@longest
functionDeclaration = functionHead functionName genericParameterClause? functionSignature genericWhereClause? functionBody? .

functionHead = attributes? declarationModifiers? "func" .
functionName = hardIdentifier | functionNameOperator | "&" .

functionSignature = parameterClause functionAsyncSpecifier? declarationThrowsClause? functionResult? .
functionAsyncSpecifier = "async" | "reasync" .
functionResult = "->" resultType .
functionBody = codeBlock .

parameterClause = "(" ")" | "(" parameterList ","? ")" .
parameterList = parameter { "," parameter } .

parameter = attributes? @shortest [ parameterDeclarationModifiers ] parameterNames typeAnnotation defaultArgumentClause? .
parameter = attributes? [ parameterDeclarationModifiers ] parameterNames typeAnnotation "..." .

parameterNames = externalParameterName localParameterName | localParameterName .
externalParameterName = softIdentifier | "_" .
localParameterName = softIdentifier | "_" .
```

```apus
parameterModifiers = parameterModifier parameterModifiers? .

parameterModifier = "inout" | "borrowing" | "consuming" | "isolated" | "_const" | "sending" | "__shared" | "__owned" .

parameterModifier = parenthesisedTypeSpecifier .
parenthesisedTypeSpecifier = "nonisolated" >s< "(" "nonsending" ")" .
```

```apus
parenthesisedTypeSpecifier = "dependsOn" >s< "(" "scoped"? lifetimeSpecifierArgument { "," lifetimeSpecifierArgument } ")" .
lifetimeSpecifierArgument = hardIdentifier | "self" | integerLiteral .

parameterDeclarationModifiers = parameterDeclarationModifier parameterDeclarationModifiers? .

parameterDeclarationModifier = "_const" | "isolated" .

defaultArgumentClause = assignmentOperator expression .
```


### Grammar of an enumeration declaration
_enum-declaration → attributes? access-level-modifier? union-style-enum_
_enum-declaration → attributes? access-level-modifier? raw-value-style-enum_
_union-style-enum → **indirect**? **enum** enum-name generic-parameter-clause? type-inheritance-clause? generic-where-clause? **{** union-style-enum-members? **}**_
_union-style-enum-members → union-style-enum-member union-style-enum-members?_
_union-style-enum-member → declaration | union-style-enum-case-clause | compiler-control-statement_
_union-style-enum-case-clause → attributes? **indirect**? **case** union-style-enum-case-list_
_union-style-enum-case-list → union-style-enum-case | union-style-enum-case **,** union-style-enum-case-list_
_union-style-enum-case → enum-case-name tuple-type?_
_enum-name → identifier_
_enum-case-name → identifier_
_raw-value-style-enum → **enum** enum-name generic-parameter-clause? type-inheritance-clause generic-where-clause? **{** raw-value-style-enum-members **}**_
_raw-value-style-enum-members → raw-value-style-enum-member raw-value-style-enum-members?_
_raw-value-style-enum-member → declaration | raw-value-style-enum-case-clause | compiler-control-statement_
_raw-value-style-enum-case-clause → attributes? **case** raw-value-style-enum-case-list_
_raw-value-style-enum-case-list → raw-value-style-enum-case | raw-value-style-enum-case **,** raw-value-style-enum-case-list_
_raw-value-style-enum-case → enum-case-name raw-value-assignment?_
_raw-value-assignment → **=** raw-value-literal_
_raw-value-literal → numeric-literal | static-string-literal | boolean-literal_

```apus
enumDeclaration = attributes? declarationModifiers? "enum" enumName genericParameterClause? typeInheritanceClause? genericWhereClause? "{" enumMembers? "}" .
enumMembers = enumMember ";"? .
enumMembers = enumMember statementSeparator enumMembers .
enumMember = memberDeclaration | compilerControlStatement .

associatedValues = "(" enumCaseParameterList? ")" .

enumCaseParameterList = enumCaseParameter { "," enumCaseParameter } .

enumCaseParameter = type defaultArgumentClause? .
enumCaseParameter = parameterModifiers? externalArgumentLabel? localArgumentLabel typeAnnotation defaultArgumentClause? .

enumName = hardIdentifier .
enumCaseName = hardIdentifier .

enumCaseDeclaration = attributes? "indirect"? "case" enumCaseElementList .

enumCaseElementList = enumCaseElement { "," enumCaseElement } .

enumCaseElement = enumCaseName associatedValues? enumCaseRawValueInitializer? .
enumCaseRawValueInitializer = assignmentOperator expression .
```


### Grammar of a structure declaration
_struct-declaration → attributes? access-level-modifier? **struct** struct-name generic-parameter-clause? type-inheritance-clause? generic-where-clause? struct-body_
_struct-name → identifier_
_struct-body → **{** struct-members? **}**_
_struct-members → struct-member struct-members?_
_struct-member → declaration | compiler-control-statement_

```apus
structDeclaration = attributes? declarationModifiers? "struct" structName genericParameterClause? typeInheritanceClause? genericWhereClause? structBody .
structName = hardIdentifier .
structBody = "{" structMembers? "}" .

structMembers = structMember ";"? .
structMembers = structMember statementSeparator structMembers .
structMember = memberDeclaration | compilerControlStatement .
```


### Grammar of a class declaration
_class-declaration → attributes? access-level-modifier? **final**? **class** class-name generic-parameter-clause? type-inheritance-clause? generic-where-clause? class-body_
_class-declaration → attributes? **final** access-level-modifier? **class** class-name generic-parameter-clause? type-inheritance-clause? generic-where-clause? class-body_
_class-name → identifier_
_class-body → **{** class-members? **}**_
_class-members → class-member class-members?_
_class-member → declaration | compiler-control-statement_

```apus
classDeclaration = attributes? declarationModifiers? "class" className genericParameterClause? typeInheritanceClause? genericWhereClause? classBody .
className = hardIdentifier .
classBody = "{" classMembers? "}" .

classMembers = classMember ";"? .
classMembers = classMember statementSeparator classMembers .
classMember = memberDeclaration | compilerControlStatement .
```


### Grammar of an actor declaration
_actor-declaration → attributes? access-level-modifier? **actor** actor-name generic-parameter-clause? type-inheritance-clause? generic-where-clause? actor-body_
_actor-name → identifier_
_actor-body → **{** actor-members? **}**_
_actor-members → actor-member actor-members?_
_actor-member → declaration | compiler-control-statement_

```apus
actorDeclaration = attributes? declarationModifiers? "actor" actorName genericParameterClause? typeInheritanceClause? genericWhereClause? actorBody .
actorName = hardIdentifier .
actorBody = "{" actorMembers? "}" .

actorMembers = actorMember ";"? .
actorMembers = actorMember statementSeparator actorMembers .
actorMember = memberDeclaration | compilerControlStatement .
```


### Grammar of a protocol declaration
_protocol-declaration → attributes? access-level-modifier? **protocol** protocol-name type-inheritance-clause? generic-where-clause? protocol-body_
_protocol-name → identifier_
_protocol-body → **{** protocol-members? **}**_
_protocol-members → protocol-member protocol-members?_
_protocol-member → protocol-member-declaration | compiler-control-statement_
_protocol-member-declaration → protocol-property-declaration_
_protocol-member-declaration → protocol-method-declaration_
_protocol-member-declaration → protocol-initializer-declaration_
_protocol-member-declaration → protocol-subscript-declaration_
_protocol-member-declaration → protocol-associated-type-declaration_
_protocol-member-declaration → typealias-declaration_


### Grammar of a protocol property declaration
_protocol-property-declaration → variable-declaration-head variable-name type-annotation getter-setter-keyword-block_

### Grammar of a protocol method declaration
_protocol-method-declaration → function-head function-name generic-parameter-clause? function-signature generic-where-clause?_

### Grammar of a protocol initializer declaration
_protocol-initializer-declaration → initializer-head generic-parameter-clause? parameter-clause throws-clause? generic-where-clause?_
_protocol-initializer-declaration → initializer-head generic-parameter-clause? parameter-clause **rethrows** generic-where-clause?_

### Grammar of a protocol subscript declaration
_protocol-subscript-declaration → subscript-head subscript-result generic-where-clause? getter-setter-keyword-block_

### Grammar of a protocol associated type declaration
_protocol-associated-type-declaration → attributes? access-level-modifier? **associatedtype** typealias-name type-inheritance-clause? typealias-assignment? generic-where-clause?_

```apus
protocolDeclaration = attributes? declarationModifiers? "protocol" protocolName primaryAssociatedTypeClause? typeInheritanceClause? genericWhereClause? protocolBody .
protocolName = hardIdentifier .

primaryAssociatedTypeClause = openAngle primaryAssociatedTypeList ","? closeAngle .

primaryAssociatedTypeList = hardIdentifier { "," hardIdentifier } .

protocolBody = "{" protocolMembers? "}" .

protocolMembers = protocolMember ";"? .
protocolMembers = protocolMember statementSeparator protocolMembers .
protocolMember = memberDeclaration | compilerControlStatement .

associatedTypeDeclaration = attributes? declarationModifiers? "associatedtype" typealiasName typeInheritanceClause? typealiasAssignment? genericWhereClause? .
```


### Grammar of an initializer declaration
_initializer-declaration → initializer-head generic-parameter-clause? parameter-clause **async**? throws-clause? generic-where-clause? initializer-body_
_initializer-declaration → initializer-head generic-parameter-clause? parameter-clause **async**? **rethrows** generic-where-clause? initializer-body_
_initializer-head → attributes? declaration-modifiers? **init**_
_initializer-head → attributes? declaration-modifiers? **init** **?**_
_initializer-head → attributes? declaration-modifiers? **init** **!**_
_initializer-body → code-block_

```apus
initializerDeclaration = initializerHead genericParameterClause? parameterClause functionAsyncSpecifier? declarationThrowsClause? functionResult? genericWhereClause? initializerBody .
bodylessInitializerDeclaration = initializerHead genericParameterClause? parameterClause functionAsyncSpecifier? declarationThrowsClause? functionResult? genericWhereClause? .
initializerHead = attributes? declarationModifiers? "init" .
initializerHead = attributes? declarationModifiers? "init" optionalMark .
initializerHead = attributes? declarationModifiers? "init" forceMark .
initializerBody = codeBlock .
```


### Grammar of a deinitializer declaration
_deinitializer-declaration → attributes? **deinit** code-block_

```apus
deinitializerDeclaration = attributes? declarationModifiers? "deinit" "async"? codeBlock? .
```


### Grammar of an extension declaration
_extension-declaration → attributes? access-level-modifier? **extension** type-identifier type-inheritance-clause? generic-where-clause? extension-body_
_extension-body → **{** extension-members? **}**_
_extension-members → extension-member extension-members?_
_extension-member → declaration | compiler-control-statement_

```apus
extensionDeclaration = attributes? accessLevelModifier? "extension" ( typeIdentifier | arrayType | dictionaryType | optionalType | implicitlyUnwrappedOptionalType ) typeInheritanceClause? genericWhereClause? extensionBody .
extensionBody = "{" extensionMembers? "}" .

extensionMembers = extensionMember ";"? .
extensionMembers = extensionMember statementSeparator extensionMembers .
extensionMember = memberDeclaration | compilerControlStatement .
```


### Grammar of a subscript declaration
_subscript-declaration → subscript-head subscript-result generic-where-clause? code-block_
_subscript-declaration → subscript-head subscript-result generic-where-clause? getter-setter-block_
_subscript-declaration → subscript-head subscript-result generic-where-clause? getter-setter-keyword-block_
_subscript-head → attributes? declaration-modifiers? **subscript** generic-parameter-clause? parameter-clause_
_subscript-result → **->** attributes? type_

```apus
subscriptDeclaration = subscriptHead subscriptResult genericWhereClause? getterSetterBlock? .
subscriptHead = attributes? declarationModifiers? "subscript" genericParameterClause? parameterClause .
subscriptResult = "->" type .
```


### Grammar of a macro declaration
_macro-declaration → macro-head identifier generic-parameter-clause? macro-signature macro-definition? generic-where-clause_
_macro-head → attributes? declaration-modifiers? **macro**_
_macro-signature → parameter-clause macro-function-signature-result?_
_macro-function-signature-result → **->** type_
_macro-definition → **=** expression_

```apus
macroDeclaration = macroDeclarationHead hardIdentifier genericParameterClause? macroSignature macroDefinition? genericWhereClause? .
macroDeclarationHead = attributes? declarationModifiers? "macro" .
macroSignature = parameterClause macroFunctionSignatureResult? .
macroFunctionSignatureResult = "->" type .
macroDefinition = assignmentOperator expression .
```


### Grammar of an operator declaration
_operator-declaration → prefix-operator-declaration | postfix-operator-declaration | infix-operator-declaration_
_prefix-operator-declaration → **prefix** **operator** **operator**_
_postfix-operator-declaration → **postfix** **operator** **operator**_
_infix-operator-declaration → **infix** **operator** **operator** infix-operator-group?_
_infix-operator-group → **:** precedence-group-name_

```apus
operatorDeclaration = ( "prefix" | "postfix" | "infix" ) "operator" declaredOperator infixOperatorGroup? .

declaredOperator = operatorName | dotOperator | "&" .

infixOperatorGroup = ":" precedenceGroupName designatedTypes? .

designatedTypes = "," | "," designatedType designatedTypes? .

designatedType = identifier | escapedIdentifier | nonWordToken | literal | operator .
```


### Grammar of a precedence group declaration
_precedence-group-declaration → **precedencegroup** precedence-group-name **{** precedence-group-attributes? **}**_
_precedence-group-attributes → precedence-group-attribute precedence-group-attributes?_
_precedence-group-attribute → precedence-group-relation_
_precedence-group-attribute → precedence-group-assignment_
_precedence-group-attribute → precedence-group-associativity_
_precedence-group-relation → **higherThan** **:** precedence-group-names_
_precedence-group-relation → **lowerThan** **:** precedence-group-names_
_precedence-group-assignment → **assignment** **:** boolean-literal_
_precedence-group-associativity → **associativity** **:** **left**_
_precedence-group-associativity → **associativity** **:** **right**_
_precedence-group-associativity → **associativity** **:** **none**_
_precedence-group-names → precedence-group-name | precedence-group-name **,** precedence-group-names_
_precedence-group-name → identifier_

```apus
precedenceGroupDeclaration = "precedencegroup" precedenceGroupName "{" precedenceGroupAttributes? "}" .

precedenceGroupAttributes = precedenceGroupAttribute precedenceGroupAttributes? .
precedenceGroupAttribute = precedenceGroupRelation .
precedenceGroupAttribute = precedenceGroupAssignment .
precedenceGroupAttribute = precedenceGroupAssociativity .

precedenceGroupRelation = "higherThan" ":" precedenceGroupNames .
precedenceGroupRelation = "lowerThan" ":" precedenceGroupNames .

precedenceGroupAssignment = "assignment" ":" booleanLiteral .

precedenceGroupAssociativity = "associativity" ":" ( "left" | "right" | "none" ) .

precedenceGroupNames = precedenceGroupName { "," precedenceGroupName } .
precedenceGroupName = hardIdentifier .
```


### Grammar of a declaration modifier
_declaration-modifier → **class** | **convenience** | **dynamic** | **final** | **infix** | **lazy** | **optional** | **override** | **postfix** | **prefix** | **required** | **static** | **unowned** | **unowned** **(** **safe** **)** | **unowned** **(** **unsafe** **)** | **weak**_
_declaration-modifier → access-level-modifier_
_declaration-modifier → mutation-modifier_
_declaration-modifier → actor-isolation-modifier_
_declaration-modifiers → declaration-modifier declaration-modifiers?_
_access-level-modifier → **private** | **private** **(** **set** **)**_
_access-level-modifier → **fileprivate** | **fileprivate** **(** **set** **)**_
_access-level-modifier → **internal** | **internal** **(** **set** **)**_
_access-level-modifier → **package** | **package** **(** **set** **)**_
_access-level-modifier → **public** | **public** **(** **set** **)**_
_access-level-modifier → **open** | **open** **(** **set** **)**_
_mutation-modifier → **mutating** | **nonmutating**_
_actor-isolation-modifier → **nonisolated**_

```apus
declarationModifier = "class" | "convenience" | "dynamic" | "final" | "infix" | "lazy" | "optional" | "override" | "postfix" | "prefix" | "required" | "static" | "unowned" | "unowned" "(" "safe" ")" | "unowned" "(" "unsafe" ")" | "weak" .
declarationModifier = "async" | "borrowing" | "consuming" | "sending" | "distributed" | "reasync" | "indirect" | "isolated" .
declarationModifier = "_const" | "_local" | "__consuming" | "__setter_access" .
declarationModifier = accessLevelModifier .
declarationModifier = mutationModifier .
declarationModifier = actorIsolationModifier .

declarationModifiers = declarationModifier declarationModifiers? .

accessLevelModifier = "private" | "private" "(" "set" ")" .
accessLevelModifier = "fileprivate" | "fileprivate" "(" "set" ")" .
accessLevelModifier = "internal" | "internal" "(" "set" ")" .
accessLevelModifier = "package" | "package" "(" "set" ")" .
accessLevelModifier = "public" | "public" "(" "set" ")" .
accessLevelModifier = "open" .

mutationModifier = "mutating" | "nonmutating" .

actorIsolationModifier = "nonisolated" | "nonisolated" "(" "unsafe" ")" | "nonisolated" "(" "nonsending" ")" .
```


## Attributes

### Grammar of an attribute
_attribute → **@** attribute-name attribute-argument-clause?_
_attribute-name → identifier_
_attribute-argument-clause → **(** balanced-tokens? **)**_
_attributes → attribute attributes?_
_balanced-tokens → balanced-token balanced-tokens?_
_balanced-token → **(** balanced-tokens? **)**_
_balanced-token → **[** balanced-tokens? **]**_
_balanced-token → **{** balanced-tokens? **}**_
_balanced-token → **Any** identifier, keyword, literal, or **operator**_
_balanced-token → **Any** punctuation except (, ), [, ], {, or **}**_

```apus
attribute = "@" >s< "abi" >s< "(" abiDeclaration ")" .

abiDeclaration = associatedTypeDeclaration | deinitializerDeclaration | enumCaseDeclaration
               | functionDeclaration | initializerDeclaration | bodylessInitializerDeclaration
               | subscriptDeclaration
               | typealiasDeclaration | variableDeclaration | constantDeclaration .
```

```apus
attribute = "@" >s< "isolated" >s< "(" identifier ")" .
```

```apus
attribute = "@" >s< "attached"     >s< "(" macroRoleArguments? ")" .
attribute = "@" >s< "freestanding" >s< "(" macroRoleArguments? ")" .

attribute = availableAttribute .
```

```apus
availableAttribute = "@" >s< "available" >s< "(" availabilityAttributeArguments ")" .
availabilityAttributeArguments = availabilityAttributeArgument { "," availabilityAttributeArgument } .
availabilityAttributeArgument = "*" .
availabilityAttributeArgument = platformName platformVersion? .
availabilityAttributeArgument = availabilityLabel ":" availabilityValue .
availabilityLabel = hardIdentifier .
availabilityValue = platformVersion | availabilityStringLiteral | hardIdentifier .
availabilityStringLiteral = singleLineStringLiteral | multilineStringLiteral .
attribute = "@" >s< "convention" >s< "(" conventionArguments ")" .
conventionArguments = conventionArgument { "," conventionArgument } .
conventionArgument = hardIdentifier | hardIdentifier ":" conventionValue .
conventionValue = hardIdentifier | staticStringLiteral .

attribute = "@" >s< "objc" >s< "(" objcSelector ")" .
attribute = "@" >s< "objc" .
objcSelector = identifier .
objcSelector = objcSelectorPieces .
objcSelectorPieces = objcSelectorPiece objcSelectorPieces? .
objcSelectorPiece = identifier? ":" .

attribute = "@" >s< "derivative" >s< "(" "of" ":" derivativeName ")" .
attribute = "@" >s< "derivative" >s< "(" "of" ":" derivativeName "," differentiableWrt ")" .
attribute = "@" >s< "transpose" >s< "(" "of" ":" derivativeName ")" .
attribute = "@" >s< "transpose" >s< "(" "of" ":" derivativeName "," differentiableWrt ")" .

derivativeName      = derivativeNameChain | derivativeNameChain >s< "(" argumentNames? ")" .
derivativeNameChain = derivativeNameAtom
                    | derivativeNameChain "." >n< derivativeNameAtom
                    | derivativeNameChain >s< dotOperator .
derivativeNameAtom  = moduleSelector? hardIdentifier | moduleSelector? selfType | operator .
```

```apus
attribute = "@" >s< "lifetime" >s< "(" lifetimeArguments ")" .
lifetimeArguments = lifetimeArgument { "," lifetimeArgument } .
lifetimeArgument  = lifetimeTarget | hardIdentifier ":" lifetimeTarget .
lifetimeTarget    = hardIdentifier
                  | "borrow" hardIdentifier
                  | "copy" hardIdentifier
                  | "&" >s< hardIdentifier .
```

```apus
attribute = "@" >s< "backDeployed" >s< "(" "before" ":" backDeployedPlatforms ")" .
attribute = "@" >s< "_backDeploy" >s< "(" "before" ":" backDeployedPlatforms ")" .

attribute = "@" >s< "_effects" >s< "(" < effectsToken > ")" .
effectsToken  = identifier | escapedIdentifier | nonWordToken | literal | operator .
backDeployedPlatforms = backDeployedPlatform { "," backDeployedPlatform } .

attribute = "@" >s< "_originallyDefinedIn" >s< "(" "module" ":" staticStringLiteral "," originallyDefinedInPlatforms ")" .

attribute = "@" >s< "_documentation" >s< "(" documentationArguments ")" .

attribute = "@" >s< "_dynamicReplacement" >s< "(" "for" ":" attributeDeclName ")" .

attribute = "@" >s< "_implements" >s< "(" type "," attributeDeclName ")" .

attributeDeclName = moduleSelector? attributeDeclBase
                  | moduleSelector? attributeDeclBase >s< "(" argumentNames? ")" .
attributeDeclBase = hardIdentifier | escapedIdentifier | operator
                  | "init" | "deinit" | "subscript" | "self" | "Self" .
documentationArguments = documentationArgument { "," documentationArgument } .
documentationArgument  = "visibility" ":" documentationVisibility
                       | "metadata" ":" hardIdentifier
                       | "metadata" ":" staticStringLiteral .
documentationVisibility = "private" | "fileprivate" | "internal" | "package" | "public" | "open" .
originallyDefinedInPlatforms = originallyDefinedInPlatform { "," originallyDefinedInPlatform } .
originallyDefinedInPlatform  = platformName platformVersion? | "*" platformVersion? .
backDeployedPlatform  = platformName platformVersion? .
```

```apus
attribute = "@" >s< "differentiable" >s< "(" differentiableArguments ")" .
differentiableArguments = differentiableKind
                        | differentiableKind "," differentiableWrt
                        | differentiableWrt
                        | differentiableKind genericWhereClause
                        | differentiableKind "," differentiableWrt genericWhereClause
                        | differentiableWrt genericWhereClause .
differentiableKind = hardIdentifier .
differentiableWrt  = "wrt" ":" differentiabilityArgument
                   | "wrt" ":" "(" differentiabilityArgumentList ")" .

differentiabilityArgumentList = differentiabilityArgument { "," differentiabilityArgument } .

differentiabilityArgument = hardIdentifier | "self" | selfType | decimalDigits .
```

```apus
attribute = "@" >s< "specialized" >s< "(" genericWhereClause ")" .

attribute = "@" >s< "_specialize" >s< "(" specializeArguments? genericWhereClause? ")" .
specializeArguments = < specializeArgument > .
specializeArgument  = "target" ":" attributeDeclName ","?
                    | "availability" ":" availabilityAttributeArguments ";"
                    | "exported" ":" booleanLiteral ","?
                    | "kind" ":" hardIdentifier ","?
                    | "spi" ":" effectsToken ","?
                    | "spiModule" ":" effectsToken ","? .

attribute = "@"
            >-> ( "abi" "attached" "available" "convention" "freestanding" "isolated" "backDeployed" "derivative" "differentiable" "lifetime" "objc" "specialized" "transpose" "_originallyDefinedIn" "_documentation" "_dynamicReplacement" "_implements" "_backDeploy" "_effects" "_specialize" )
            >s< attributeName attributeArgumentExprClause? .

attribute = "@"
            >-> ( "abi" "attached" "available" "convention" "freestanding" "isolated" "backDeployed" "derivative" "differentiable" "lifetime" "objc" "specialized" "transpose" "_originallyDefinedIn" "_documentation" "_dynamicReplacement" "_implements" "_backDeploy" "_effects" "_specialize" )
            >s< moduleSelector attributeName attributeArgumentExprClause? .

attributeArgumentExprClause = >s< "(" functionCallArgumentList? ")" .

macroRoleArguments = macroRoleArgument { "," macroRoleArgument } .
macroRoleArgument  = macroRoleName | hardIdentifier ":" macroRoleName .

macroRoleName      = moduleSelector? macroRoleDeclName
                   | moduleSelector? macroRoleDeclName >s< "(" macroRoleName ")"
                   | moduleSelector? macroRoleDeclName >s< "(" argumentNames ")" .

macroRoleDeclName  = identifier
                     ---( "_" "Any" "as" "associatedtype" "await" "break" "case" "catch" "class" "continue" "default" "defer" "do" "else" "enum" "fallthrough" "false" "fileprivate" "for" "func" "guard" "if" "import" "in" "inout" "internal" "is" "let" "nil" "open" "operator" "precedencegroup" "private" "protocol" "public" "repeat" "rethrows" "return" "static" "struct" "super" "switch" "throw" "throws" "true" "try" "typealias" "var" "where" "while" )
                   | escapedIdentifier .

attributeName = attributeHeadName typeGenericArgumentClause?
              | attributeHeadName typeGenericArgumentClause? "." >n< typeIdentifier
              | "rethrows" .
attributeHeadName = hardIdentifier | selfType .

attributes = attribute attributes? .
attributes = conditionalCompilationAttributes attributes? .
conditionalCompilationAttributes = ifDirectiveAttributes elseifDirectiveAttributes? elseDirectiveAttributes? endifDirective .
ifDirectiveAttributes = ifDirective compilationCondition attributes? .
elseifDirectiveAttributes = elseifDirectiveAttributes elseifDirectiveAttributes? .
elseifDirectiveAttributes = elseifDirective compilationCondition attributes? .
elseDirectiveAttributes = elseDirective attributes? .

nonWordToken = "#available" | "#colorLiteral" | "#elseif" | "#else" | "#endif" | "#error" | "#fileLiteral" | "#if" | "#imageLiteral" | "#keyPath" | "#selector" | "#sourceLocation" | "#unavailable" | "#warning" | "." | "," | ":" | ";" | "=" | "&" | "?" | "!" | "_" | "@".
nonWordToken = "#" >-> ( singleLineStringLiteral multilineStringLiteral ) .
```


## Patterns

### Grammar of a pattern
_pattern → wildcard-pattern type-annotation?_
_pattern → identifier-pattern type-annotation?_
_pattern → value-binding-pattern_
_pattern → tuple-pattern type-annotation?_
_pattern → enum-case-pattern_
_pattern → optional-pattern_
_pattern → type-casting-pattern_
_pattern → expression-pattern_

```apus
bindingPattern = wildcardPattern typeAnnotation?
               | identifierPattern typeAnnotation?
               | tupleBindingPattern typeAnnotation? .

tupleBindingPattern = "(" tupleBindingElementList? ")" .

tupleBindingElementList = tupleBindingElement { "," tupleBindingElement } .

tupleBindingElement = bindingSubpattern | softIdentifier ":" bindingSubpattern .
bindingSubpattern = wildcardPattern | identifierPattern | tupleBindingPattern .
bindingSubpattern = ( "var" | "let" ) ( wildcardPattern | identifierPattern | tupleBindingPattern ) .
```

```apus
matchPattern = wildcardPattern
             | identifierPattern
             | valueBindingPattern
             | tupleMatchPattern
             | enumCasePattern
             | optionalPattern
             | typeCastingPattern
             | @prefer expressionPattern .
```


### Grammar of a wildcard pattern
_wildcard-pattern → **\_**_

```apus
wildcardPattern = "_" .
```


### Grammar of an identifier pattern
_identifier-pattern → identifier_

```apus
identifierPattern = hardIdentifier .
identifierPattern = @confinedTo(optionalBindingCondition) "self" .
```


### Grammar of a value-binding pattern
_value-binding-pattern → **var** pattern | **let** pattern_

```apus
valueBindingPattern = "var" matchPattern
                    | "let" matchPattern
                    | "inout" matchPattern
                    | "borrowing" >+> ( identifier "_" ) matchPattern .

valueBindingPattern = "_borrowing" >+> ( identifier "_" ) matchPattern
                    | "_consuming" matchPattern
                    | "_mutating" matchPattern .
```


### Grammar of a tuple pattern
_tuple-pattern → **(** tuple-pattern-element-list? **)**_
_tuple-pattern-element-list → tuple-pattern-element | tuple-pattern-element **,** tuple-pattern-element-list_
_tuple-pattern-element → pattern | identifier **:** pattern_

```apus
tupleMatchPattern = "(" tupleMatchElementList? ")" .

tupleMatchElementList = tupleMatchElement { "," tupleMatchElement } .

tupleMatchElement = matchPattern | softIdentifier ":" matchPattern .
```


### Grammar of an enumeration case pattern
_enum-case-pattern → type-identifier? **.** enum-case-name tuple-pattern?_

```apus
enumCasePattern = enumCaseName tupleMatchPattern .
enumCasePattern = typeIdentifier? "." >n< memberName tupleMatchPattern? .
```


### Grammar of an optional pattern
_optional-pattern → identifier-pattern **?**_

```apus
optionalPattern = ( identifierPattern | tupleMatchPattern ) >s< optionalMark .
```


### Grammar of a type casting pattern
_type-casting-pattern → is-pattern | as-pattern_
_is-pattern → **is** type_
_as-pattern → pattern **as** type_

```apus
typeCastingPattern = isPattern .
isPattern = "is" type .
```


### Grammar of an expression pattern
_expression-pattern → expression_

```apus
expressionPattern = expression .
```


## Generic Parameters and Arguments

### Grammar of a generic parameter clause
_generic-parameter-clause → < generic-parameter-list ,? **>**_
_generic-parameter-list → generic-parameter | generic-parameter **,** generic-parameter-list_
_generic-parameter → type-name_
_generic-parameter → type-name **:** type-identifier_
_generic-parameter → type-name **:** protocol-composition-type_
_generic-parameter → **let** type-name **:** type **\\**_
_generic-where-clause → **where** requirement-list_
_requirement-list → requirement | requirement **,** requirement-list_
_requirement → conformance-requirement | same-type-requirement_
_conformance-requirement → type-identifier **:** type-identifier_
_conformance-requirement → type-identifier **:** protocol-composition-type_
_same-type-requirement → type-identifier **==** type_
_same-type-requirement → type-identifier **==** signed-integer-literal_

```apus
genericParameterClause  = openAngle genericParameterList genericWhereClause? ","? closeAngle .

genericParameterList = genericParameter { "," genericParameter } .
```

```apus
genericParameter = attributes? "each"? typeName .
genericParameter = attributes? "each"? typeName ":" "~"? >-> ( "Self" ) typeIdentifier .
genericParameter = attributes? "each"? typeName ":" "~"? protocolCompositionType .
genericParameter = attributes? "let" typeName ":" type .

genericWhereClause = "where" requirementList .
requirementList = requirement { "," requirement } .

requirement = conformanceRequirement | sameTypeRequirement | layoutRequirement .

conformanceRequirement = type ":" "~"? conformanceRequirementRHS .
conformanceRequirementRHS = >-> ( "_Trivial" "_TrivialAtMost" "_TrivialStride"
                                  "_UnknownLayout" "_RefCountedObject" "_NativeRefCountedObject"
                                  "_Class" "_NativeClass" "_BridgeObject" )
                          ( typeIdentifier | protocolCompositionType ) .
sameTypeRequirement    = type "==" ( type | signedIntegerLiteral ) .
layoutRequirement      = type ":" layoutSpecifier layoutRequirementArguments? .
layoutSpecifier        = "_Trivial" | "_TrivialAtMost" | "_TrivialStride"
                       | "_UnknownLayout" | "_RefCountedObject" | "_NativeRefCountedObject"
                       | "_Class" | "_NativeClass" | "_BridgeObject" .
layoutRequirementArguments = "(" integerLiteral ( "," integerLiteral )? ")" .
```


### Grammar of a generic argument clause
_generic-argument-clause → < generic-argument-list ,? **>**_
_generic-argument-list → generic-argument | generic-argument **,** generic-argument-list_
_generic-argument → type | signed-integer-literal_

```apus
genericArgumentClause = openAngle genericArgumentList ","? closeAngle
                        >+> ( "(" ")" "[" "]" "{" "}" "," ";" ":" "." keyPathDot "?" "!" "&" EOF ) .

typeGenericArgumentClause = openAngle genericArgumentList ","? closeAngle .

genericArgumentList = genericArgument { "," genericArgument } .
genericArgument =
    | type
    | signedIntegerLiteral
    | parenthesizedExpression
    .
```
