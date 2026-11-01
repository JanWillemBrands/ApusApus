```apus
Book = { Import } { TLD } .

Whitespace  : /\s+/ .
Comment     : /#.*/ .

CHAR    - /'([^'\\\n]|\\.)'/ .
STRING  - /"[^"\\]*(?:\\.[^"\\]*)*"/ .
F32Lit  - /[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?(?![a-zA-Z0-9._-])/ .
NatSucc - /[0-9]+n\+/ .
NatLit  - /[0-9]+n(?![a-zA-Z0-9._-])/ .
U32Lit  - /[0-9]+(?![a-zA-Z0-9._-])/ .
Name    - /[a-zA-Z_][a-zA-Z0-9._-]*/ .

FilePath    - /\.\/[a-zA-Z0-9_-]+\.bend/ .
PackagePath - /[a-zA-Z0-9_-]+(@[0-9.]+)?\/[a-zA-Z0-9_-]+\.bend/ .
HashPath    - /0x[a-fA-F0-9]+\/[a-zA-Z0-9_-]+\.bend/ .

Quant = [ "-" | "+" ] .

Bind =
    | Quant Name ":" Term
    | "~" Name ":" Term
    | Name
    .

Term =
    | Var
    | Ref
    | Ann
    | Typ
    | Qnt
    | Qua
    | Min
    | All
    | Lam
    | App
    | Fill
    | CtrTerm
    | Mat
    | Efq
    | Eql
    | Rfl
    | Rwt
    | Hol
    | Grp

    | DoBlock

    | Lit
    | Nat
    | Plus
    | Arrow
    | Exists
    | Pair
    | Or
    | Not
    | Tuple
    | List
    | Cons
    | Array
    | Index
    | Op
    .

Var = Name .

Ref = Name .

Ann = "{" Term ":" Term "}" .

Typ = "Type" | "Data" | "Kind" "(" Term ")" .

Qnt = "Quant" .

Qua = "&0" | "&1" | "&2" .

Min = Term "<&>" Term .

All = "@" Bind "->" Term .

Lam = Name "=>" Block .

App = Term "(" { Term ","? } ")" .

Fill = Name "<" { Term ","? } ">" .

CtrTerm = Name "{" { Term ","? } "}" .

Mat = "\\" "{" Name ":" Term ";"? Term "}" .

Efq = "\\" "{" "}" .

Eql = "{" Term "==" Term ":" Term "}" .

Rfl = "{" "==" "}" .

Rwt = "%" [ Name "@" ] Term ":" Term ";"? Body .

Hol = "?" Name .

Grp = "(" Body ")" .

U32    = U32Lit .
F32    = F32Lit .
Chr    = CHAR .
Str    = STRING .
Lit    = U32 | F32 | Chr | Str .
Nat    = NatSucc Term | NatLit .
Plus   = "+" Name [ "<" { Term ","? } ">" ] .
Arrow  = Term "->" Term .
Exists = "&" Name ":" Term "->" Term .
Pair   = Term "&" Term .
Or     = Term "|" Term .
Not    = "{" Term "!=" Term ":" Term "}" .
Tuple  = "(" Term "," Term { "," Term } ","? ")" .
List   = "[" { Term ","? } "]" .
Cons   = Term "<>" Term .
Array  = "[" Term ":" Term ( "*" | "^" ) Term "]" .
Index  = Term "[" Term "]" [ "<-" Term ] .
Op     = Term ( "||" | "&&" | "++" ) Term
       | "(" OpExpr ":" Term ")" .
OpExpr = Term OpSymbol Term { OpSymbol Term } .
OpSymbol = "<" | "<=" | ">" | ">="
         | ".|." | ".^." | ".&." | "<<" | ">>"
         | "+" | "-" | "*" | "/" | "%" .
```

```apus
Case    = "case" { Term } ":" Block .
Match   = "match" { Term } ":" ( >n< Case+
                               | <n> >>| Case+ |<<
                               ) .
Local   = < Quant Name | Term > "=" Term+ ( ";" | <n> ) Body .
Reply   = Term .
Body    = Match | Local | Reply .
Block   = >n< Body
        | <n> >>| Body |<<
        .
CtrDecl = Name "{" { Bind ","? } "}" .
ADTDecl = "type" Name [ "<" { Bind ","? } ">" ] "is" Term ":" [ >n< < CtrDecl >
                                                              | <n> >>| < CtrDecl <n> > |<<
                                                              ] .
Clause  = ( "for" ( Quant | "~" ) | "exs" ) Name ":" Term [ "where" Term ] .
Law     = "law" Name ":" ( >n< { Clause } Body
                         | <n> >>| { Clause <n> } Body |<<
                         ) .
Def     = [ "@unsafe" ] "def" Name "?"? "(" { Bind ","? } ")" [ "->" Term ] ":" ( Block | < "import" STRING > ) .
TLD     = ADTDecl | Law | Def .
Import  = "import" "Base" | "import" Path "as" Name .
Path    = FilePath | PackagePath | HashPath .
```

```apus
 DoBlock = "do" Name "<" { Term ","? } ">" ":" DoLayout .
 DoLayout = >n< DoStmt
          | <n> >>| DoStmt |<<
          .

 DoStmt =
    | DoLet
    | DoExec
    | DoBind
    | DoStep
    | DoPure
    | DoRetr
    .

DoLet  = Name ":" Term "=" Term ";"? DoStmt .
DoExec = Term "<-" Term ";"? DoStmt .
DoBind = Name ":" Term "<-" Term ";"? DoStmt .
DoStep = Term ( ";" | <n> ) DoStmt .
DoPure = "return" Term .
DoRetr = Term .
```
