{
module Act.Lex
  ( LEX (..)
  , Lexeme (..)
  , AlexPosn (..)
  , lexer
  , posn
  , showposn
  , name
  , value
  , nowhere
  , lastPos
  ) where

import Prelude hiding (EQ, GT, LT)

}

%wrapper "posn"

$digit = 0-9                    -- digits
$alpha = [a-z A-Z]              -- alphabetic characters
$ident = [$alpha _]
$space = [\ \t\f\v\r]
$negative = \-

tokens :-

  $white+                               ;

  -- reserved words
  contract                              { mk CONTRACT }
  constructor                           { mk CONSTRUCTOR }
  transition                            { mk TRANSITION }
  of                                    { mk OF }
  creates                               { mk CREATES }
  case                                  { mk CASE }
  returns                               { mk RETURNS }
  updates                               { mk UPDATES }
  noop                                  { mk NOOP }

  iff $white+ in $white+ range          { mk IFFINRANGE }
  inRange                               { mk INRANGE }
  iff                                   { mk IFF }
  and                                   { mk AND }
  not                                   { mk NOT }
  or                                    { mk OR }
  true                                  { mk TRUE }
  false                                 { mk FALSE }
  new                                   { mk NEW }
  as                                    { mk AS }
  mapping                               { mk MAPPING }
  ensures                               { mk ENSURES }
  invariants                            { mk INVARIANTS }
  if                                    { mk IF }
  then                                  { mk THEN }
  else                                  { mk ELSE }
  at                                    { mk AT }
  pre                                   { mk PRE }
  post                                  { mk POST }
  with                                  { mk WITH }
  value                                 { mk VALUE }
  payable                               { mk PAYABLE }
  -- builtin types
  uint $digit+                          { \ p s -> L (UINT (read (drop 4 s))) p }
  int  $digit+                          { \ p s -> L (INT  (read (drop 3 s))) p }
  uint                                  { mk (UINT 256) }
  int                                   { mk (INT 256) }
  bytes $digit+                         { \ p s -> L (BYTES (read (drop 5 s))) p }
  bytes                                 { error "TODO" }
  address                               { mk ADDRESS }
  bool                                  { mk BOOL }
  string                                { mk STRING }
  address(0)                            { mk ADDR0 }
  -- builtin functions
  newAddr                               { mk NEWADDR }

  -- environment vars
  CALLER                                { mk CALLER }
  CALLVALUE                             { mk CALLVALUE }
  CALLDEPTH                             { mk CALLDEPTH }
  ORIGIN                                { mk ORIGIN }
  BLOCKHASH                             { mk BLOCKHASH }
  BLOCKNUMBER                           { mk BLOCKNUMBER }
  DIFFICULTY                            { mk DIFFICULTY }
  CHAINID                               { mk CHAINID }
  GASLIMIT                              { mk GASLIMIT }
  COINBASE                              { mk COINBASE }
  TIMESTAMP                             { mk TIMESTAMP }
  THIS                                  { mk THIS }  -- normally called address, but that's taken
  NONCE                                 { mk NONCE } -- technically not an opcode

  -- symbols
  ":="                                  { mk ASSIGN }
  "==>"                                 { mk ARROW }
  "=>"                                  { mk MAPSTO }
  "=="                                  { mk EQEQ }
  "!="                                  { mk NEQ }
  ">="                                  { mk GE }
  "<="                                  { mk LE }
  "++"                                  { mk CAT }
  ".."                                  { mk SLICE }
  "("                                   { mk LPAREN }
  ")"                                   { mk RPAREN }
  "["                                   { mk LBRACK }
  "]"                                   { mk RBRACK }
  "{"                                   { mk LBRACE }
  "}"                                   { mk RBRACE }
  "="                                   { mk Act.Lex.EQ }
  ">"                                   { mk Act.Lex.GT }
  "<"                                   { mk Act.Lex.LT }
  ":"                                   { mk COLON }
  "+"                                   { mk PLUS }
  "-"                                   { mk MINUS }
  "*"                                   { mk STAR }
  "/"                                   { mk SLASH }
  "%"                                   { mk MOD }
  "^"                                   { mk CARET }
  "_"                                   { mk SCORE }
  "."                                   { mk DOT }
  ","                                   { mk COMMA }
  "//"                                  [.]* ; -- Toss single line comments
  -- identifiers
  $ident ($ident | $digit)*             { \ p s -> L (ID s) p }

  -- literals
  $negative? $digit+                    { \ p s -> L (ILIT (read s)) p }

{

data LEX =

  -- reserved words
    CONTRACT
  | CONSTRUCTOR
  | TRANSITION
  | OF
  | CREATES
  | CASE
  | RETURNS
  | UPDATES
  | NOOP
  | IFFINRANGE
  | INRANGE
  | IFF
  | POINTERS
  | MAPSTO
  | AND
  | NOT
  | OR
  | TRUE
  | FALSE
  | CREATE
  | AS
  | MAPPING
  | ENSURES
  | INVARIANTS
  | IF
  | THEN
  | ELSE
  | AT
  | PRE
  | POST
  | PAYABLE
  | VALUE
  | NEW
  | WITH
  | ADDR0
  -- builtin types
  | UINT  Int
  | INT   Int
  | BYTES Int
  | ADDRESS
  | BOOL
  | STRING

  -- builtin functions
  | NEWADDR

  -- environment vars
  | CALLER
  | CALLVALUE
  | CALLDEPTH
  | ORIGIN
  | BLOCKHASH
  | BLOCKNUMBER
  | DIFFICULTY
  | CHAINID
  | GASLIMIT
  | COINBASE
  | TIMESTAMP
  | THIS
  | NONCE

  -- symbols
  | ASSIGN
  | ARROW
  | EQEQ
  | NEQ
  | GE
  | LE
  | CAT
  | SLICE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | LBRACE
  | RBRACE
  | EQ
  | GT
  | LT
  | COLON
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | MOD
  | CARET
  | SCORE
  | DOT
  | COMMA

  -- identifiers
  | ID String

  -- literals
  | ILIT Integer

  deriving (Eq, Show)

data Lexeme = L LEX AlexPosn
  deriving (Eq, Show)

-- annoying that we can't override the show instance for this here
showposn (AlexPn _ line column) =
  concat [show line, ":", show column]

posn :: Lexeme -> AlexPosn
posn (L _ p) = p

nowhere :: AlexPosn
nowhere = AlexPn 0 0 0

lastPos :: AlexPosn
lastPos = AlexPn (-1) (-1) (-1)

name :: Lexeme -> String
name (L (ID s) _) = s
name _ = error "unsupported arg to name"

value :: Lexeme -> Integer
value (L (ILIT i) _) = i
value _ = error "unsupported arg to value"

-- helper function to reduce boilerplate
mk :: LEX -> (AlexPosn -> String -> Lexeme)
mk lexeme p _ = L lexeme p

lexer :: String -> [Lexeme]
lexer = alexScanTokens
}
