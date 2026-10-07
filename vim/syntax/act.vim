" Vim syntax file
" Language: Act (formal specification language for EVM smart contracts)
" Maintainer: Act contributors
" Latest Revision: 2026-03-16

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword actTopLevel       contract constructor transition behaviour
syn keyword actBlock          creates updates invariants ensures interface pointers storage
syn keyword actClause         iff returns case of

" Modifiers
syn keyword actModifier       payable

" Control flow
syn keyword actConditional    if then else

" Logical operators (word-form)
syn keyword actLogical        and or not

" Boolean literals
syn keyword actBoolean        true false

" Built-in types
syn keyword actType           uint uint8 uint16 uint32 uint64 uint128 uint192 uint256
syn keyword actType           int int8 int16 int32 int56 int64 int128 int192 int256
syn keyword actType           bool address string bytes bytes32 mapping

" Object creation
syn keyword actKeyword        new create pre post

" Built-in functions
syn match   actBuiltin        /\<inRange\>/
syn match   actBuiltin        /\<address\ze(/

" Environment variables
syn keyword actEnvironment    CALLER CALLVALUE BALANCE THIS CALLDEPTH ORIGIN
syn keyword actEnvironment    BLOCKHASH BLOCKNUMBER DIFFICULTY CHAINID
syn keyword actEnvironment    GASLIMIT COINBASE TIMESTAMP NONCE

" Operators
syn match   actOperator       /==/
syn match   actOperator       /!=/
syn match   actOperator       /<=\@!/
syn match   actOperator       />=\@!/
syn match   actOperator       /==>/
syn match   actOperator       /=\/=/
syn match   actOperator       /:=/
syn match   actOperator       /=>/
syn match   actOperator       /|->/
syn match   actOperator       /[+\-\*\/\^%]/
syn match   actOperator       /</
syn match   actOperator       />/

" Numbers
syn match   actNumber         /\<\d\+\>/
syn match   actNumber         /\<0x[0-9a-fA-F]\+\>/

" Strings
syn region  actString         start=/"/ skip=/\\"/ end=/"/

" Comments
syn match   actComment        /\/\/.*$/ contains=actTodo
syn keyword actTodo           TODO FIXME XXX NOTE contained

" Typed addresses: address<ContractName>
syn match   actTypedAddress   /address<[A-Za-z_][A-Za-z0-9_]*>/

" Highlighting links
hi def link actTopLevel       Structure
hi def link actBlock          Keyword
hi def link actClause         Keyword
hi def link actModifier       StorageClass
hi def link actConditional    Conditional
hi def link actLogical        Operator
hi def link actBoolean        Boolean
hi def link actType           Type
hi def link actKeyword        Keyword
hi def link actBuiltin        Function
hi def link actEnvironment    Constant
hi def link actOperator       Operator
hi def link actNumber         Number
hi def link actString         String
hi def link actComment        Comment
hi def link actTodo           Todo
hi def link actTypedAddress   Type

let b:current_syntax = "act"
