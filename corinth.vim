" Vim syntax file
" Language: Corinth
" Maintainer: Joshua Phillips

if exists("b:current_syntax")
    finish
endif

syn keyword synKeyword class else elsif end if implements imported is loop 
syn keyword synKeyword overriding proc return then type unit while with
syn keyword synMinorKeyword and const new not or out var 
syn match synIdent '[A-Za-z_][A-Za-z0-9_]*'
syn match synBracket '[()<>{}|]'
syn match synOperator '[-+*/=]'
syn keyword synOperator := =>
syn match synNumber '\d\+'
syn region synComment oneline contains=@Spell start="--" end="$"
syn region synString contains=@Spell start=+"+ skip=+""+ end=+"+ 

hi def link synKeyword Keyword
hi def link synNumber Number
hi def link synParen Special
hi def link synComment Comment
hi def link synBracket SpecialChar
hi def link synOperator Operator
hi def link synMinorKeyword Function
hi def link synString String

let b:current_syntax = 'corinth'
