" Vim syntax file
" Language:     Coq
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change:  2007 Nov 5 - Initial version.

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "coq"
  finish
endif

" Coq is case sensitive.
syn case match

syn keyword coqKwd2        if then else match with end let in forall exists exists2
syn keyword coqTopLevel    Add Declare End Export Hint Ltac Import Notation Open Require Scope Section Set
syn keyword coqTodo        TODO FIXME XXX NOTE contained
syn match   coqPunctuation "(\|)\|:=\|\|:>\|:\|\.\|;\|,"
syn match   coqKwd2        "|\|/\\\|\\/\|<->\|\~\|->\|=>"
syn match   coqType        ":[^).]*" containedin=coqDecl contained contains=coqPunctuation
syn region  coqDecl        matchgroup=coqKwd1 start="Axiom\|Conjecture\|Hypothes[ie]s\|Parameters\?\|Variables\?" matchgroup=coqNormal end="\." contains=coqPunctuation,coqKwd2
syn region  coqIdent       matchgroup=coqKwd1 start="\%(Theorem\|Lemma\|Definition\|Let\|\%(\%(Co\)\?Fixpoint\)\)\_[[:blank:]]*" matchgroup=coqPunctuation end="[[:blank:]:]"

syn region  coqInductive   matchgroup=coqKwd1 start="\%(Co\)\?Inductive" matchgroup=coqPunctuation end="\." keepend contains=coqPunctuation
syn region  coqIndBody     matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=coqKwd1 end=":=" containedin=coqInductive contains=coqPunctuation,coqKwd2 contained keepend nextgroup=coqIndFirstCase,coqIndCase skipwhite skipnl skipempty
syn region  coqIndFirstCase matchgroup=coqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=coqKwd1 end="|"me=e-1 matchgroup=coqKwd1 end="with" matchgroup=coqPunctuation end="\." matchgroup=coqKwd1 end="with" contained nextgroup=coqIndCase skipwhite skipnl skipempty contains=coqPunctuation,coqKwd2
syn region  coqIndCase matchgroup=coqIdent start="|\_[[:blank:]]*[_[:alpha:]][_'[:alnum:]]*"hs=s+1 matchgroup=coqKwd1 end="|"me=e-1 matchgroup=coqKwd1 end="with" matchgroup=coqPunctuation end="\." matchgroup=coqKwd1 end="with" contained nextgroup=coqIndCase skipwhite skipnl skipempty contains=coqPunctuation,coqKwd2

syn region  coqComment     start="(\*" end="\*)" contains=coqComment,coqTodo
syn region  coqString      start="\"" skip="\"\"" end="\""
syn region  coqNormal      matchgroup=coqProof start="Proof" end="Qed" end="Defined"
syn keyword coqProof       Qed


" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_coq_syntax_inits")
  if version < 508
    let did_coq_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink coqKwd1        Keyword
  HiLink coqPunctuation Keyword
  HiLink coqKwd2        Type
  HiLink coqIdent       Identifier
  HiLink coqDecl        Identifier
  HiLink coqProof       Underlined
  HiLink coqTopLevel    PreProc
  HiLink coqNormal      Normal
  HiLink coqType        Normal
  HiLink coqComment     Comment
  HiLink coqTodo        Todo
  HiLink coqString      String

  delcommand HiLink
endif

let b:current_syntax = "coq"

" vim: ts=8
