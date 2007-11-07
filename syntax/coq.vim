" Vim syntax file
" Language:     Coq
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change: 2007 Nov 7 - Complete refactoring, (much) more accurate highlighting
"              2007 Nov 7 - Added tactic colouration, added other keywords (thanks to Tom Harke)
"              2007 Nov 6 - Added "Defined" keyword (thanks to Serge Leblanc)
"              2007 Nov 5 - Initial version.
" License:     public domain

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "coq"
  finish
endif

" Coq is case sensitive.
syn case match

" Divers (low priority)
syn match coqIdent       contained "[_[:alpha:]][_'[:alnum:]]*"
syn match coqConstructor contained "[_[:alpha:]][_'[:alnum:]]*"
syn match coqPunctuation "(\|)\|:=\|:>\|:\|\.\|;\|," contained
syn keyword coqKwd       contained if then else match with end let in forall exists exists2 struct
syn match   coqKwd       contained "|\|/\\\|\\/\|<->\|\~\|->\|=>"
syn keyword coqTodo      contained TODO FIXME XXX NOTE
syn keyword coqTopLevel  Add Arguments Declare End Export Hint Implicit Ltac Import Notation Open Require Scope Section Set
syn keyword coqFeedback  Check Eval Guarded Show

" Declarations
syn region coqDecl       contains=coqIdent,coqDeclTerm,coqDeclBinder matchgroup=coqVernacular start="Axiom\|Conjecture\|Hypothes[ie]s\|Parameters\?\|Variables\?" matchgroup=coqPunctuation end="\." keepend
syn region coqDeclTerm   contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":" end="\."
syn region coqDeclBinder contained contains=coqDeclNames,coqDeclTerm matchgroup=coqPunctuation start="(" end=")" keepend
syn match  coqDeclNames  contained contains=coqIdent "[^:]*"
syn region coqDeclTerm   contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":" end=")"

" Theorems
syn region coqProof     contains=coqThm,coqProofBody matchgroup=coqVernacular start="Theorem\|Lemma\|Example\|Corollary" matchgroup=coqProofDelim end="Qed" end="Defined" matchgroup=coqError end="Admitted" end="Abort" keepend
syn region coqThm       contained contains=coqIdent,coqThmTerm,coqThmBinder matchgroup=coqVernacular start="" matchgroup=coqPunctuation end="\."me=e-1 keepend
syn region coqThmTerm   contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":" end="\."
syn region coqThmBinder contained matchgroup=coqPunctuation start="(" end=")"

          " proofs
syn region coqProofBody   contained contains=coqPunctuation,coqProofDelim,coqTactic,coqTacticKwd start="\." matchgroup=coqProofDelim end="Qed" end="Defined" end="Admitted" end="Abort"
syn keyword coqProofDelim Proof
syn keyword coqTactic     contained absurd apply assert assumption auto case_eq change clear[body] cofix cbv compare compute congruence constructor contradiction cut[rewrite] decide decompose dependant destruct discriminate do double eapply eassumption econstructor elim[type] equality evar exact eexact exists f_equal fold functional generalize hnf idtac induction info injection instantiateintro[s] intuition inversion[_clear] lapply left move omega pattern pose proof quote red refine reflexivity rename repeat replace revert rewrite right ring set simpl[e] simplify_eqsplit subst stepl stepr symmetry transitivity trivial try unfold vm_compute contained
syn keyword coqTacticKwd  contained as in using with into after until

" Definitions
syn region coqDef        contains=coqDefProfile,coqDefContent matchgroup=coqVernacular start="Definition\|Let" matchgroup=coqPunctuation end="\." keepend
syn region coqDefProfile contained contains=coqIdent,coqDefTerm,coqDefBinder containedin=coqDef start="" matchgroup=coqPunctuation end=":="me=e-2
syn region coqDefTerm    contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":"  end=":="me=e-2
syn region coqDefBinder  contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start="("  end=")"
syn region coqDefContent contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":=" end="\."

" Fixpoints
syn region coqFix        contains=coqFixProfile,coqFixContent matchgroup=coqVernacular start="\%(Co\)\?Fixpoint" matchgroup=coqPunctuation end="\." keepend
syn region coqFixProfile contained contains=coqIdent,coqFixTerm,coqFixBinder,coqFixAnnot containedin=coqFix start="" matchgroup=coqPunctuation end=":="me=e-2
syn region coqFixTerm    contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":" end=":="me=e-2
syn region coqFixBinder  contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start="(" end=")"
syn region coqFixAnnot   contained contains=coqKwd matchgroup=coqPunctuation start="{" end="}"
syn region coqFixContent contains=coqPunctuation,coqKwd contained matchgroup=coqPunctuation start=":=" end="\."

"Inductives
syn region coqInd        contains=coqIndBody matchgroup=coqVernacular start="\%(Co\)\?Inductive" matchgroup=coqPunctuation end="\." keepend
syn region coqIndBody    contained contains=coqIndProfile,coqIndContent start="" matchgroup=coqPunctuation end="\." matchgroup=coqVernacular end="with" keepend
syn match  coqIndProfile contained contains=coqIdent,coqIndTerm,coqIndBinder containedin=coqInd ".*:="
syn match coqIndTerm     contained contains=coqPunctuation,coqKwd ":.*"
syn region coqIndBinder  contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start="("  end=")"
syn region coqIndContent contained contains=coqIndConstructor  matchgroup=coqPunctuation start="" end="\." end="with" keepend
syn region coqIndConstructor contained contains=coqConstructor,coqIndBinder,coqIndBodyTerm matchgroup=coqPunctuation start="\_[[:blank:]]*|\?" end="|"me=e-1 end="\." end="with"
syn region coqIndBodyTerm    contained contains=coqPunctuation,coqKwd matchgroup=coqPunctuation start=":" end="|"me=e-1 end="\." end="with"

" Divers (high priority)
syn region  coqComment   contains=coqComment,coqTodo containedin=ALL start="(\*" end="\*)"
syn region  coqString    start="\"" skip="\"\"" end="\""



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

  HiLink coqPunctuation Keyword
  HiLink coqIdent       Identifier
  HiLink coqConstructor Special
  HiLink coqVernacular  Keyword
  HiLink coqError       Error
  HiLink coqProofDelim  Underlined
  HiLink coqTactic      Constant
  HiLink coqTacticKwd   Constant
  HiLink coqKwd         Type
  HiLink coqComment     Comment
  HiLink coqTodo        Todo
  HiLink coqString      String
  HiLink coqFeedback    PreProc
  HiLink coqTopLevel    PreProc

  delcommand HiLink
endif

let b:current_syntax = "coq"
