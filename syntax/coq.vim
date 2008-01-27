" Vim syntax file
" Language:     Coq
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change: 2008 Jan 27 - Changed the way things are coloured, improved the efficiency of colouring.
"              2008 Jan 25 - Added Ltac, added Notations, bugfixes.
"              2007 Dec 1 - Added Record's.
"              2007 Nov 28 - Added things to reuse (in other plugins) the knowledge that we are inside a proof.
"              2007 Nov 19 - Fixed bug with comments.
"              2007 Nov 17 - Various minor bugfixes.
"              2007 Nov 8 - Added keywords.
"              2007 Nov 8 - Fixed some ill-highlighting in the type of declarations.
"              2007 Nov 8 - Fixed pb with keywords ("\<...\>" had been forgotten) 
"                           (thanks to Vasileios Koutavas)
"              2007 Nov 8 - Definition...Defined now works as expected, 
"                           fixed a bug with tactics that were not recognized,
"                           fixed other bugs
"              2007 Nov 7 - Complete refactoring, (much) more accurate highlighting. Much bigger file...
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
syn match coqVernacPunctuation ":=\|\.\|:"
syn match coqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"
syn match coqConstructor       contained "[_[:alpha:]][_'[:alnum:]]*"
syn match coqField             contained "[_[:alpha:]][_'[:alnum:]]*"
syn keyword coqKwd             contained else end exists exists2 fix forall fun if in match let struct then where with
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|=\|>\|<\|<="
syn match coqAccolade          contained "{"
syn match coqPunctuation       contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"
syn match coqTermPunctuation   contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"
syn keyword coqTodo            contained TODO FIXME XXX NOTE
syn keyword coqTopLevel        Add Arguments Bind Declare Delimit End Export Hint Implicit Local
syn keyword coqTopLevel        Import Module Opaque Open Require Scope Section Set Type Unset
syn keyword coqVernacular      Functional Scheme
syn keyword coqHint            Resolve Immediate Constructors Unfold Extern
syn keyword coqFeedback        Check Eval Guarded Show
syn keyword coqProofDelim      Defined  
"                              ^^^^^^^ hide #bug1 a little bit

" The following is just to help other plugins to detect via syntax groups that we are inside a proof
syn keyword coqProofKwd         contained else end exists exists2 forall fun if in match let struct then where with
syn match   coqProofKwd         contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|="
syn match   coqProofPunctuation contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"

" Notations
syn region coqNotation     contains=coqNotationDef start="\<\(Notation\|Infix\)\>\(\s\+Local\>\)\?" end="\.\_s" keepend
syn region coqNotationDef  contained contains=coqNotationString,coqNotationTerm matchgroup=coqVernacular start="\<\(Notation\|Infix\)\>\(\s\+Local\>\)\?" end="\.\_s"
syn region coqNotationTerm contained contains=coqKwd,coqNotationKwd,coqString,coqTermPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn match   coqNotationKwd contained "at \(next \)\?level"
syn match   coqNotationKwd contained "\(no\|left\|right\) associativity"
syn match   coqNotationKwd contained "only parsing"
syn keyword coqNotationKwd contained ident global bigint format

" Tactic notations
syn region coqTacNotation     contains=coqTacNotationDef start="\<Tactic\_s\+Notation\>" end="\.\_s" keepend
syn region coqTacNotationDef  contained contains=coqNotationString,coqTacNotationKwd,coqTacNotationTerm matchgroup=coqVernacular start="\<Tactic\_s\+Notation\>" end="\.\_s"
syn region coqTacNotationTerm contained contains=coqKwd,coqString,coqTermPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqTacNotationKwd contained ident simple_intropattern hyp reference constr integer int_or_var tactic
syn match   coqTacNotationKwd contained "at level"

" Declarations
syn region coqDecl       contains=coqIdent,coqDeclTerm,coqDeclBinder matchgroup=coqVernacular start="\<\%(Axiom\|Conjecture\|Hypothes[ie]s\|Parameters\?\|Variables\?\)\>" matchgroup=coqVernacular end="\.\_s" keepend
syn region coqDeclBinder contained contains=coqDeclNames,coqDeclTerm matchgroup=coqTermPunctuation start="(" end=")" keepend
syn match  coqDeclNames  contained contains=coqIdent "[^:]*"
syn region coqDeclTerm   contained contains=coqTermPunctuation,coqKwd matchgroup=coqTermPunctuation start=":" end=")"
syn region coqDeclTerm   contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacPunctuation start=":" end="\.\_s"

" Theorems
syn region coqProof     contains=coqThm,coqProofBody matchgroup=coqVernacular start="\<\%(Theorem\|Lemma\|Example\|Corollary\)\>" matchgroup=coqProofDelim end="\<\%(Qed\|Defined\)\>" matchgroup=coqError end="\<\%(Admitted\|Abort\)\>" keepend
syn region coqThm       contained contains=coqIdent,coqThmTerm,coqThmBinder matchgroup=coqVernacular start="" end="\.\_s"me=s-1 keepend
syn region coqThmTerm   contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start=":" end="\.\_s"
syn region coqThmBinder contained matchgroup=coqTermPunctuation start="(" end=")"

syn region coqProof     contains=coqGoal,coqProofBody matchgroup=coqVernacular start="\<Goal\>" matchgroup=coqProofDelim end="\<\%(Qed\|Defined\)\>" matchgroup=coqError end="\<\%(Admitted\|Abort\)\>" keepend
syn region coqGoal      contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start="" matchgroup=coqVernacPunctuation end="\.\_s"me=s-1 keepend

" Ltac
syn region coqLtacDecl     contains=coqLtacProfile start="\<Ltac\>" end="\.\_s" keepend
syn region coqLtacProfile  contained contains=coqLtacIdent,coqVernacPunctuation,coqLtacContents start="Ltac" end="\.\_s"
syn region coqLtacIdent    contained matchgroup=coqVernacular start="Ltac" matchgroup=coqIdent end="[_[:alpha:]][_'[:alnum:]]*"
syn region coqLtacContents contained contains=coqTactic,coqTacticKwd,coqLtac,coqProofPunctuation matchgroup=coqVernacPunctuation start=":=" end="\.\_s"

syn keyword coqLtac contained do info progress repeat try
syn keyword coqLtac contained abstract constr context end external eval fail first fresh fun goal
syn keyword coqLtac contained idtac in let ltac lazymatch match of rec reverse solve type with
syn match   coqLtac contained "|\|=>\|||\|\[\|\]\|_"

" Proofs
syn region coqProofBody   contained contains=coqProofPunctuation,coqProofDelim,coqTactic,coqTacticKwd,coqProofComment,coqProofKwd matchgroup=coqVernacPunctuation start="\.\_s" matchgroup=coqProofDelim end="\<\%(Qed\|Defined\)\>" matchgroup=coqError end="\<\%(Admitted\|Abort\)\."
syn match coqProofDelim contained contains=coqVernacPunctuation "Proof."
syn keyword coqTactic contained absurd apply assert assumption auto 
syn keyword coqTactic contained case[_eq] change clear[body] cofix cbv compare compute congruence constructor contradiction cut[rewrite] 
syn keyword coqTactic contained decide decompose dependant destruct discriminate double
syn keyword coqTactic contained eapply eassumption econstructor elim[type] equality evar exact eexact exists
syn keyword coqTactic contained fix f_equal fold functional generalize hnf
syn keyword coqTactic contained idtac induction injection instantiate intro[s] intuition inversion[_clear]
syn keyword coqTactic contained lapply left move omega pattern pose proof quote
syn keyword coqTactic contained red refine reflexivity rename replace revert rewrite right ring
syn keyword coqTactic contained set simpl[e] simplify_eq split subst stepl stepr symmetry
syn keyword coqTactic contained transitivity trivial unfold vm_compute
syn keyword coqTacticKwd  contained as by in using with into after until


" Definitions
"     definitions defined by a proof ("Defined"). must be placed *before* the usual definitions.
"     #bug1: this is buggy when the type of the defined term contains ':='
"     Putting the type not on the same line than "Definition" gives the right behaviour.
syn match   coqDef2       contains=coqDefProfile2,coqProofBody "\<\%(Definition\|Let\)\>\_.\{-}\<Defined\>"
syn region coqDefProfile2 contained contains=coqIdent,coqDefTerm2,coqDefBinder2 matchgroup=coqVernacular start="\<\%(Definition\|Let\)\>" matchgroup=coqVernacular end="\.\_s"me=s-1
syn region coqDefTerm2    contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start=":"  end="\.\_s"me=s-1
syn region coqDefBinder2  contained contains=coqTermPunctuation,coqKwd matchgroup=coqTermPunctuation start="("  end=")"

"     usual definitions
syn match   coqDef        contains=coqDefProfile,coqDefContent "\%(Definition\|Let\).\{-}:=\_.\{-}\.\_s"
syn region coqDefProfile  contained contains=coqIdent,coqDefTerm,coqDefBinder matchgroup=coqVernacular start="\%(Definition\|Let\)" matchgroup=coqVernacular end=":="me=e-2
syn region coqDefTerm    contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start=":"  end=":="me=s-1
syn region coqDefBinder  contained contains=coqTermPunctuation,coqKwd matchgroup=coqTermPunctuation start="("  end=")"
syn region coqDefContent contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start=":=" end="\.\_s"

" Records
syn region coqRec        contains=coqRecProfile start="\<Record\>" end="\.\_s" keepend
syn region coqRecProfile contained contains=coqIdent,coqRecTerm,coqRecBinder matchgroup=coqVernacular start="Record" matchgroup=NONE end="\.\_s"
syn region coqRecBinder  contained contains=coqTermPunctuation,coqKwd matchgroup=coqTermPunctuation start="("  end=")"
syn region coqRecTerm    contained contains=coqTermPunctuation,coqKwd,coqRecContent matchgroup=coqVernacPunctuation start=":"  end="\.\_s"
syn region coqRecContent contained contains=coqConstructor,coqRecStart matchgroup=coqVernacPunctuation start=":=" end="\.\_s"
syn region coqRecStart   contained contains=coqRecField,coqTermPunctuation,coqKwd start="{" matchgroup=coqVernacPunctuation end="}\_s*\.\_s"
syn region coqRecField   contained contains=coqField,coqPunctuation matchgroup=coqVernacPunctuation start="{" matchgroup=coqPunctuation end=":"
syn region coqRecField   contained contains=coqField,coqPunctuation matchgroup=coqPunctuation start=";" end=":"

" Fixpoints
syn region coqFix        contains=coqFixProfile,coqFixContent matchgroup=coqVernacular start="\<\%(\%(\%(Co\)\?Fixpoint\)\|Function\)\>" matchgroup=coqVernacular end="\.\_s" keepend
syn region coqFixProfile contained contains=coqIdent,coqFixTerm,coqFixBinder,coqFixAnnot containedin=coqFix start="" matchgroup=coqVernacular end=":="me=e-2
syn region coqFixTerm    contained contains=coqTermPunctuation,coqKwd matchgroup=coqVernacular start=":" end=":="me=e-2
syn region coqFixBinder  contained contains=coqTermPunctuation,coqKwd,coqFixBinder matchgroup=coqTermPunctuation start="(" end=")"
syn region coqFixAnnot   contained contains=coqKwd matchgroup=coqTermPunctuation start="{" end="}"
syn region coqFixContent contains=coqTermPunctuation,coqKwd contained matchgroup=coqVernacular start=":=" end="\.\_s"

"Inductives
syn region coqInd            contains=coqIndBody matchgroup=coqVernacular start="\<\%(\%(Co\)\?Inductive\)\>" matchgroup=coqVernacular end="\.\_s" keepend
syn region coqIndBody        contained contains=coqIndProfile,coqIndContent start="" matchgroup=coqVernacular end="\.\_s" matchgroup=coqVernacular end="\<with\>" keepend
syn match  coqIndProfile     contained contains=coqIdent,coqIndTerm,coqIndBinder,coqVernacPunctuation containedin=coqInd ".\{-}:="
syn match  coqIndTerm        contained contains=coqTermPunctuation,coqKwd ":[^=]\+"me=e-1
syn region coqIndBinder      contained contains=coqTermPunctuation,coqKwd,coqIndBinder matchgroup=coqTermPunctuation start="("  end=")"
syn match  coqIndContent     contained contains=coqIndConstructor "\_.*\(\.\_s\|\<with\>\)"
syn match  coqIndConstructor contained contains=coqConstructor,coqIndBinder,coqIndBodyTerm,coqIndPunctuation "\_.*\(|\|\.\_s\|\<with\>\)"
syn match  coqIndPunctuation contained "|"
syn region coqIndBodyTerm    contained contains=coqTermPunctuation,coqKwd matchgroup=coqIndConstructor start=":" matchgroup=coqVernacular end="|"me=e-1 end="\.\_s" end="\<with\>"

" Divers (high priority)
syn region  coqComment        contains=coqComment,coqTodo start="(\*" end="\*)" extend keepend
syn region  coqString         start=+"+ skip=+""+ end=+"+ extend
syn region  coqProofComment   contains=coqProofComment,coqTodo start="(\*" end="\*)" extend keepend
syn region  coqNotationString contained start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

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

 HiLink coqAccolade          PreProc
 HiLink coqConstructor       Keyword
 HiLink coqComment           Comment
 HiLink coqError             Error
 HiLink coqHint              PreProc
 HiLink coqFeedback          PreProc
 HiLink coqField             Keyword
 HiLink coqIndPunctuation    PreProc
 HiLink coqIdent             Identifier
 HiLink coqKwd               Type
 HiLink coqLtac              Keyword
 HiLink coqNotationKwd       Special
 HiLink coqNotationString    Identifier
 HiLink coqProofKwd          Keyword
 HiLink coqPunctuation       Keyword
 HiLink coqProofPunctuation  Keyword
 HiLink coqProofDelim        Underlined
 HiLink coqString            String
 HiLink coqTactic            Keyword
 HiLink coqTacticKwd         Keyword
 HiLink coqTacNotationKwd    Keyword
 HiLink coqTermPunctuation   Type
 HiLink coqTodo              Todo
 HiLink coqTopLevel          PreProc
 HiLink coqVernacular        PreProc
 HiLink coqVernacPunctuation PreProc
 HiLink coqProofComment      Comment

 delcommand HiLink
endif

let b:current_syntax = "coq"
