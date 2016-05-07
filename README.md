# Shullivan

Shullivan is an implementation in C of the original Ghilbert language and proof
verification system by Raph Levien, with a few optional enhancements.  Ghilbert
was in turn inspired by Metamath.  Shullivan's main claim to fame is that it is
much faster at verification than the original python Ghilbert implementation.

Shullivan comes with a simple Makefile that probably needs to be adapted
to particular environments.  As of May 7 2016, Shullivan builds without
warnings on Arch Linux.  Other than a minor amount of maintenance to get
shullivan to build before uploading it to github, I have done no work on
shullivan in a long time and do not currently have plans to work on it in
the future.  Note that Ghilbert itself has moved on since the days in which
shullivan was written.

Here's an example shullivan session, making use of the (old) Ghilbert pax library.
Note that since readline is used to edit the partial proofs, one doesn't have
to retype the whole proof so far to change it.  (I suggest using 'Ctrl-J'
to enter line-feeds within an editable 'line'.)

```
[dlkrejsa@clifford shullivan]$ export GHILBERT_PATH=/home/dlkrejsa/src/ghilbert
[dlkrejsa@clifford shullivan]$ ./shul
Shullivan version 0.01. Enter 'help' for help.
shul=> import (PROP pax/prop () "")
Importing PROP
shul=> interfaces
import (PROP pax/prop ( ) "")
   Kinds:  wff
   Terms:  -. -> <-> \/ /\ \/\/ /\/\
   Statements:  ax-1 ax-2 ax-3 ax-mp df-bi df-or df-an df-3or df-3an
shul=> thm (a1i () ((a1i.1 ph)) (-> ps ph)
        (a1i.1 ph ps ax-1 ax-mp))
verifying a1i
*** Cannot infer kind for undeclared variable 'ps'
shul=> flags ?
Current shullivan flags : 0x0
0x1 : Allow statements with 0 or more conclusions [Off]
0x2 : Allow kind inference for variables in hypotheses or conclusions [Off]
0x4 : Allow variable kind inference in exported statements [Off]
0x8 : Print warnings about unneeded DV items in exported statements [Off]
shul=> flags 0xf
shul=> history
0. import (PROP pax/prop ( ) "")
shul=> thm (a1i () ((a1i.1 ph)) (-> ps ph)
        (a1i.1 ph ps ax-1 ax-mp))
verifying a1i
shul=> history
0. import (PROP pax/prop ( ) "")
1. thm  (a1i () ((a1i.1 ph))
          (-> ps ph) ...)
shul=> thm (a2i () ((a2i.1 (-> ph (-> ps ch))))
        (-> (-> ph ps) (-> ph ch))
        (a2i.1 ph ps ch ax-2 ax-mp))
verifying a2i
shul=> thm (syl () (syl.1 (syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)

> thm (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)
        (-> syl.1 syl.2))
> )
*** expected thm (NAME ([(VAR1 VAR2 ...)]) ([(HYPNAME HYP) ...]) {CONCL | ([CONCL ...])} (STEP ...))
shul=> thm (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)
        (syl.1 syl.2))
verifying syl
*** Expected 1 conclusions at end of proof, have 2.
PS0   (-> ph ps)
PS1   (-> ps ch)
MV stack empty.
shul=> thm (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)
        (syl.1 syl.2 ph a1i))
verifying syl
*** Expected 1 conclusions at end of proof, have 2.
PS0   (-> ph ps)
PS1   (-> ph (-> ps ch))
MV stack empty.
shul=> thm (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)
        (syl.1 syl.2 ph a1i a2i))
verifying syl
*** Expected 1 conclusions at end of proof, have 2.
PS0   (-> ph ps)
PS1   (-> (-> ph ps) (-> ph ch))
MV stack empty.
shul=> thm (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
        (-> ph ch)
        (syl.1 syl.2 ph a1i a2i ax-mp))
verifying syl
shul=> save (test.gh)
shul=> exit
Cheerio!
[dlkrejsa@clifford shullivan]$ cat test.gh
import (PROP pax/prop ( ) "")
thm  (a1i () ((a1i.1 ph))
          (-> ps ph)
          (a1i.1 ph ps ax-1 ax-mp))
thm  (a2i () ((a2i.1 (-> ph (-> ps ch))))
          (-> (-> ph ps) (-> ph ch))
          (a2i.1 ph ps ch ax-2 ax-mp))
thm  (syl () ((syl.1 (-> ph ps)) (syl.2 (-> ps ch)))
          (-> ph ch)
          (syl.1 syl.2 ph a1i a2i ax-mp))
[dlkrejsa@clifford shullivan]$ ./shul
Shullivan version 0.01. Enter 'help' for help.
shul=> keep
Proofs will be kept.
shul=> load test
Importing PROP
verifying a1i
*** Cannot infer kind for undeclared variable 'ps'
thm (a1i () ((a1i.1 ph)) (-> ps ph) (a1i.1 ph ps ax-1 ax-mp))
load: last line number: 4
load failed.
shul=> history
0. import (PROP pax/prop ( ) "")
shul=> erase 0
shul=> flags 0xf
shul=> history
shul=> load test
Importing PROP
verifying a1i
verifying a2i
verifying syl
shul=> thm (com12 () ((com12.1 (-> ph (-> ps ch))))
        (-> ps (-> ph ch))
        (com12.1 a2i))
verifying com12
*** conclusion mismatch, expected variable 'ps'
PS0   (-> (-> ph ps) (-> ph ch))
MV stack empty.
shul=> thm (com12 () ((com12.1 (-> ph (-> ps ch))))
        (-> ps (-> ph ch))
        (ps ph ax-1 com12.1 a2i))
verifying com12
*** Expected 1 conclusions at end of proof, have 2.
PS0   (-> ps (-> ph ps))
PS1   (-> (-> ph ps) (-> ph ch))
MV stack empty.
shul=> thm (com12 () ((com12.1 (-> ph (-> ps ch))))
        (-> ps (-> ph ch))
        (ps ph ax-1 com12.1 a2i syl))
verifying com12
shul=> save (test.gh)
shul=> erase 0
shul=> load test
Importing PROP
verifying a1i
verifying a2i
verifying syl
verifying com12
shul=> exit
Cheerio!
```