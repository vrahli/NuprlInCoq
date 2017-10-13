Nuprl Proof Checker
===================

We have written a proof checker that can take as input a proof
exported from Nuprl.  This part of the program is written in Ocaml.
Nuprl uses an XML-like format to export definitions, rules, and
proofs.  To try our proof checker run:

1. `make` to create a binary.  This will create `Parse.native`

2. Then to convert the `uall_wf` proof type:

       `./Parse.native --i uall_wf.term-list --o uall_output.v`

   This will create the `uall_output.v` file containing everything you
   need to check the proof using our Coq framework coq.

   To actually check the proof in coq, either open that
   `uall_output.v` file with a Coq editor and run the whole thing, or
   type

       `coqc -R ../axiom_choice axiom_choice -R ../bar_induction bar_induction -R ../cequiv cequiv -R ../close close -R ../computation computation -R ../continuity continuity -R ../per per -R ../rules rules -R ../terms terms -R ../util util uall_output.v`
