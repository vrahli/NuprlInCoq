Nuprl Proof Checker
===================

We have written a proof checker that can take as input a proof
exported from Nuprl, and outputs a script (a list of commands), which
can then be evaluated within Coq to construct a library and check the
validity of the proof: if the library is valid, the proof is valid.
The translator from Nuprl to Coq is written in OCaml.  Nuprl uses an
XML-like format to export definitions, rules, and proofs.  The files
exported from Nuprl contain a proof as well as all its dependencies,
which form a sub-library of Nuprl's library.  Our OCaml program
converts such an XML-like file into a script to reconstruct the
corresponding sub-library within our Coq implementation of Nuprl.

The interface to our Coq formalization is essentially in
`../proof_with_lib_non_dep.v`.  It contains, among other things,
definitions of complete and incomplete proofs, of a library of
definitions and facts, and of what it means for a library to be valid.
It also provides a simple script language to manipulate the library:
to build proofs and add new definitions.

In addition to using this tool to automatically check Nuprl proofs,
one can use it as a standalone tool to build new proofs.  See
`proof_with_lib_non_dep_example1.v` for a simple example.

To run the code below, in addition to Coq, you'll need `ocamlbuild`,
`batteries`, and `menhir`, which you can get through opam.

To try our proof checker run (1 and 2 are to build our Coq formalization):

1. `(cs ..; ./create_makefile.sh)`

2. `(cd ..; make)`

3. `make` to create a binary.  This will create `Parse.native`

4. Then to convert the `uall_wf` proof, type:

       `./Parse.native --i uall_wf.term-list --o uall_output.v`

   This will create the `uall_output.v` file containing everything you
   need to check the proof using our Coq framework.

   To actually check the proof in coq, either open that
   `uall_output.v` file with a Coq editor and run the whole thing, or
   type

       `coqc -R ../axiom_choice axiom_choice -R ../bar_induction bar_induction -R ../cequiv cequiv -R ../close close -R ../computation computation -R ../continuity continuity -R ../per per -R ../rules rules -R ../terms terms -R ../util util uall_output.v`
