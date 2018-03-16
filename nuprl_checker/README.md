Nuprl Proof Checker
===================


Overview
--------


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


Generating primitive proof trees within Nuprl
---------------------------------------------


To generate such files, you first need to connect to Nuprl.  (If you
don't already have an account, look at
`http://www.nuprl.org/html/NuprlSystem.html` to see how to get an
account.)  Then in the Evaluator run:

  `primitive_export b1 b2 t l`

where `b1` is a Boolean (true/false) that indicates whether or not to
overwrite the file; `b2` is a Boolean that indicates whether or not to
include the dependency information used to the graph used to find the
list of objects to export; `t` is a token which is going to be used as
base for the filename; `l` is a list of objects used as seed for
closure of objects to export.

A token is a sequence of characters delimited by backquotes.  For the
objects, you'll have to click on an object somewhere in the library to
copy a pointer to the object, and then type C-y to paste the
pointer---it has to be preceded by `ioid`.

It is usually safe to use true for `b1` and `b2`.

The file will be exported to
/usr/nuprl/public/tmp/primitive-export/<name>.term-list.  If `b1` is
false, then the file will be exported to
/usr/nuprl/public/tmp/primitive-export/<name>-<datetime>.term-list.


Coq Files
---------


The interface to our Coq formalization is essentially in
`../rules/proof_with_lib_non_dep.v`.  It contains, among other things,
definitions of complete and incomplete proofs, of a library of
definitions and facts, and of what it means for a library to be valid.
It also provides a simple script language to manipulate the library:
to build proofs and add new definitions.

In addition to using this tool to automatically check Nuprl proofs,
one can use it as a standalone tool to build new proofs.  See
`../rules/proof_with_lib_non_dep_example1.v` for a simple example.


Using the tool
--------------


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


Roadmap
-------

As hinted above, the main file is `Parse.ml`.  It contains the
translator from Nuprl proofs to proofs in our verified
re-implementation of Nuprl in Coq.  It uses: `NuprlTerms.ml`, which
contains the abstract syntax for Nuprl terms; `ParseNuprlAscii.ml`,
which contains the parser of XML-file that Nuprl generates.


How to extend the tool
----------------------


To extend the tool with a new rule, you have to:

1. Prove the validity of the rule if we haven't done so yet.

2. Add support for this rule in our Coq checker of Nuprl proofs in
`../rules/proof_with_lib_non_dep.v`.  There are a few things to add
such as: a new constructor for `proof_step`; a description of what it
means for such a rule to be valid in `valid_proof_node_context`; etc.
Best is to look at an example such as `proof_step_function_equality`
and do something similar for the new rule.

3. Add support for this rule in our proof translator in `Parse.ml` by
adding a new case to the function  `print_proof_tree`.  Again, the
best thing to do is to look at an example.
