MAKEFILE
========

To generate a Makefile, run `create_makefile.sh`.  This script
requires bash v4.  It will generate a Makefile for `rules.v` and its
dependencies.  Re-run `create_makefile.sh` everytime you pull to
update the Makefile in case new files have been committed, or files
have been moved around.

Then run "make" (or alternatively if your machine has multiple cores,
run make -j n, where n is the number of cores you want to use) to
compile everything.  This will take a while.

Our implementation compiles with Coq version 8.9.0.


DESCRIPTION
===========

This library formalizes Nuprl's Constructive Type Theory (CTT) as of
2016.  More information can be found about Nuprl on the [Nuprl
website](http://www.nuprl.org/).  (Also check out
[JonPRL](https://github.com/jonsterling/JonPRL) for an SML
re-implementation of Nuprl.)  As for
[Agda](http://wiki.portal.chalmers.se/agda/),
[Coq](https://coq.inria.fr/), and [Idris](http://www.idris-lang.org/),
Nuprl implements a dependent type theory à la Martin-Löf.  However,
CTT is an extensional type theory originally inspired by Martin-Löf's
extensional type theory.  It has since then been extended with several
new types such as: intersection types, union types, image types,
partial types, set types, quotient types, partial equivalence relation
(per) types, simulation and bisimulation types, an atom type, and the
"Base" type.

Our formalization includes a definition of Nuprl's computation system,
a definition of Howe's computational equivalence relation and a proof
that it is a congruence, an impredicative definition of Nuprl's type
system using Allen's PER semantics (using Prop's impredicativity, we
can formalize Nuprl's infinite hierarchy of universes), definitions of
most (but not all) of Nuprl's inference rules and proofs that these
rules are valid w.r.t. Allen's PER semantics, and a proof of Nuprl's
consistency.

In addition to the standard introduction and elimination rules for
Nuprl's types, we have also proved several Brouwerian rules.  Our
computation system also contains: (1) free choice sequences that we
used to prove Bar Induction rules; (2) named exceptions and a "fresh"
operator to generate fresh names, that we used to prove a continuity
rule.

More information can be found on our [NuprlInCoq
website](http://www.nuprl.org/html/Nuprl2Coq/).  Feel free to send
questions to the authors (preferably to Vincent).


KEYWORDS
========

* Nuprl
* Coq
* Constructive Type Theory
* Computational Type Theory
* Extensional Type Theory
* Intuitionistic Type Theory
* Nominal Type Theory
* Howe's computational equivalence relation
* Partial Equivalence Relation (PER) semantics
* Consistency
* Continuity
* Bar Induction
* Choice Sequences
* Effects (exceptions)


ROADMAP
=======

* The term definition is in `terms/terms.v` (see the definition of
`NTerm`).

* The definition of the computation system is in
`computation/computation.v` (see the definition of `compute_step`).

* Howe's computational equivalence relation is defined in
`cequiv/cequiv.v` (see the definition of `cequiv`).  This relation is
defined in terms of Howe's approximation relation defined in
`cequiv/approx.v` (see the definition `approx`).  Howe's computational
equivalence relation is proved to be a congruence in
`cequiv/approx_star.v`

* Types are defined in `per/per.v` using Allen's PER semantics.
Universes are closed under our various type constructor (see the
inductive definition of `close`).

* Universes and the `nuprl` type system are defined in `per/nuprl.v`.
We've proved that `nuprl` is indeed a type system in
`per/nuprl_type_sys.v`.

* Files such as `per/per_props.v` contain proofs of properties of the
`nuprl` type system.

* The definitions of sequents and rules are in `per/sequents.v`.  This
file also contains the definition of what it means for sequents and
rules to be valid.  We also prove in this file that Nuprl is
consistent in `per/weak_consistency.v`, meaning that there is no proof
of False.

* Our proofs of the validity of Nuprl's inference rules can be
accessed from `rules.v` (see for example `rules/rules_function.v`,
`rules/rules_squiggle.v`).

* The proof of our most general Bar Induction rule is in
`bar_induction/bar_induction_cterm3.v`.

* The proof of our most general continuity rule is discussed in
`continuity/continuity_roadmap.v`.

* In `per/function_all_types.v` (and similarly in `per/union_all_types.v`)
we have a proof that the pi type [forall n : nat. Universe(n)] is
indeed a Nuprl type even though it's not in any universe.

* In `axiom_choice/axiom_choice_gen.v` we have proved a version of the
axiom of choice AC00 for squashed sums.

* In `axiom_choice/choice_sequence_ind.v` we have proved the validity
of a principle to recursively define choice sequences.

* We started implemented a theorem prover backend that relies on a
verified library of definitions and proofs.  This
`rules/proof_with_lib_example1.v` for an example.  We can use this
backend as a proof checker for Nuprl.  See `nuprl_checker/README.md`
for more details.


CONTRIBUTORS
============

* Vincent Rahli
* Liron Cohen
* Abhishek Anand
* Mark Bickford
