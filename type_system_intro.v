(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export cequiv.

(**
This chapter presents our formalization of Nuprl's type system.
We will first explain how induction-recursion can be used to 
define the type system in an intuitive way.
We will then explain why such a simple definition cannot be achieved 
in Coq either by pure mutual induction(using the [Inductive] construct)
or by pure mutual recursion(using the [Fixpoint] construct).
As mentioned above,
this problem is well known, and we are just adapting it to our context with a slightly different explanation.
In one sentence, the problem is that the intuitive definition the evidence of typehood of an [NTerm]
is an inductive one, 
but equality can be best understood as function that is structurally recursive on the evidence of typehood.

As a proof of concept, we show how to use induction-recursion to define the entire predicative
hierarchy of universes of Nuprl in the first universe of Agda's predicative hierarchy.
The use of induction-recursion to define shallow embeddings of hierarchies 
of Martin Lof universes have been
often described in the literature %\cite{Dybjer:2000, McBride:2011}%.
However, since we have a deep embedding, we have to use parametrized induction-recursion
and our definitions are parametrized over (pairs of) [NTerm].
This deep approach is required for our goals of extracting an independent, 
correct by construction proof assistant.

Also for Nuprl, we have to simultaneously
define the equality of types and equality of members in types,
unlike other works where just typehood and membership are defined simultaneously.
Note that two terms that are not related by [cequiv] can represent the same type.
For example, $\lambda x.((x+1)-1) =_{\mathbb{N} \rightarrow \mathbb{N}} \lambda x.x$
and $ \lambda x.x =_{\mathbb{N} \rightarrow \mathbb{N}} \lambda x.((x+1)-1)$ are equal 
equality types, but the two terms are not related by [cequiv].
On the other hand, types that have the same PER are not always equal. For example,
as we will see later, the equality types
$0 =_{\mathbb{N}} 0$ and $1 =_{\mathbb{N}} 1$ are not equal types.
Hence, the equality of types in a Nuprl universe is non-trivial and our  
the inductive part defines the pairs of [NTerm]s that represent equal types,
instead of just defining the [NTerm]s that denote types.


Although the inductive-recursive definition is easier to understand and 
would enable a predicative formalization of all of Nuprl,
Agda does not have a tactic language, 
which we heavily depend on to automate many otherwise tedious parts of proofs.
So we had to accept the lack of induction-recursion in Coq and we 
finally settled on using Allen's trick to define the type system of Nuprl in Coq.
At first, this purely inductive definition in section %\ref{sec:type:ind}% might seem overly complicated.
However, it can be understood as applying the generalized recipe of %\cite{Capretta:2004}%
to the inductive-recursive definition.
One might want to revisit Fig. %\ref{fig:metatheories}% for a summary our deep embeddings.
*)

(*
	\begin{figure}
	\centering
	\input{finalPicTikz.tex}
	\caption{The left hand side summarizes our predicative embeddings. For completeness,
			we also pictorially depict Werner's set theoretic 
			semantics\cite{Werner97setsin} on the right hand side.
                        }
	\label{figure:embeddings}
	\end{figure}
*)

(** * An Inductive Recursive Definition of Nuprl's Type System
%\label{sec:type:indrec}%

Just for this section, we will pretend that all our definitions
so far are in Agda. Given the theoretical slimilarity between
Coq and Agda%\footnote{\url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.AgdaVsCoq}}%,
and the fact that all our definitions are predicative,
we think that it should be fairly straightforward to convert our
definitions to Agda. In fact, all the definitions so far can be defined
in [Set], the first predicate universe in both Coq and Agda.

We will first show the construction of just one universe of Nuprl
in Agda and then define the whole hierarchy of universes.
We only define the following 3 representative types to illustrate the idea:
- the integer type
- dependent functions
- partial types
- W types
Our Agda definition is just intended as a proof of concept. It illustrates  the
elegance and the consistency strength of induction-recursion. As mentioned before,
we have defined all the types of Nuprl in Coq because the powerful
tactic machinery of Coq is critical for automating our tedious proofs.

We will assume that we had the following definitions( among others )
 in Agda instead of Coq.

[[
Definition subst (t : NTerm) (v : NVar) (u : NTerm) : NTerm :=
    lsubst t [(v,u)].
Definition mk_lam (v : NVar) (b : NTerm) : NTerm :=  
    oterm (Can NLambda) [bterm [v] b].
Definition mk_apply (f a : NTerm) : NTerm := 
    oterm (NCan NApply) [bterm [] f , bterm [] a].
Definition mk_int (z : Z ) := oterm (Can (Nint z)) [].
Definition mk_Int   := oterm (Can NInt)   [].
Definition mk_Uni n := oterm (Can (NUni n)) [].
Definition mk_Function (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NFunction) [bterm [] T1, bterm [v] T2].
Definition mk_W (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
    oterm (Can NW) [bterm [] T1, bterm [v] T2].
]]
*)



(*
A straightforward way to define a single universe will be to define the following
by mutual induction.
- equalType : [NTerm -> NTerm -> Set]
- equalInType : [ {T1 T2  : NTerm} -> (ev: equalType T1 T2) -> (t1 t2: NTerm) -> Set]

The idea is that [equalType T1 T2] asserts that [T1] and [T2] denote
equal types and given an evidence [ev] that [T1] and [T2] denote equal types,
[equalInType ev t1 t2] are equal terms in the type denoted by [T1] and [T2].
Note that the first two arguments of equalInType are implicit.

*)