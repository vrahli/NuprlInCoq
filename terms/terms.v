(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export Recdef.
Require Export Eqdep_dec.
Require Export opid.
Require Export variables.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)



(**
  We can now define the terms of the Nuprl language as an inductive type.
  There are several considerations in choosing the right definition.
  The definition needs to be general enough so that adding
  new constructs to the term language does
  not break proofs about general properties of general operations on terms.
  For example, the substitution operation and the alpha equality
  relation only care about the getting access to the variables and
  do not care about the other operators(constucts) of the language.

  Our term definition(similar to %\cite{Howe:1989}%)
  exposes the variables, especially the concept
  of bound variables in a uniform way so that these
  and many other operations and proofs work unchanged
  when adding/removing constructs from the language.
  These robust proofs run into several thousands of lines and include the
  many properties about substitution and alpha equality that
  we need for formalizing all of Nurpl.

  Many alternative approaches for variable bindings
  have been discussed in the
  literature %~\cite{Pfenning:1988,Capretta:2007,Chlipala:cpdt}%.
  Our choice avoided the overhead of translating
  the paper definitions about Nuprl to some other style of variable
  bindings.

  We will first intuitively explain parts of the definition before showing it.
  Firstly, we have a constructor ([vterm]) that builds a term([NTerm]) from a variable([NVar])).
  Variable bindings are made explicit by the concept of a bound term ([BTerm]).
  [bterm] is the only constructor of [BTerm]. It takes a list of variables (say [lv])
  and a term (say [nt]) and constructs a bound term. Intuitively, a variable that is
  free in [nt] gets bound to its first occurence in [lv], if any.
  For example, the bound term [bterm [nvarx] (vterm nvarx)] will
  be used soon in constructing an identity function($\lambda x.x$).

  The rest of our term definition is
  parametrized by a collection of
  operators([Opid]). Operators take bound terms as input and construct another
  term.  For example, there is an operator that takes [[bterm [nvarx] (vterm nvarx)]]
  and constructs the lambda term $\lambda x.x$.
  With that in mind, here is the inductive type([NTerm]) that represents the terms of Nurpl:


 *)
Inductive NTerm {p} : tuniv :=
| vterm: NVar -> NTerm
| sterm : (nat -> NTerm) -> NTerm (* closed free choice sequence *)
| oterm: @Opid p -> list BTerm -> NTerm
with BTerm {p} : tuniv :=
| bterm: (list NVar) -> NTerm -> BTerm.

(*
  The [Opid] type contains one element corresponding to every operator
  of the language, e.g. lambda abstraction, funtion application,
  dependent function type constructor. As a more concrete example,
  the [Can NLambda] is the element of [Opid] that represents lambda
  abstractions.
  To construct a bound term([BTerm]), we need a list of variables and
  an [NTerm] (see the [bterm] constructor). As a concrete example,
   $ \lambda x.x$ is represented in this type
  as [(oterm  (Can NLambda) (bterm [nvarx] (vterm nvarx)))].
*)

(**
  It is a mutually inductive definition that simultaneously defines terms
  and bound terms. As mentioned before, the [vterm] constructor
  takes an [NVar] and constructs an [NTerm]. The other constructor([oterm])
  takes an [Opid] and a list of bound terms ([BTerm]s) and constructs an [NTerm].
  Note that not all members of [NTerm] are meaningful(well-formed).
  For example, the [Opid] corresponding to lambda abstractions must be
  provided with exactly one bound term as argument. Moreover, that
  bound term must have exactly one bound variable. So, we have a function
  [OpBindings] in type [Opid -> list nat] that specifies both the
  number of arguments and the number of bound variables in each argument([BTerm]).
  We will use it soon to define the subcollection of well-formed terms.
*)

(* begin hide *)
Inductive ord :=
| OZ : ord
| OS : ord -> ord
| OL : (nat -> ord) -> ord.

Notation O1 := (OS OZ).

Fixpoint oadd (o1 o2 : ord) :=
  match o1 with
    | OZ => o2
    | OS o => OS (oadd o o2)
    | OL f => OL (fun x => oadd (f x) o2)
  end.

Fixpoint oaddl (ts : list ord) : ord :=
  match ts with
  | nil => OZ
  | n :: ns => oadd n (oaddl ns)
  end.

Fixpoint osize {o} (t : @NTerm o) : ord :=
  match t with
    | vterm _ => O1
    | sterm f => OS (OL (fun x => osize (f x)))
    | oterm op bterms => OS (oaddl (map osize_bterm bterms))
  end
with osize_bterm {o} (bt : BTerm) : ord :=
  match bt with
    | bterm lv nt => osize nt
  end.

Fixpoint opred_type (o : ord) : Set :=
  match o with
    | OZ    => False
    | OS o' => option (opred_type o')
    | OL f  => { n : nat & opred_type (f n) }
  end.

Fixpoint opred (o : ord) : opred_type o -> ord :=
  match o return opred_type o -> ord with
    | OZ    => fun i => match i with end
    | OS o' => fun i => match i with
                          | None => o'
                          | Some t  => opred o' t
                        end
    | OL f  => fun i => match i with
                          | existT _ n t => opred (f n) t
                        end
  end.

Inductive ord_le : ord -> ord -> Type :=
| le_OZ : forall o, ord_le OZ o
| le_OS : forall o1 o2 i, ord_le o1 (opred o2 i) -> ord_le (OS o1) o2
| le_OL : forall f o, (forall n, ord_le (f n) o) -> ord_le (OL f) o.
Hint Constructors ord_le.

Definition ord_lt (o1 o2 : ord) := {i : opred_type o2 & ord_le o1 (opred o2 i)}.

Definition ord_eq o1 o2 := ord_le o1 o2 # ord_le o2 o1.

Notation "o1 << o2" := (ord_lt o1 o2) (at level 0).
Notation "o1 <=< o2" := (ord_le o1 o2) (at level 0).
Notation "o1 =o= o2" := (ord_eq o1 o2) (at level 0).

Lemma not_ord_lt_zero : forall o, !(o << OZ).
Proof.
  induction o; intro olt; unfold ord_lt in olt; exrepnd; allsimpl; tcsp.
Qed.

Lemma ord_le_opred_implies_ord_lt :
  forall o1 o2 t, o1 <=< (opred o2 t) -> o1 << o2.
Proof.
  introv ole.
  exists t; auto.
Qed.

Lemma ord_le_ex_opred_type :
  forall o1 o2,
    opred_type o1
    -> o1 <=< o2
    -> opred_type o2.
Proof.
  induction o1 as [|?|? ind]; introv opt ole; allsimpl; tcsp.
  - destruct opt as [t|].
    + inversion ole as [|? ? t' ole'|]; subst; clear ole; auto.
    + inversion ole as [|? ? t' ole'|]; subst; clear ole; auto.
  - exrepnd.
    inversion ole as [|?|? ? i]; subst; clear ole.
    pose proof (i n) as ole; clear i.
    apply ind in ole; auto.
Qed.

Lemma ord_le_opred_right_implies_le :
  forall o1 o2 (t : opred_type o2),
    o1 <=< (opred o2 t)
    -> o1 <=< o2.
Proof.
  induction o1 as [|? ind|? ind]; introv ole; allsimpl; tcsp.
  - apply (le_OS _ _ t).
    inversion ole as [|? ? t' ole'|]; subst; clear ole.
    apply ind in ole'; auto.
  - inversion ole as [|?|? ? i]; subst; clear ole.
    constructor; introv.
    pose proof (i n) as h; clear i.
    apply ind in h; auto.
Qed.

Lemma ord_le_opred_right_implies_lt :
  forall o1 o2 (t : opred_type o2),
    o1 <=< (opred o2 t)
    -> o1 << o2.
Proof.
  introv ole; exists t; auto.
Qed.

Lemma implies_ord_le_opred_left :
  forall o1 o2 (t1 : opred_type o1),
    o1 <=< o2
    -> (opred o1 t1) <=< o2.
Proof.
  induction o1 as [|? ind|? ind]; introv ole; allsimpl; tcsp.
  - inversion ole as [|? ? t ole'|]; subst; clear ole.
    apply ord_le_opred_right_implies_le in ole'; auto.
    destruct t1; tcsp.
  - inversion ole as [|?|? ? i]; subst; clear ole; exrepnd.
    apply ind; auto.
Qed.

Lemma ord_le_trans :
  forall o1 o2 o3, o1 <=< o2 -> o2 <=< o3 -> o1 <=< o3.
Proof.
  introv ole.
  revert o3.

  induction ole as [|? ? ? ? ind|]; introv ole2; auto; clear ole.

  induction ole2 as [|? ? ? ? ind2|? ? ? ind2]; introv; allsimpl; tcsp.

  - apply (le_OS _ _ i0).
    apply ind.
    destruct i; allsimpl; tcsp.
    apply implies_ord_le_opred_left; auto.

  - exrepnd.
    apply (ind2 n i0); auto.
Qed.
Hint Resolve ord_le_trans : slow.

Lemma ord_lt_trans :
  forall o1 o2 o3, o1 << o2 -> o2 << o3 -> o1 << o3.
Proof.
  introv olt1 olt2.
  allunfold ord_lt; exrepnd.
  exists i.
  eapply ord_le_trans;[exact olt2|].
  apply implies_ord_le_opred_left; auto.
Qed.
Hint Resolve ord_lt_trans : slow.

Lemma implies_ord_le_opred :
  forall o1 o2 (t1 : opred_type o1),
    o1 <=< o2
    -> {t2 : opred_type o2 & (opred o1 t1) <=< (opred o2 t2)}.
Proof.
  induction o1 as [|? ind|? ind]; introv ole; allsimpl; tcsp.

  - inversion ole as [|? ? t ole'|]; subst; clear ole.
    destruct t1; allsimpl.

    + apply ind.
      eapply ord_le_opred_right_implies_le; eauto.

    + exists t; auto.

  - inversion ole as [|?|? ? i]; subst; clear ole; exrepnd.
    pose proof (i n) as h; clear i.
    applydup ind in h as t; auto.
Qed.

Lemma ord_lt_le_trans :
  forall o1 o2 o3, o1 << o2 -> o2 <=< o3 -> o1 << o3.
Proof.
  introv olt1 olt2.
  allunfold ord_lt; exrepnd.
  pose proof (implies_ord_le_opred o2 o3 i olt2) as h; exrepnd.
  exists t2.
  eapply ord_le_trans;[|exact h0]; auto.
Qed.

Lemma implies_ord_le_limit_right :
  forall o f n, o <=< (f n) -> o <=< (OL f).
Proof.
  induction o as [|?|? ind]; introv ole; auto.
  - inversion ole as [|? ? t ole'|]; subst; clear ole.
    apply (le_OS o (OL f) (existT (fun n => opred_type (f n)) n t)); simpl; auto.
  - inversion ole as [|?|? ? i]; subst; clear ole; exrepnd.
    constructor; introv.
    eapply ind; apply i.
Qed.

Lemma ord_le_refl : forall o, o <=< o.
Proof.
  induction o; auto.
  - apply (le_OS o (OS o) None); simpl; auto.
  - constructor; introv.
    eapply implies_ord_le_limit_right; eauto.
Qed.
Hint Resolve ord_le_refl : slow.

Lemma ord_eq_refl : forall o, o =o= o.
Proof.
  introv.
  split; apply ord_le_refl.
Qed.

Lemma ord_eq_sym :
  forall o1 o2, o1 =o= o2 -> o2 =o= o1.
Proof.
  introv oeq.
  allunfold ord_eq; sp.
Qed.

Lemma ord_le_eq_trans :
  forall o1 o2 o3, o1 <=< o2 -> o2 =o= o3 -> o1 <=< o3.
Proof.
  introv ole oeq.
  allunfold ord_eq; repnd.
  eapply ord_le_trans;eauto.
Qed.

Lemma ord_lt_eq_trans :
  forall o1 o2 o3, o1 << o2 -> o2 =o= o3 -> o1 << o3.
Proof.
  introv olt oeq.
  allunfold ord_eq; repnd.
  eapply ord_lt_le_trans;eauto.
Qed.

Lemma implies_ord_lt_OS :
  forall o1 o2, o1 <=< o2 -> o1 << (OS o2).
Proof.
  introv ole.
  unfold ord_lt.
  exists (None : opred_type (OS o2)); simpl; auto.
Qed.

Lemma ord_le_oadd_l :
  forall o1 o2, o1 <=< (oadd o1 o2).
Proof.
  induction o1; introv; auto; simpl.
  - apply (le_OS o1 (OS (oadd o1 o2)) None); simpl; auto.
  - constructor; introv.
    eapply implies_ord_le_limit_right; eauto.
Qed.

Lemma ord_le_OS :
  forall o, o <=< (OS o).
Proof.
  induction o as [|? ind|? ind]; introv; auto; simpl.
  - apply (le_OS o (OS (OS o)) None); simpl; auto.
  - constructor; introv.
    eapply ord_le_trans;[apply ind|].
    apply (le_OS (o n) (OS (OL o)) None); simpl; auto.
    eapply implies_ord_le_limit_right; apply ord_le_refl.
Qed.

Lemma ord_le_oadd_r :
  forall o1 o2, o2 <=< (oadd o1 o2).
Proof.
  induction o1 as [|? ind|? ind]; introv; auto; simpl.
  - apply ord_le_refl.
  - eapply ord_le_trans;[apply ind|]; auto.
    apply ord_le_OS.
  - eapply ord_le_trans;[apply (ind 0)|]; auto.
    eapply implies_ord_le_limit_right; apply ord_le_refl.
Qed.

Lemma ord_lt_OS_implies :
  forall o1 o2,
    o1 << (OS o2)
    -> o1 <=< o2.
Proof.
  introv olt.
  unfold ord_lt in olt; exrepnd; allsimpl.
  destruct i; allsimpl; tcsp.
  eapply ord_le_trans;[exact olt0|].
  apply implies_ord_le_opred_left.
  apply ord_le_refl.
Qed.

Lemma comp_ind_ord :
  forall (P: ord -> Type),
    (forall n, (forall m, m << n -> P m) -> P n)
    -> forall n, P n.
Proof.
 intros P IH n.

 assert (forall n m, ord_lt m n -> P m) as h.
 { intro n0.
   induction n0 as [|n' ind|f ind]; introv h.
   - apply not_ord_lt_zero in h; tcsp.
   - unfold ord_lt in h; exrepnd; allsimpl.
     destruct i; allsimpl.
     + apply IH; auto.
       apply ord_le_opred_implies_ord_lt in h0.
       introv q.
       eapply ord_lt_trans in h0;[|exact q].
       apply ind; auto.
     + apply IH.
       introv ltm.
       apply ind.
       eapply ord_lt_le_trans; eauto.
   - unfold ord_lt in h; exrepnd; allsimpl.
     exrepnd; allsimpl.
     apply ord_le_opred_right_implies_lt in h0.
     apply ind in h0; auto. }

 apply IH; apply h.
Defined.

Definition ntseq {o} : Type := nat -> @NTerm o.

Definition bterm2term {o} (b : @BTerm o) :=
  match b with
    | bterm _ t => t
  end.

(*
Scheme NTerm_mut := Induction for NTerm Sort Prop
with BTerm_mut := Induction for BTerm Sort Prop.
*)

(*
Definition term_rel := NTerm -> NTerm -> Type.
*)

Definition isvar {p} (t : @NTerm p) :=
  match t with
    | vterm _ => true
    | _ => false
  end.

Definition isvariable {p} (t : @NTerm p) :=
  match t with
    | vterm _ => True
    | _ => False
  end.

Definition iscanonical {p} (t : @NTerm p) :=
  match t with
    | oterm (Can _) _ => true
    | sterm _ => true
    | _ => false
  end.

Definition iscan {p} (t : @NTerm p) :=
  match t with
    | oterm (Can _) _ => True
    | sterm _ => True
    | _ => False
  end.

Definition isnoncan {p} (t : @NTerm p) :=
  match t with
    | vterm _ => False
    | sterm _ => False
    | oterm o _ =>
      match o with
        | NCan _ => True
        | _ => False
      end
  end.

Definition isexception {p} (t: @NTerm p) :=
  match t with
    | vterm _ => false
    | sterm _ => false
    | oterm o _ =>
      match o with
        | Exc => true
        | _ => false
      end
  end.

Definition isexc {p} (t: @NTerm p) :=
  match t with
    | vterm _ => False
    | sterm _ => False
    | oterm o _ =>
      match o with
        | Exc => True
        | _ => False
      end
  end.

Definition isabs {p} (t: @NTerm p) :=
  match t with
    | vterm _ => False
    | sterm _ => False
    | oterm o _ =>
      match o with
        | Abs _ => True
        | _ => False
      end
  end.

Definition isseq {p} (t : @NTerm p) :=
  match t with
    | vterm _ => False
    | sterm _ => True
    | oterm _ _ => False
  end.

Ltac d_isnoncan H :=
  match type of H with
      isnoncan ?t =>
      let tlbt := fresh t "lbt" in
      let tnc := fresh t "nc" in
      let tt := fresh "temp" in
      destruct t as [tt|tt|tt tlbt];
        [complete (inverts H as H)|complete (inverts H as H)|];
        destruct tt as [tt|tnc|tex|tabs];
        [ complete(inverts H as H)
        | idtac
        | complete(inverts H as H)
        | complete(inverts H as H)
        ]
  end.

Ltac d_isexc H :=
  match type of H with
      isexc ?t =>
      let tlbt := fresh t "lbt" in
      let tnc := fresh t "nc" in
      let tt := fresh "temp" in
      destruct t as [tt|tt|tt tlbt];
        [complete (inverts H as H)|complete (inverts H as H)|];
        destruct tt as [tt|tnc|tex|tabs];
        [ complete(inverts H as H)
        | complete(inverts H as H)
        | idtac
        | complete(inverts H as H)
        ]
  end.

Ltac d_isabs H :=
  match type of H with
      isabs ?t =>
      let x  := fresh t "x" in
      let bs := fresh t "bs" in
      let tt := fresh "temp" in
      destruct t as [tt|tt|tt tlbt];
        [complete (inverts H as H)|complete (inverts H as H)|];
        destruct tt as [tt|tnc|tex|tabs];
        [ complete(inverts H as H)
        | complete(inverts H as H)
        | complete(inverts H as H)
        | idtac
        ]
  end.


(*Notation "x # b" := (bterm [x] b) (at level 70, right associativity).
(*Check [[ btermO (vterm(nvar 0))]] *)
(* Notation "< N >" := (btermO N). *)
Notation "\\ f" :=
  (oterm (Can NLambda) [[f]]) (at level 70, right associativity).

*)

Notation "(| a , b |)" :=
  (oterm (Can NPair) [bterm [] a, bterm [] b]) (at level 70, right associativity).


(* ------ CONSTRUCTORS ------ *)


(* --- primitives --- *)

(* end hide *)

(** Here are some handy definitions that will
    reduce the verbosity of some of our later definitions.
*)

Definition nobnd {p} (f : @NTerm p) := bterm [] f.

Definition mk_var {p} (nv : NVar) : @NTerm p := vterm nv.

Definition mk_lam {p} (v : NVar) (b : @NTerm p) := oterm (Can NLambda) [bterm [v] b].

Definition mk_fix {p} (f : @NTerm p) := oterm (NCan NFix) [ bterm [] f ].

Definition mk_apply {p} (f a : @NTerm p) := oterm (NCan NApply) [nobnd f , nobnd a].

Definition mk_eapply {p} (f a : @NTerm p) := oterm (NCan NEApply) [nobnd f , nobnd a].

(*
Definition mk_apseq {p} (f : nseq) (a : @NTerm p) := oterm (NCan (NApseq f)) [nobnd a].
 *)

Definition mk_token {p} s : @NTerm p := oterm (Can (NTok s)) [].

Definition mk_utoken {p} (u : get_patom_set p) : @NTerm p := oterm (Can (NUTok u)) [].

Definition mk_exception {p} (a e : @NTerm p) := oterm Exc [nobnd a; nobnd e].

Definition mk_axiom {p} : @NTerm p := oterm (Can NAxiom) [].

Definition mk_inl {p} (x : @NTerm p) := oterm (Can (NInj NInl)) [nobnd x].
Definition mk_inr {p} (x : @NTerm p) := oterm (Can (NInj NInr)) [nobnd x].

Definition mk_equality {p} (t1 t2 T : @NTerm p) :=
  oterm (Can NEquality) [nobnd t1,nobnd t2,nobnd T].

(** %\noindent \\*% We define similar abstractions for other [Opid]s.
    This document does not show them. As mentioned before, one can click
    at the hyperlinked filename that is closest above to open a
    webpage that shows complete contents of this file.
*)

(** %\noindent% Whenever we talk about the [NTerm] of a [BTerm], this is
what we would mean:

*)
Definition get_nt {p} (bt : @BTerm p) : NTerm :=
 match bt with
 | bterm lv nt => nt
 end.

Definition get_vars {p} (bt: @BTerm p) : list NVar :=
 match bt with
 | bterm lv nt => lv
 end.

Definition num_bvars {p} (bt : @BTerm p) := length (get_vars bt).


(**
    We define functions that compute the free variables and
    bound variables of a term.
    Note how these functions have just two cases
    and are robust against addition/deletion of new operators([Opid]s) to the
    language.
    If we had defined [NTerm] in the usual way(with one constructor for each [Opid]),
    these definitions would be of the form of a long pattern match with one case for each [Opid].
    However, these definitions only care about the binding structure.
    We will reap more benefits of this uniformity when we define substitution and alpha equality
    in the next subsection.
*)


(* --- variables --- *)

(* What could be the free vars of [sterm f]?  The union of the free vars of
   all the [f n] for all nats [n]?  For now let's consider closed sequences
   only.
 *)
Fixpoint free_vars {p} (t:@NTerm p) : list NVar :=
  match t with
  | vterm v => [v]
  | sterm _ => []
  | oterm op bts => flat_map free_vars_bterm bts
  end
 with free_vars_bterm {p} (bt : BTerm) :=
  match bt with
  | bterm  lv nt => remove_nvars lv (free_vars nt)
  end.

Fixpoint bound_vars {p} (t : @NTerm p) : list NVar :=
  match t with
  | vterm _ => []
  | sterm _ => []
  | oterm _ bts => flat_map bound_vars_bterm bts
  end
 with bound_vars_bterm {p} (bt : BTerm) :=
  match bt with
  | bterm lv nt => lv ++ bound_vars nt
  end.

Definition all_vars {p} (t : @NTerm p) := free_vars t ++ bound_vars t.

Definition closed {p} (t : @NTerm p) := free_vars t = [].

Definition get_utokens_c {p} (c : @CanonicalOp p) : list (get_patom_set p) :=
  match c with
    | NUTok u => [u]
    | _ => []
  end.

Definition get_utokens_o {p} (o : @Opid p) : list (get_patom_set p) :=
  match o with
    | Can c => get_utokens_c c
    | _ => []
  end.

Fixpoint get_utokens {p} (t : @NTerm p) : list (get_patom_set p) :=
  match t with
    | vterm _ => []
    | sterm _ => []
    | oterm o bterms => (get_utokens_o o) ++ (flat_map get_utokens_b bterms)
  end
with get_utokens_b {p} (bt : @BTerm p) : list (get_patom_set p) :=
       match bt with
         | bterm _ t => get_utokens t
       end.

Definition noutokens {o} (t : @NTerm o) := get_utokens t = [].

(**

  First, we define the [allvars] function that extracts all the
  variables from a term, i.e., both its free and bound variables.  We
  prove that [allvars t] is equivalent as a set to [all_vars t].

 *)

Fixpoint allvars {p} (t : @NTerm p) : list NVar :=
  match t with
    | vterm v => [v]
    | sterm _ => []
    | oterm o bts => flat_map allvarsbt bts
  end
with allvarsbt {p} (bt : BTerm) :=
  match bt with
    | bterm vs t => vs ++ allvars t
  end.

Set Implicit Arguments.

Inductive OList T :=
| OLO : T -> OList T
| OLL : list (OList T) -> OList T
| OLS : (nat -> OList T) -> OList T.

Fixpoint olist_size {T} (l : OList T) : ord :=
  match l with
    | OLO _ => O1
    | OLL l => OS (oaddl (map olist_size l))
    | OLS f => OS (OL (fun x => olist_size (f x)))
  end.

Lemma implies_ord_le_oaddl :
  forall l o,
    {x : ord & LIn x l # o <=< x}
    -> o <=< (oaddl l).
Proof.
  induction l; introv h; exrepnd; allsimpl; tcsp.
  eapply ord_le_trans;[exact h0|]; clear h0.
  repndors; subst; tcsp.
  - apply ord_le_oadd_l.
  - eapply ord_le_trans;[apply IHl|].
    { eexists; dands; eauto 3 with slow. }
    { apply ord_le_oadd_r. }
Qed.

Lemma olist_better_ind {T} :
  forall P : OList T -> Type,
    (forall x : T, P (OLO x))
    -> (forall l, (forall x, LIn x l -> P x) -> P (OLL l))
    -> (forall f, (forall n, P (f n)) -> P (OLS f))
    -> forall o, P o.
Proof.
  introv ho hl hs.

  assert (forall n o, (olist_size o) =o= n -> P o) as Hass;
    [|introv;
       apply Hass with (n := olist_size o);
       apply ord_eq_refl];[].

  induction n as [n Hind] using comp_ind_ord.
  introv Hsz.
  destruct o as [v|l|f]; auto.

  - apply hl; introv i; allsimpl.
    pose proof (Hind (olist_size x)) as h; clear Hind.
    autodimp h hyp; [|apply h; apply ord_eq_refl].
    eapply ord_lt_eq_trans;[|exact Hsz]; clear Hsz.
    apply implies_ord_lt_OS.
    apply implies_ord_le_oaddl.
    exists (olist_size x); dands; eauto 3 with slow.
    rw in_map_iff; eexists; eauto.

  - apply hs; introv; allsimpl.
    pose proof (Hind (olist_size (f n0))) as h; clear Hind.
    autodimp h hyp; [|apply h; apply ord_eq_refl].
    eapply ord_lt_eq_trans;[|exact Hsz]; clear Hsz.
    apply implies_ord_lt_OS.
    eapply implies_ord_le_limit_right; apply ord_le_refl.
Defined.

Inductive in_olist {T} (v : T) : OList T -> Type :=
| in_olist_v : in_olist v (OLO v)
| in_olist_l :
    forall l,
      {o : OList T & LIn o l # in_olist v o}
      -> in_olist v (OLL l)
| in_olist_s :
    forall f,
      {n : nat & in_olist v (f n)}
      -> in_olist v (OLS f).
Hint Constructors in_olist.

Definition subseto {T} (l : list T) (o : OList T) : Type :=
  forall x, LIn x l -> in_olist x o.

Definition osubset {T} (o1 o2 : OList T) :=
  forall x, in_olist x o1 -> in_olist x o2.

Lemma osubset_singleton_OLS_l {T} :
  forall f (l : OList T),
    osubset (OLS f) l <=> (forall n, osubset (f n) l).
Proof.
  unfold osubset.
  introv; split; introv h i; allsimpl.
  - apply h.
    constructor; eexists; eauto.
  - inversion i; exrepnd; subst.
    eapply h; eauto.
Qed.

Lemma implies_osubset_singleton_OLS_r {T} :
  forall (o : @OList T) n f,
    osubset o (f n)
    -> osubset o (OLS f).
Proof.
  introv i j.
  constructor.
  exists n; auto.
Qed.

Lemma implies_osubset_singleton_OLS_r_ex {T} :
  forall (l : OList T) f,
    {n : nat & osubset l (f n)}
    -> osubset l (OLS f).
Proof.
  introv h; exrepnd.
  eapply implies_osubset_singleton_OLS_r; eauto.
Qed.

Definition onil {T} : OList T := OLL [].

Lemma osubset_nil_l {T} :
  forall (l : OList T), osubset onil l.
Proof.
  introv i.
  inversion i; subst; exrepnd; allsimpl; tcsp.
Qed.
Hint Resolve osubset_nil_l : slow.

Lemma in_olist_in_trans {T} :
  forall l (x : T) o,
    in_olist x o
    -> LIn o l
    -> in_olist x (OLL l).
Proof.
  introv i j.
  constructor.
  eexists; eauto.
Qed.

Lemma osubset_in_trans {T} :
  forall (o1 : OList T) o2 l,
    osubset o1 o2
    -> LIn o2 l
    -> osubset o1 (OLL l).
Proof.
  introv i j k.
  constructor.
  eexists; dands; eauto.
Qed.

Lemma osubset_OLO_implies_in_olist_eq {T} :
  forall (o : OList T) x,
    osubset o (OLO x)
    -> (forall v, in_olist v o -> v = x).
Proof.
  introv h q.
  apply h in q.
  inversion q; auto.
Qed.

Lemma osubset_refl {T} :
  forall (l : OList T), osubset l l.
Proof.
  introv i; auto.
Qed.
Hint Resolve osubset_refl : slow.

(*
Lemma olist_in_if_in {T} :
  forall o (l : list (OList T)), LIn o l -> olist_in o (OLL l).
Proof.
  introv i.
  apply olist_in_iff; introv j.
  constructor.
  eexists; dands; eauto.
Qed.
*)

Definition osubset_as_osubseto {T} :
  forall (l : list T) (os : OList T),
    subseto l os <=> osubset (OLL (map (@OLO T) l)) os.
Proof.
  unfold osubset, subseto.
  introv; split; introv h.
  - introv i.
    inversion i as [|? q|]; subst; clear i; exrepnd.
    allrw in_map_iff; exrepnd; subst.
    inversion q0; subst; clear q0; auto.
  - introv i.
    apply h.
    constructor.
    exists (OLO x); dands; auto.
    rw in_map_iff; eexists; eauto.
Qed.

Lemma subseto_nil_l {T} :
  forall (os : OList T), subseto [] os.
Proof.
  introv h; allsimpl; tcsp.
Qed.
Hint Resolve subseto_nil_l : slow.

Lemma subseto_app_l {T} :
  forall l1 l2 (os : OList T),
    subseto (l1 ++ l2) os <=> (subseto l1 os # subseto l2 os).
Proof.
  introv; split; intro h.
  - dands; introv i; apply h; rw in_app_iff; sp.
  - repnd; introv i; allrw in_app_iff; repndors; discover; auto.
Qed.

Lemma implies_subseto_app_r {T} :
  forall l (os1 os2 : list (OList T)),
    (subseto l (OLL os1) [+] subseto l (OLL os2))
    -> subseto l (OLL (os1 ++ os2)).
Proof.
  introv h i.
  constructor.
  repndors; apply h in i; clear h; inversion i; subst; exrepnd;
  eexists; dands; eauto; rw in_app_iff; tcsp.
Qed.

Lemma implies_subseto_cons_ols_r {T} :
  forall l f (os : list (OList T)),
    ({n : nat & subseto l (f n)} [+] subseto l (OLL os))
    -> subseto l (OLL (OLS f :: os)).
Proof.
  introv h i.
  repndors.
  - exrepnd.
    apply h0 in i.
    constructor; simpl.
    eexists; dands; eauto.
  - apply h in i; exrepnd.
    inversion i; subst; exrepnd.
    constructor; simpl.
    eexists; dands; eauto.
Qed.

Lemma subseto_refl {T} :
  forall (l : list T), subseto l (OLL (map (@OLO T) l)).
Proof.
  introv i.
  constructor.
  exists (OLO x); dands; auto.
  rw in_map_iff; eexists; eauto.
Qed.
Hint Resolve osubset_refl : slow.

Lemma subseto_flat_map_l :
  forall {A B} (f : A -> list B) (l : list A) (k : OList B),
    subseto (flat_map f l) k <=> (forall x : A, LIn x l -> subseto (f x) k).
Proof.
  introv; split; intro h.
  - introv i j.
    apply h.
    rw lin_flat_map; eexists; eauto.
  - introv i; allrw lin_flat_map; exrepnd.
    applydup h in i1.
    applydup i2 in i0; auto.
Qed.

Lemma subseto_flat_map2 :
  forall {A B} (f : A -> list B) (g : A -> OList B) (l : list A),
    (forall x : A, LIn x l -> subseto (f x) (g x))
    -> subseto (flat_map f l) (OLL (map g l)).
Proof.
  introv imp i.
  allrw lin_flat_map; exrepnd.
  applydup imp in i1.
  applydup i2 in i0.
  constructor.
  eexists; dands; eauto.
  rw in_map_iff; eexists; eauto.
Qed.

Lemma osubset_singleton_OLL_l {T} :
  forall l (o : OList T),
    osubset (OLL l) o <=> (forall x, LIn x l -> osubset x o).
Proof.
  unfold osubset.
  introv; split; introv h i; allsimpl.
  - introv j.
    apply h.
    constructor.
    eexists; eauto.
  - inversion i; exrepnd; subst; clear i.
    eapply h; eauto.
Qed.

Lemma implies_osubset_singleton_OLL_r {T} :
  forall l (o : OList T),
    {x : OList T & LIn x l # osubset o x}
    -> osubset o (OLL l).
Proof.
  unfold osubset; introv h i; exrepnd.
  constructor.
  eexists; eauto.
Qed.

Definition oeqset {T} (o1 o2 : OList T) :=
  forall x, in_olist x o1 <=> in_olist x o2.

Lemma oeqset_refl {T} :
  forall o : OList T, oeqset o o.
Proof.
  introv; unfold oeqset; introv; sp.
Qed.
Hint Resolve oeqset_refl : slow.

Lemma oeqset_sym {T} :
  forall (o1 o2 : OList T), oeqset o1 o2 <=> oeqset o2 o1.
Proof.
  introv; unfold oeqset; split; intro h; introv; rw h; sp.
Qed.
Hint Resolve oeqset_sym : slow.

Lemma oeqset_trans {T} :
  forall (o1 o2 o3 : OList T), oeqset o1 o2 -> oeqset o2 o3 -> oeqset o1 o3.
Proof.
  unfold oeqset; introv h1 h2; introv.
  rw h1; rw h2; sp.
Qed.
Hint Resolve oeqset_trans : slow.

Fixpoint oflatten {T} (o : OList T) : list (OList T) :=
  match o with
    | OLL l => flat_map oflatten l
    | _ => [o]
  end.

Definition oappl {T} (l : list (OList T)) : OList T :=
  match flat_map oflatten l with
    | [o] => o
    | l => OLL l
  end.

Definition oapp {T} (o1 o2 : OList T) : OList T := oappl [o1, o2].

Lemma in_olist_OLL_app {T} :
  forall x (l1 l2 : list (OList T)),
    in_olist x (OLL (l1 ++ l2))
    <=> (in_olist x (OLL l1) [+] in_olist x (OLL l2)).
Proof.
  introv; split; introv h.
  - inversion h as [|? q|]; clear h; subst; exrepnd.
    allrw in_app_iff; repndors.
    + left; constructor; eexists; eauto.
    + right; constructor; eexists; eauto.
  - constructor; repndors; inversion h as [|? q|]; clear h; subst; exrepnd.
    + eexists;dands;[|eauto]; rw in_app_iff; sp.
    + eexists;dands;[|eauto]; rw in_app_iff; sp.
Qed.

Lemma in_olist_OLL_cons {T} :
  forall x o (l : list (OList T)),
    in_olist x (OLL (o :: l))
    <=> (in_olist x o [+] in_olist x (OLL l)).
Proof.
  introv; split; introv h.
  - inversion h as [|? q|]; clear h; subst; exrepnd.
    allsimpl; repndors; subst; tcsp.
    right; constructor; eexists; eauto.
  - constructor; repndors; inversion h as [|? q|]; clear h; subst; exrepnd; simpl;
    try (complete (eexists; eauto)).
    exists (OLL l0); dands; auto.
    constructor.
    eexists; eauto.
Qed.

Lemma in_olist_OLL_singleton {T} :
  forall x (o : OList T),
    in_olist x (OLL [o]) <=> in_olist x o.
Proof.
  introv; split; intro h.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    allsimpl; repndors; subst; tcsp.
  - constructor; simpl; eexists; eauto.
Qed.

Lemma oeqset_singleton_l {T} :
  forall (o : OList T), oeqset (OLL [o]) o.
Proof.
  repeat introv.
  apply in_olist_OLL_singleton.
Qed.

Lemma implies_oeqset_OLL_OLL2 {T} :
  forall (l1 l2 : list (OList T)),
    (forall o x, LIn o l1 -> in_olist x o -> in_olist x (OLL l2))
    -> (forall o x, LIn o l2 -> in_olist x o -> in_olist x (OLL l1))
    -> oeqset (OLL l1) (OLL l2).
Proof.
  introv h1 h2; introv; split; intro h.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    apply h1 in q0; auto.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    apply h2 in q0; auto.
Qed.

Lemma in_olist_OLL_map {A T} :
  forall x (f : A -> OList T) (l : list A),
    in_olist x (OLL (map f l)) <=> {a : A & LIn a l # in_olist x (f a)}.
Proof.
  introv; split; intro h.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    allrw in_map_iff; exrepnd; subst.
    eexists; eauto.
  - exrepnd.
    constructor; eexists; dands; eauto.
    rw in_map_iff; eexists; eauto.
Qed.

Lemma in_olist_OLL_flat_map {A T} :
  forall x (f : A -> list (OList T)) (l : list A),
    in_olist x (OLL (flat_map f l))
    <=> {a : A & LIn a l # in_olist x (OLL (f a))}.
Proof.
  introv; split; intro h.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    allrw lin_flat_map; exrepnd; subst.
    eexists; eauto.
  - exrepnd.
    constructor.
    inversion h0; subst; exrepnd; clear h0.
    eexists; dands; eauto.
    rw lin_flat_map; dands.
    eexists; dands; eauto.
Qed.

Lemma oeqset_OLL_oflatten {T} :
  forall o : OList T, oeqset (OLL (oflatten o)) o.
Proof.
  induction o as [|l ind|f ind] using olist_better_ind; allsimpl.
  - apply oeqset_singleton_l.
  - introv; split; intro h; allrw @in_olist_OLL_flat_map; exrepnd.
    + applydup ind in h1.
      apply h2 in h0.
      constructor.
      eexists; dands; eauto.
    + inversion h as [|? q|]; clear h; subst; exrepnd.
      applydup ind in q1.
      eexists; dands; eauto.
      apply q2; auto.
  - apply oeqset_singleton_l.
Qed.

Lemma oeqset_oapp_OLL_app_oflatten {T} :
  forall (o1 o2 : OList T),
    oeqset (oapp o1 o2) (OLL (oflatten o1 ++ oflatten o2)).
Proof.
  repeat introv.
  unfold oapp, oappl; simpl; allrw app_nil_r.
  remember (oflatten o1) as l1.
  remember (oflatten o2) as l2.
  destruct l1; simpl.
  - destruct l2; simpl; tcsp.
    destruct l2; simpl; tcsp.
    rw @oeqset_singleton_l; tcsp.
  - destruct l1; simpl; tcsp.
    destruct l2; simpl; tcsp.
    rw @oeqset_singleton_l; tcsp.
Qed.

Lemma oeqset_app_if {T} :
  forall (l1 l2 l3 l4 : list (OList T)),
    oeqset (OLL l1) (OLL l3)
    -> oeqset (OLL l2) (OLL l4)
    -> oeqset (OLL (l1 ++ l2)) (OLL (l3 ++ l4)).
Proof.
  unfold oeqset.
  introv h1 h2; introv.
  split; introv q;
  allrw @in_olist_OLL_app; repndors;
  try (complete (apply h1 in q; sp));
  try (complete (apply h2 in q; sp)).
Qed.

Lemma oeqset_cons_if {T} :
  forall o1 o2 (l1 l2 : list (OList T)),
    oeqset o1 o2
    -> oeqset (OLL l1) (OLL l2)
    -> oeqset (OLL (o1 :: l1)) (OLL (o2 :: l2)).
Proof.
  unfold oeqset.
  introv h1 h2; introv.
  split; introv q;
  allrw @in_olist_OLL_cons; repndors; tcsp;
  try (complete (apply h1 in q; sp));
  try (complete (apply h2 in q; sp)).
Qed.

Lemma fold_oapp {T} :
  forall (o1 o2 : OList T), oeqset (oapp o1 o2) (OLL [o1, o2]).
Proof.
  introv.
  eapply oeqset_trans;[apply oeqset_oapp_OLL_app_oflatten|].
  assert ([o1,o2] = [o1] ++ [o2]) as e by sp.
  rw e; clear e.
  apply oeqset_app_if.
  - eapply oeqset_trans;[apply oeqset_OLL_oflatten|].
    apply oeqset_sym.
    apply oeqset_singleton_l.
  - eapply oeqset_trans;[apply oeqset_OLL_oflatten|].
    apply oeqset_sym.
    apply oeqset_singleton_l.
Qed.

Lemma oapp_nil_l {T} :
  forall (o : OList T), oeqset (oapp onil o) o.
Proof.
  introv.
  eapply oeqset_trans;[apply oeqset_oapp_OLL_app_oflatten|].
  simpl.
  apply oeqset_OLL_oflatten.
Qed.

Lemma flat_map_eq_singleton_implies :
  forall {A B} (f : A -> list B) l x,
    flat_map f l = [x] -> {a : A & LIn a l # f a = [x]}.
Proof.
  induction l; introv e; allsimpl; ginv.
  remember (f a) as l1.
  destruct l1; allsimpl.
  - apply IHl in e; exrepnd.
    eexists; dands; eauto.
  - destruct l1; allsimpl; ginv.
    remember (flat_map f l) as l2.
    destruct l2; allsimpl; ginv.
    exists a; sp.
Qed.

Lemma oflatten_singleton {T} :
  forall o1 o2 : OList T,
    oflatten o1 = [o2] -> oflatten o2 = [o2].
Proof.
  induction o1 as [|l ind|f ind] using olist_better_ind;
  introv h; allsimpl; ginv; allsimpl; auto.
  apply flat_map_eq_singleton_implies in h; exrepnd.
  eapply ind; eauto.
Qed.

Lemma oeqset_OLL_cons {T} :
  forall (o : OList T) l, oeqset (OLL (o :: l)) (oapp o (OLL l)).
Proof.
  introv.
  eapply oeqset_trans;[|apply oeqset_sym; apply fold_oapp].
  apply oeqset_cons_if; eauto 3 with slow.
  eapply oeqset_sym.
  apply oeqset_singleton_l.
Qed.

Lemma oeqset_flat_map_oflatten {T} :
  forall (l : list (OList T)),
    oeqset (OLL (flat_map oflatten l)) (OLL l).
Proof.
  induction l; simpl; eauto 3 with slow.
  rw cons_as_app.
  apply oeqset_app_if; auto.
  eapply oeqset_trans;[apply oeqset_OLL_oflatten|].
  apply oeqset_sym.
  apply oeqset_singleton_l.
Qed.

Lemma oappl_nil {T} : @oappl T [] = OLL [].
Proof. sp. Qed.
Hint Rewrite @oappl_nil : slow.

Lemma oappl_OLL_nil {T} :
  oappl [OLL []] = @OLL T [].
Proof.
  sp.
Qed.
Hint Rewrite @oappl_OLL_nil : slow.

Lemma in_oflatten_singleton {T} :
  forall (o1 o2 : OList T),
    LIn o2 (oflatten o1) -> oflatten o2 = [o2].
Proof.
  induction o1 as [|l ind|f ind] using olist_better_ind;
  introv i; allsimpl; ginv; allsimpl; auto; repndors; subst; tcsp.
  allrw lin_flat_map; exrepnd.
  eapply ind; eauto.
Qed.

Lemma in_oflatten_diff_OLL {T} :
  forall (o1 o2 : OList T) l,
    LIn o2 (oflatten o1) -> o2 <> OLL l.
Proof.
  induction o1 as [|l ind|f ind] using olist_better_ind;
  introv i; introv e; allsimpl; ginv; allsimpl; auto; repndors; subst; tcsp; ginv.
  allrw lin_flat_map; exrepnd.
  eapply ind; eauto.
Qed.

Lemma subset_flat_map_oflatten_singleton {T} :
  forall (k l : list (OList T)),
    subset k (flat_map oflatten l)
    -> flat_map oflatten k = k.
Proof.
  induction k; introv h; allsimpl; auto.
  allrw @cons_subset; repnd.
  allrw lin_flat_map; exrepnd.
  apply in_oflatten_singleton in h1; rw h1; simpl; f_equal.
  eapply IHk; eauto.
Qed.

Lemma osubset_app_left {T} :
  forall (l1 l2 l : list (OList T)),
    osubset (OLL l1) (OLL l)
    -> osubset (OLL l2) (OLL l)
    -> osubset (OLL (l1 ++ l2)) (OLL l).
Proof.
  introv h1 h2 i.
  apply in_olist_OLL_app in i; repndors.
  - apply h1 in i; auto.
  - apply h2 in i; auto.
Qed.

Lemma oappl_cons_oappl {T} :
  forall l1 l2 : list (OList T),
    oappl (oappl l1 :: l2) = oappl (l1 ++ l2).
Proof.
  introv; unfold oappl; simpl.
  rw flat_map_app.
  remember (flat_map oflatten l1) as k1.
  remember (flat_map oflatten l2) as k2.
  destruct k1; simpl; auto.
  destruct k1; simpl; auto.
  - symmetry in Heqk1.
    apply flat_map_eq_singleton_implies in Heqk1; exrepnd.
    apply oflatten_singleton in Heqk0; rw Heqk0; simpl; auto.
  - symmetry in Heqk1.

    assert (LIn o (flat_map oflatten l1)) as i1.
    { rw Heqk1; simpl; sp. }
    assert (LIn o0 (flat_map oflatten l1)) as i2.
    { rw Heqk1; simpl; sp. }
    assert (subset k1 (flat_map oflatten l1)) as ss.
    { rw Heqk1; repeat (apply subset_cons1); auto. }

    allrw lin_flat_map; exrepnd.
    apply in_oflatten_singleton in i3.
    apply in_oflatten_singleton in i0.
    apply subset_flat_map_oflatten_singleton in ss.
    rw i0; rw i3; rw ss; simpl; auto.
Qed.
Hint Rewrite @oappl_cons_oappl : slow.

Lemma implies_oappl_cons {T} :
  forall (o : OList T) l1 l2,
    oappl l1 = oappl l2
    -> oappl (o :: l1) = oappl (o :: l2).
Proof.
  introv h.
  allunfold @oappl; allsimpl.
  remember (oflatten o) as k1.
  remember (flat_map oflatten l1) as k2.
  remember (flat_map oflatten l2) as k3.
  destruct k1; allsimpl; tcsp; ginv.
  destruct k1; allsimpl; tcsp; ginv.
  - destruct k2; allsimpl; tcsp; ginv.
    + destruct k3; allsimpl; tcsp; ginv.
      destruct k3; allsimpl; tcsp; ginv.
      subst.
      assert (LIn (OLL []) (flat_map oflatten l2)) as i.
      { rw <- Heqk3; simpl; tcsp. }
      rw lin_flat_map in i; exrepnd.
      apply in_oflatten_singleton in i0; allsimpl; ginv.
    + destruct k2; allsimpl; tcsp; ginv.
      * destruct k3; allsimpl; tcsp; ginv.
        { subst.
          assert (LIn (OLL []) (flat_map oflatten l1)) as i.
          { rw <- Heqk2; simpl; tcsp. }
          rw lin_flat_map in i; exrepnd.
          apply in_oflatten_singleton in i0; allsimpl; ginv. }
        { destruct k3; allsimpl; tcsp; ginv.
          subst.
          assert (LIn (OLL (o2 :: o3 :: k3)) (flat_map oflatten l1)) as i.
          { rw <- Heqk2; simpl; tcsp. }
          rw lin_flat_map in i; exrepnd.
          eapply in_oflatten_diff_OLL in i0; destruct i0; eauto. }
      * destruct k3; allsimpl; tcsp; ginv.
        destruct k3; allsimpl; tcsp; ginv.
        subst.
        assert (LIn (OLL (o1 :: o2 :: k2)) (flat_map oflatten l2)) as i.
        { rw <- Heqk3; simpl; tcsp. }
        rw lin_flat_map in i; exrepnd.
        eapply in_oflatten_diff_OLL in i0; destruct i0; eauto.
  - destruct k2; allsimpl; tcsp; ginv.
    + destruct k3; allsimpl; tcsp; ginv.
      destruct k3; allsimpl; tcsp; ginv.
      subst.
      assert (LIn (OLL []) (flat_map oflatten l2)) as i.
      { rw <- Heqk3; simpl; tcsp. }
      rw lin_flat_map in i; exrepnd.
      apply in_oflatten_singleton in i0; allsimpl; ginv.
    + destruct k2; allsimpl; tcsp; ginv.
      * destruct k3; allsimpl; tcsp; ginv.
        { subst.
          assert (LIn (OLL []) (flat_map oflatten l1)) as i.
          { rw <- Heqk2; simpl; tcsp. }
          rw lin_flat_map in i; exrepnd.
          apply in_oflatten_singleton in i0; allsimpl; ginv. }
        { destruct k3; allsimpl; tcsp; ginv.
          subst.
          assert (LIn (OLL (o3 :: o4 :: k3)) (flat_map oflatten l1)) as i.
          { rw <- Heqk2; simpl; tcsp. }
          rw lin_flat_map in i; exrepnd.
          eapply in_oflatten_diff_OLL in i0; destruct i0; eauto. }
      * destruct k3; allsimpl; tcsp; ginv.
        destruct k3; allsimpl; tcsp; ginv.
        subst.
        assert (LIn (OLL (o2 :: o3 :: k2)) (flat_map oflatten l2)) as i.
        { rw <- Heqk3; simpl; tcsp. }
        rw lin_flat_map in i; exrepnd.
        eapply in_oflatten_diff_OLL in i0; destruct i0; eauto.
Qed.

Lemma oappl_cons_oappl2 {T} :
  forall (o : OList T) l1 l2,
    oappl (o :: oappl l1 :: l2)
    = oappl (o :: l1 ++ l2).
Proof.
  introv.
  apply implies_oappl_cons.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @oappl_cons_oappl2 : slow.

Lemma oappl_cons_oappl3 {T} :
  forall (o1 o2 : OList T) l1 l2,
    oappl (o1 :: o2 :: oappl l1 :: l2)
    = oappl (o1 :: o2 :: l1 ++ l2).
Proof.
  introv.
  repeat (apply implies_oappl_cons).
  autorewrite with slow; auto.
Qed.
Hint Rewrite @oappl_cons_oappl3 : slow.

Lemma oappl_cons_oappl4 {T} :
  forall (o1 o2 o3 : OList T) l1 l2,
    oappl (o1 :: o2 :: o3 :: oappl l1 :: l2)
    = oappl (o1 :: o2 :: o3 :: l1 ++ l2).
Proof.
  introv.
  repeat (apply implies_oappl_cons).
  autorewrite with slow; auto.
Qed.
Hint Rewrite @oappl_cons_oappl4 : slow.

Lemma oappl_cons_oappl5 {T} :
  forall (o1 o2 o3 o4 : OList T) l1 l2,
    oappl (o1 :: o2 :: o3 :: o4 :: oappl l1 :: l2)
    = oappl (o1 :: o2 :: o3 :: o4 :: l1 ++ l2).
Proof.
  introv.
  repeat (apply implies_oappl_cons).
  autorewrite with slow; auto.
Qed.
Hint Rewrite @oappl_cons_oappl5 : slow.

Lemma oappl_app_oappl {T} :
  forall (l1 l2 : list (OList T)),
    oappl (l1 ++ [oappl l2])
    = oappl (l1 ++ l2).
Proof.
  induction l1; introv; simpl.
  - rw @oappl_cons_oappl; allrw app_nil_r; auto.
  - apply implies_oappl_cons; auto.
Qed.

Lemma oappl_app_as_oapp {T} :
  forall (l1 l2 : list (OList T)),
    oappl (l1 ++ l2) = oapp (oappl l1) (oappl l2).
Proof.
  unfold oapp; introv.
  rw @oappl_cons_oappl.
  rw @oappl_app_oappl; auto.
Qed.

Lemma oapp_assoc {T} :
  forall (o1 o2 o3 : OList T),
    oapp (oapp o1 o2) o3 = oapp o1 (oapp o2 o3).
Proof.
  introv; unfold oapp.
  allrw @oappl_cons_oappl; simpl.
  allrw @oappl_cons_oappl2; simpl; auto.
Qed.

Lemma oeqset_oappl_cons {T} :
  forall (o : OList T) l, oappl (o :: l) = oapp o (oappl l).
Proof.
  introv; unfold oapp.
  rw @oappl_cons_oappl2; allrw app_nil_r; auto.
Qed.

Lemma oeqset_oappl_OLL {T} :
  forall l : list (OList T),
    oeqset (oappl l) (OLL l).
Proof.
  induction l; simpl; eauto 3 with slow.
  rw @oeqset_oappl_cons.
  eapply oeqset_trans;[apply fold_oapp|].
  apply oeqset_cons_if; eauto 3 with slow.
  eapply oeqset_trans;[apply oeqset_singleton_l|]; auto.
Qed.

Lemma in_olist_oapp {T} :
  forall x (o1 o2 : OList T),
    in_olist x (oapp o1 o2) <=> (in_olist x o1 [+] in_olist x o2).
Proof.
  introv.
  rw @oeqset_oapp_OLL_app_oflatten.
  rw @in_olist_OLL_app.
  allrw @oeqset_OLL_oflatten; sp.
Qed.

Lemma oeqset_oapp_sym {T} :
  forall (o1 o2 : OList T), oeqset (oapp o1 o2) (oapp o2 o1).
Proof.
  introv; unfold oeqset; introv; split; intro h; allrw @in_olist_oapp;
  repndors; tcsp.
Qed.

Lemma oapp_OLL_left {T} :
  forall l (o : OList T),
    oeqset (oapp (OLL l) o) (OLL (l ++ [o])).
Proof.
  repeat introv.

  split; intro h;
  allrw @in_olist_oapp;
  allrw @in_olist_OLL_app;
  allrw @oeqset_singleton_l; tcsp.
Qed.

Lemma implies_oeqset_OLL_OLL {T} :
  forall (l1 l2 : list (OList T)),
    (forall o x, LIn o l1 -> in_olist x o -> {z : OList T & LIn z l2 # in_olist x z})
    -> (forall o x, LIn o l2 -> in_olist x o -> {z : OList T & LIn z l1 # in_olist x z})
    -> oeqset (OLL l1) (OLL l2).
Proof.
  introv h1 h2; introv; split; intro h.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    apply h1 in q0; auto.
  - inversion h as [|? q|]; subst; clear h; exrepnd.
    apply h2 in q0; auto.
Qed.

Lemma oeqset_oapp_if {T} :
  forall (o1 o2 o3 o4 : OList T),
    oeqset o1 o3
    -> oeqset o2 o4
    -> oeqset (oapp o1 o2) (oapp o3 o4).
Proof.
  introv oeq1 oeq2.
  constructor; introv i;
  allrw @in_olist_oapp; repndors;
  try (complete (apply oeq1 in i; tcsp));
  try (complete (apply oeq2 in i; tcsp)).
Qed.

Lemma osubset_oapp_if {T} :
  forall (o1 o2 o3 o4 : OList T),
    osubset o1 o3
    -> osubset o2 o4
    -> osubset (oapp o1 o2) (oapp o3 o4).
Proof.
  introv oeq1 oeq2.
  introv i;
  allrw @in_olist_oapp; repndors;
  try (complete (apply oeq1 in i; tcsp));
  try (complete (apply oeq2 in i; tcsp)).
Qed.

Lemma osubset_trans {T} :
  forall (o1 o2 o3 : OList T), osubset o1 o2 -> osubset o2 o3 -> osubset o1 o3.
Proof.
  introv h1 h2 i.
  apply h2; apply h1; auto.
Qed.

Lemma oeqset_implies_osubset {T} :
  forall (o1 o2 : OList T), oeqset o1 o2 -> osubset o1 o2.
Proof.
  introv h i.
  apply h; auto.
Qed.

Lemma implies_osubset_oapp {T} :
  forall o o1 o2 : OList T,
    (osubset o o1 [+] osubset o o2)
    -> osubset o (oapp o1 o2).
Proof.
  introv h i.
  apply in_olist_oapp; sp.
Qed.

Lemma osubset_app_if {T} :
  forall (l1 l2 l3 l4 : list (OList T)),
    osubset (OLL l1) (OLL l3)
    -> osubset (OLL l2) (OLL l4)
    -> osubset (OLL (l1 ++ l2)) (OLL (l3 ++ l4)).
Proof.
  introv h1 h2 i.
  allrw @in_olist_OLL_app; repndors.
  - apply h1 in i; sp.
  - apply h2 in i; sp.
Qed.

Lemma subseto_oeqset {T} :
  forall l (o1 o2 : OList T),
    subseto l o1
    -> oeqset o1 o2
    -> subseto l o2.
Proof.
  introv h1 h2 i.
  apply h2; auto.
Qed.

Definition OVar := OList NVar.
Definition ovar_v v : OVar := OLO v.
Definition ovar_l l : OVar := OLL l.
Definition ovar_s f : OVar := OLS f.

Fixpoint allovars {p} (t : @NTerm p) : OVar :=
  match t with
    | vterm v => ovar_v v
    | sterm f => ovar_s (fun n => allovars (f n))
    | oterm o bts => oappl (map allovarsbt bts)
  end
with allovarsbt {p} (bt : BTerm) : OVar :=
       match bt with
         | bterm vs t => oappl (map ovar_v vs ++ [allovars t])
       end.

Definition disj_ovar (v : NVar) l := !(in_olist v l).

Definition disj_ovars (vs : list NVar) (os : OVar) : Prop :=
  forall v o, LIn v vs -> disj_ovar v o.

Definition sat_ntseq {o} (f : ntseq) (P : @NTerm o -> Prop) : Prop :=
  forall n, P (f n).

(** % \noindent \\* % We define
    a predicate [nt_wf] on [NTerm] such that
    [nt_wf nt] asserts that [nt] is a well-formed term.  %\\* %
*)
Inductive nt_wf {p} : @NTerm p -> [univ] :=
| wfvt: forall nv, nt_wf (vterm nv)
| wfst: forall f,
          (forall n, nt_wf (f n) # closed (f n) # noutokens (f n))
          -> nt_wf (sterm f)
| wfot: forall (o: Opid) (lnt: list BTerm),
          (forall l, LIn l lnt -> bt_wf l)
          -> map (num_bvars) lnt
             = OpBindings o
          -> nt_wf (oterm o lnt)
with bt_wf {p} : @BTerm p -> [univ] :=
| wfbt : forall (lnv : list NVar) (nt: NTerm),
           nt_wf nt -> bt_wf (bterm lnv nt).
Hint Constructors nt_wf bt_wf.

(*  For example, the Opid [(Can NLambda)] takes only one [BTerm] an that [BTerm]
  must have exactly one bound variable.
  Hence [OpBindings (Can NLambda) = [1]]. *)

(** % \noindent \\* %
  The only interesting case here is for the [oterm] case. The
  [wfot] constructor requires
  that the number of bound variables of the bound terms in the list
  match the signature ([OpBindings o]) of the corresponding operator [o].

  % \noindent \\* % We abstract the [Opid]s into two categories, canonical
    and noncanonical.

  [
    Inductive Opid : Set :=

     | Can  : CanonicalOp -> Opid

     | NCan : NonCanonicalOp -> Opid.

  ]
% \noindent \\* % This distinction is important from the point of view of computation
    and simplifies many definitions and properties about computation and
    also makes them more easily extensible.
    Nuprl has a lazy computation system and
    an [NTerm] is in normal(canonical) form if its outermost [Opid] is a [CanonicalOp].
    No further computation is performed on terms in canonical form.
    For example, lambda abstraction are constructed by the following [Opid] :

% \noindent \\* % [Can NLambda]

% \noindent \\* % We have [OpBindings (Can NLambda) = [1]].


    On the other hand, an [NTerm] whose outermost [Opid] is a [NonCanonicalOp] is
    not in normal form and can compute to some other term, or to an error.
    An an  example, terms denoting function applications are constructed by the
    following [Opid]:
% \noindent \\* % [NCan NApply]

% \noindent \\* % We have [OpBindings (NCan NApply) = [0,0]].


    The only restriction in defining [CanonicalOp] and [NonCanonicalOp] is
    that the equality in these types should be decidable.
    We will soon show the full-blown definition of
    the [Opid]s of Nuprl.
*)

(* Howe's T_0(L) *)
Definition isprogram {p} (t : @NTerm p) := closed t # nt_wf t.

(** %\noindent \\*% Now, we will describe the [Opid]s of Nuprl and then describe some
other useful definitions and lemmas about [NTerm]. *)


(* begin hide *)

Definition isvalue_like {o} (t : @NTerm o) := iscan t [+] isexc t.
Definition is_can_or_exc {p} (t : @NTerm p) := iscan t [+] isexc t.
Definition isp_can_or_exc {p} (t : @NTerm p) := isprogram t # is_can_or_exc t.

Lemma is_can_or_exc_implies_isvalue_like {o} :
  forall (t : @NTerm o),
    is_can_or_exc t -> isvalue_like t.
Proof.
  introv h.
  unfold isvalue_like; unfold is_can_or_exc in h; sp.
Qed.
Hint Resolve is_can_or_exc_implies_isvalue_like : slow.

Lemma isp_can_or_exc_implies_is_program {p} :
  forall t : @NTerm p, isp_can_or_exc t -> isprogram t.
Proof.
  introv i; inversion i; sp.
Qed.
Hint Resolve isp_can_or_exc_implies_is_program : slow.

Lemma isexc_exc {o} :
  forall (l : list (@BTerm o)),
    isexc (oterm Exc l).
Proof. sp. Qed.
Hint Resolve isexc_exc.

Lemma iscan_can {o} :
  forall c (l : list (@BTerm o)),
    iscan (oterm (Can c) l).
Proof. sp. Qed.
Hint Resolve iscan_can.

Lemma isnoncan_noncan {o} :
  forall nc (l : list (@BTerm o)),
    isnoncan (oterm (NCan nc) l).
Proof. sp. Qed.
Hint Resolve isnoncan_noncan.

Lemma isabs_abs {o} :
  forall abs (l : list (@BTerm o)),
    isabs (oterm (Abs abs) l).
Proof. sp. Qed.
Hint Resolve isabs_abs.

Lemma noncan_not_is_can_or_exc {p} :
  forall e : @NTerm p,
    isnoncan e
    -> is_can_or_exc e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [|?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
  destruct Hisv as [Hisv|Hisv]; auto.
Qed.
Hint Resolve noncan_not_is_can_or_exc : slow.

Lemma isabs_not_is_can_or_exc {p} :
  forall e : @NTerm p,
    isabs e
    -> is_can_or_exc e
    -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [|?|o lbt]; allsimpl; cpx.
  destruct o; cpx.
  destruct Hisv as [Hisv|Hisv]; auto.
Qed.
Hint Resolve isabs_not_is_can_or_exc : slow.

Definition ispexc {p} (t : @NTerm p) := isexc t # isprogram t.

Lemma ispexc_implies_is_can_or_exc {p} :
  forall t : @NTerm p, ispexc t -> is_can_or_exc t.
Proof.
  introv i.
  destruct i as [isp ise].
  right; sp.
Qed.

Lemma isexc_exception {o} :
  forall a e : @NTerm o, isexc (mk_exception a e).
Proof. sp. Qed.
Hint Resolve isexc_exception : slow.

Lemma is_can_or_exc_isexc {o} :
  forall t : @NTerm o, isexc t -> is_can_or_exc t.
Proof. sp. Qed.
Hint Resolve is_can_or_exc_isexc : slow.

Lemma isvalue_like_can {o} :
  forall t : @NTerm o, iscan t -> isvalue_like t.
Proof. sp. Qed.
Hint Resolve isvalue_like_can : slow.

Lemma isvalue_like_exc {o} :
  forall t : @NTerm o, isexc t -> isvalue_like t.
Proof. sp. Qed.
Hint Resolve isvalue_like_exc : slow.



Lemma osize_subterm2 {o} :
  forall (op : @Opid o) bs b,
    LIn b bs -> (osize_bterm b) << (osize (oterm op bs)).
Proof.
  simpl.
  induction bs; intros ? Hin; inverts Hin as; simpl.
  - exists (None : option (opred_type (oadd (osize_bterm b) (oaddl (map osize_bterm bs))))); simpl.
    apply ord_le_oadd_l.
  - intro Hin.
    apply IHbs in Hin; clear IHbs.
    exists (None : option (opred_type (oadd (osize_bterm a) (oaddl (map osize_bterm bs))))); simpl.
    eapply ord_le_trans;[|apply ord_le_oadd_r].
    apply ord_lt_OS_implies in Hin; auto.
Defined.

Lemma osize_subterm3 {o} :
  forall (op : @Opid o) bs t vs,
    LIn (bterm vs t) bs
    -> (osize t) << (osize (oterm op bs)).
Proof.
  introv i.
  apply (osize_subterm2 op) in i; allsimpl; auto.
Defined.

Lemma NTerm_better_ind2 {p} :
  forall P : (@NTerm p) -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall f, (forall n, P (f n)) -> P (sterm f))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt nt': NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt)
              -> (osize nt') <=< (osize nt)
              -> P nt'
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 intros P Hvar Hseq Hbt.

 assert (forall n t, (osize t) =o= n -> P t) as Hass;
   [|introv;
      apply Hass with (n := osize t);
      apply ord_eq_refl].

 induction n as [n Hind] using comp_ind_ord.
 intros t Hsz.
 destruct t as [v|f|op bs].

 - clear Hseq Hbt.
   apply Hvar.

 - clear Hvar Hbt.
   apply Hseq; introv; allsimpl; clear Hseq.

   pose proof (Hind (osize (f n0))) as h; clear Hind.
   autodimp h hyp; [|apply h; apply ord_eq_refl].
   eapply ord_lt_eq_trans;[|exact Hsz]; clear Hsz.
   apply implies_ord_lt_OS.
   eapply implies_ord_le_limit_right.
   apply ord_le_refl.

 - apply Hbt.
   introv Hin Hs; allsimpl.
   apply (Hind (osize nt')); auto.
   { eapply ord_lt_eq_trans;[|exact Hsz]; clear Hsz.
     apply implies_ord_lt_OS.
     eapply ord_le_trans;[exact Hs|]; clear Hs.
     pose proof (osize_subterm3 op bs nt lv Hin) as h; allsimpl.
     apply ord_lt_OS_implies; auto. }
   apply ord_eq_refl.
Defined.

Lemma NTerm_better_ind {p} :
  forall P : @NTerm p -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall f, (forall n, P (f n)) -> P (sterm f))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt : NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt) -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 introv Hv Hs Hind.
 apply NTerm_better_ind2; auto.
 introv Hx.
 apply Hind.
 introv Hin.
 eapply Hx in Hin; eauto.
 apply ord_le_refl.
Defined.

Fixpoint size {p} (t : @NTerm p) : nat :=
  match t with
  | vterm _ => 1
  | sterm _ => 1
  | oterm op bterms => S (addl (map size_bterm bterms))
  end
 with size_bterm {p} (bt: BTerm) :=
  match bt with
  | bterm lv nt => size nt
  end.

Lemma size_subterm2 {p} :
  forall (o : @Opid p) (lb : list BTerm) (b : BTerm) ,
    LIn b lb
    -> size_bterm b <  size (oterm o lb).
Proof.
  simpl. induction lb; intros ? Hin; inverts Hin as; simpl.
  - unfold lt. apply le_n_S.
    apply le_plus_l.
  - intros Hin. apply IHlb in Hin. clear IHlb.
    eapply lt_le_trans; eauto.
    apply le_n_S. apply le_plus_r.
Defined.

Lemma size_subterm3 {p} :
  forall (o : @Opid p) (lb : list BTerm) (nt : NTerm) (lv : list NVar) ,
    LIn (bterm lv nt) lb
    -> size nt <  size (oterm o lb).
Proof.
 introv X.
 apply (@size_subterm2 p) with (o:=o) in X. auto.
Defined.

Lemma NTerm_simple_better_ind2 {p} :
  forall P : (@NTerm p) -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall f, P (sterm f))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt nt': NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt)
              -> size nt' <= size nt
              -> P nt'
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 intros P Hvar Hseq Hbt.

 assert (forall n t, (size t) = n -> P t) as Hass;
   [|introv; apply Hass with (n := size t); reflexivity].

 induction n as [n Hind] using comp_ind_type.
 intros t Hsz.
 destruct t as [v|f|op bs]; auto.

 apply Hbt.
 introv Hin Hs; allsimpl.
 apply (Hind (size nt')); auto.
 eapply le_lt_trans;[exact Hs|].
 pose proof (size_subterm3 op bs nt lv Hin) as h; allsimpl.
 eapply lt_le_trans;[exact h|].
 rewrite Hsz; auto.
Defined.

Lemma NTerm_simple_better_ind {p} :
  forall P : @NTerm p -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall f, P (sterm f))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt : NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt) -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 introv Hv Hs Hind.
 apply NTerm_simple_better_ind2; auto.
 introv Hx.
 apply Hind.
 introv Hin.
 eapply Hx in Hin; eauto.
Defined.

Fixpoint NTerm_BTerm_mutual_ind {p}
    (PN : @NTerm p -> Type) (PB : BTerm -> Type)
    (vcase : forall n : NVar, PN (vterm n))
    (scase : forall f, (forall n, PN (f n)) -> PN (sterm f))
    (bcase: forall (lv : list NVar) (nt : NTerm),
             PN nt ->  PB (bterm lv nt))
    (ocase: forall (o : Opid) (lbt : list BTerm),
            (forall (bt : BTerm),
               (LIn bt lbt) -> PB bt)
            -> PN (oterm o lbt))
    (t : NTerm) {struct t}  : PN t
with
    BTerm_NTerm_mutual_ind {p} (PN : @NTerm p -> Type) (PB : BTerm -> Type)
    (vcase : forall n : NVar, PN (vterm n))
    (scase : forall f, (forall n, PN (f n)) -> PN (sterm f))
    (bcase: forall (lv : list NVar) (nt : NTerm),
             PN nt ->  PB (bterm lv nt))
    (ocase: forall (o : Opid) (lbt : list BTerm),
            (forall (bt : BTerm),
               (LIn bt lbt) -> PB bt)
            -> PN (oterm o lbt))
    (bt : BTerm) {struct bt}  : PB bt.
Proof.
  - destruct t as [?|f|o lbt];[ apply vcase; fail| |].
    { apply scase; auto; introv.
      apply NTerm_BTerm_mutual_ind with (PB := PB); auto. }
    apply ocase.
    introv Hin.
    induction lbt as [| btt lbt HBInd];[inverts Hin|].
    dorn Hin.
    + rw <- Hin.
      apply BTerm_NTerm_mutual_ind with (PN:=PN);
        clear BTerm_NTerm_mutual_ind;trivial.
    + clear BTerm_NTerm_mutual_ind;
      apply HBInd in Hin. auto.
  - clear BTerm_NTerm_mutual_ind.
    destruct bt as [lv nt]. apply bcase.
    apply NTerm_BTerm_mutual_ind with (PB:=PB);
      clear NTerm_BTerm_mutual_ind; trivial.
Defined.

Lemma  NBTerm_mutual_ind {p}  : forall
    (PN : @NTerm p -> Type) (PB : BTerm -> Type)
    (vcase : forall n : NVar, PN (vterm n))
    (scase : forall f, (forall n, PN (f n)) -> PN (sterm f))
    (bcase: forall (lv : list NVar) (nt : NTerm),
             PN nt ->  PB (bterm lv nt))
    (ocase: forall (o : Opid) (lbt : list BTerm),
            (forall (bt : BTerm),
               (LIn bt lbt) -> PB bt)
            -> PN (oterm o lbt)),
    ((forall nt, PN nt) # (forall bt, PB bt)).
Proof.
  intros.
  split.
  - eapply NTerm_BTerm_mutual_ind; eauto.
  - eapply BTerm_NTerm_mutual_ind; eauto.
Defined.

Lemma NTerm_better_ind_direct {p} :
  forall P : @NTerm p -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall f, (forall n, P (f n)) -> P (sterm f))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt : NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt) -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
  introv Hv Hs Hind.
  fix 1.
  intro t.
  destruct t as [|f|o lbt];[apply Hv;fail|apply Hs;auto;fail|].
  apply Hind.
  introv Hin.
  induction lbt as [| bt lbt HBInd];[inverts Hin|].
  destruct bt as [blv bnt].
  dorn Hin.
  - symmetry in Hin. inverts Hin. apply NTerm_better_ind_direct.
  - clear NTerm_better_ind_direct.
    apply HBInd in Hin. auto.
Defined.

Tactic Notation "nterm_ind" ident(h) ident(c) :=
  induction h using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "sp_nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_simple_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "sterm"
  | Case_aux c "oterm"
  ].


(* end hide *)
