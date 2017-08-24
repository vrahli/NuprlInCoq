(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export bin_rels.
Require Export computation_seq.
Require Export rel_nterm.
Require Export computation_lib_extends.
Require Export computation_lib_extends2.
Require Export bar.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #<=># *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** We now define [close_comput],
    an endofunction in the type of binary relations on [NTerm].
    [approx] can be considered the greatest fixpoint of [close_comput].
    However, we define it predicatively using the [CoInductive] construct of
    Coq.
    Howe denotes [close_compute R] as $[R]$.

 *)

(*
Definition upto_alpha (R: NTerm -> NTerm -> [univ]) (a b : NTerm) :=
  {c : NTerm & { d : NTerm & alpha_eq a c # alpha_eq b d # R c d}}.

Lemma upto_alpha_weak :
  forall R a b, R a b -> upto_alpha R a b.
Proof.
  introv k.
  exists a b; dands; auto.
Qed.
*)

(** printing =v>  $\Downarrow$ #=v># *)



Definition eInExt {o} (lib : @library o) (F : @library o -> Type) :=
  {lib' : library
   & lib_extends lib' lib
   # F lib'}.

Definition all_in_bar_t {o} {lib} (bar : BarLib lib) (F : @library o -> Type) :=
  forall (lib' : library), bar_lib_bar bar lib' -> inExt lib' F.



Definition computes_to_value_ext {o} (lib : @library o) (a b : @NTerm o) :=
  inExt lib (fun lib => a =v>(lib) b).
Notation "a =e=v>( lib ) b" := (computes_to_value_ext lib a b) (at level 0).

Definition computes_to_value_eext {o} (lib : @library o) (a b : @NTerm o) :=
  eInExt lib (fun lib => a =v>(lib) b).
Notation "a =ee=v>( lib ) b" := (computes_to_value_eext lib a b) (at level 0).

Definition computes_to_value_alpha {o} (lib : @library o) (a b : @NTerm o) :=
  {c : NTerm & (a =v>(lib) c) # alpha_eq b c}.
Notation "a =a=v>( lib ) b" := (computes_to_value_alpha lib a b) (at level 0).

Definition computes_to_value_bar {o} {lib} (bar : @BarLib o lib) (a b : @NTerm o) :=
  all_in_bar_t bar (fun lib => a =a=v>(lib) b).
Notation "a =b=v>( lib ) b" := (computes_to_value_bar lib a b) (at level 0).



Definition computes_to_exception_ext {o} (lib : @library o) (a t1 t2 : @NTerm o) :=
  inExt lib (fun lib => t1 =e>(a,lib) t2).
Notation "t1 =e=e>( a , lib ) t2" := (computes_to_exception_ext lib a t1 t2) (at level 0).

Definition computes_to_exception_eext {o} (lib : @library o) (a t1 t2 : @NTerm o) :=
  eInExt lib (fun lib => t1 =e>(a,lib) t2).
Notation "t1 =ee=e>( a , lib ) t2" := (computes_to_exception_eext lib a t1 t2) (at level 0).

Definition computes_to_exception_alpha {o} (lib : @library o) (a t1 t2 : @NTerm o) :=
  {c : NTerm & {d : NTerm & (t1 =e>(c,lib) d) # alpha_eq a c # alpha_eq t2 d}}.
Notation "t1 =a=e>( a , lib ) t2" := (computes_to_exception_alpha lib a t1 t2) (at level 0).

Definition computes_to_exception_bar {o} {lib} (bar : @BarLib o lib) (a t1 t2 : @NTerm o) :=
  all_in_bar_t bar (fun lib => t1 =a=e>(a,lib) t2).
Notation "t1 =b=e>( a , lib ) t2" := (computes_to_exception_bar lib a t1 t2) (at level 0).



Definition computes_to_seq_ext {o} (lib : library) (t : NTerm) (f : @ntseq o) :=
  inExt lib (fun lib => t =s>(lib) f).
Notation "t =e=s>( lib ) f" := (computes_to_seq_ext lib t f) (at level 0).

Definition computes_to_seq_eext {o} (lib : library) (t : NTerm) (f : @ntseq o) :=
  eInExt lib (fun lib => t =s>(lib) f).
Notation "t =ee=s>( lib ) f" := (computes_to_seq_eext lib t f) (at level 0).

Definition computes_to_seq_alpha {o} (lib : library) (t : NTerm) (f : @ntseq o) :=
  {g : ntseq & (t =s>(lib) g) # forall n, alpha_eq (f n) (g n)}.
Notation "t =a=s>( lib ) f" := (computes_to_seq_alpha lib t f) (at level 0).

Definition computes_to_seq_bar {o} {lib} (bar : BarLib lib) (t : NTerm) (f : @ntseq o) :=
  all_in_bar_t bar (fun lib => t =a=s>(lib) f).
Notation "t =b=s>( lib ) f" := (computes_to_seq_bar lib t f) (at level 0).


(* We proved that bars are non-empty but in Prop, and since everything is
   unfortunately in Type here, we assume work on non-empty bars by definition *)
Record NeBarLib {o} (lib : @library o) :=
  MkNeBarLib
    {
      ne_bar_lib_bar :> BarLib lib;
      ne_bar_lib_lib : library;
      ne_bar_lib_ne  : bar_lib_bar ne_bar_lib_bar ne_bar_lib_lib;
    }.


Definition close_compute_val_ext {p} lib (R: NTrel) (tl tr : NTerm) : [univ] :=
  forall (c : CanonicalOp) (tl_subterms : list BTerm) (bar : NeBarLib lib),
    (* We assume that the bar is non-empty.  We proved that but in Prop... *)
    tl =b=v>(bar) (oterm (Can c) tl_subterms)
    -> {tr_subterms : list (@BTerm p)
        & (tr =b=v>(bar) (oterm (Can c) tr_subterms))
        # lblift (olift R) tl_subterms tr_subterms }.

(*
Definition close_compute_exc (R: NTerm -> NTerm -> [univ]) (tl tr : NTerm): [univ]:=
  forall (e : NTerm), (tl =e> e) -> {e' : NTerm & (tr =e> e') # upto_alpha R e e' }.
*)

Definition close_compute_exc_ext {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall a e (bar : NeBarLib lib),
    tl =b=e>(a,bar) e
    -> {a' : NTerm & {e' : NTerm & (tr =b=e>(a',bar) e') # R a a' # R e e' }}.

(*
Definition close_compute_seq {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall f,
    (tl =s>(lib) f)
    -> {f' : ntseq & (tr =s>(lib) f') # (forall n, R (f n) (f' n)) }.
*)

Definition close_compute_seq_ext {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall f (bar : NeBarLib lib),
    tl =b=s>(bar) f
    -> {f' : ntseq & (tr =b=s>(bar) f') # (forall n, R (f n) (f' n)) }.


(*Definition close_compute_mrk {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall m, (tl =m>(lib) m) -> (tr =m>(lib) m).*)

Definition close_compute_ext {p} lib (R: NTrel) (tl tr : @NTerm p) : [univ]:=
  isprogram tl
  # isprogram tr
  # close_compute_val_ext lib R tl tr
  # close_compute_exc_ext lib R tl tr
  # close_compute_seq_ext lib R tl tr
  # True (*close_compute_mrk lib R tl tr*).

(** % \noindent \\* %  At this point, one could directly define [approx] as: *)

CoInductive approx_ext_bad {o} (lib : @library o) (tl : NTerm) (tr : NTerm) : [univ] :=
| approx_ext_bad_dest :
    close_compute_ext lib (approx_ext_bad lib) tl tr
    -> approx_ext_bad lib tl tr.

(** %\noindent % However, this approach would require using the [cofix] tactic of Coq
  for proving the the properties of [approx].
  Unfortunately, [cofix] does a very
  conservative productivity checking and often rejects our
  legitimate proofs at [Qed] time.

  So, we use parametrized coinduction %\cite{Hur+Neis+Dreyer+Vafeiadis:2013}%
  to define it in a slightly indirect way. With this technique, we only
  need to use [cofix] once.%\footnote{If we allowed ourselves the
    luxury of impredicativity([Prop]), we would never need [cofix].}%
*)

Notation "p =2> q" :=
  (forall x0 x1 (PR: p x0 x1 : Type), q x0 x1 : Type)
  (at level 50, no associativity).

Notation "p \2/ q" :=
  (fun x0 x1 => p x0 x1 [+] q x0 x1)
  (at level 50, no associativity).

Definition bot2 {p} (x y : @NTerm p) := False.
Hint Unfold bot2.

CoInductive approx_ext_aux {p}
            (lib : library)
            (R : bin_rel NTerm)
            (tl tr : @NTerm p) : [univ] :=
| approx_aux_ext_dest :
   close_compute_ext lib (approx_ext_aux lib R \2/ R) tl tr
   -> approx_ext_aux lib R tl tr.

Definition approx_ext {p} lib := @approx_ext_aux p lib bot2.


(** %\noindent % The first thing we do is to
  prove  "co-induction principle" for approx using [cofix]
  and then never ever use [cofix] again.
  An interested user can walk through the proof
  of [approx_refl] below to see this co-induction
  principle in action.

 *)

Theorem approx_ext_acc {p} :
  forall (lib : library)
         (l r0 : bin_rel (@NTerm p))
         (OBG: forall (r: bin_rel NTerm)
                      (INC: r0 =2> r) (CIH: l =2> r),
                 l =2> approx_ext_aux lib r),
    l =2> approx_ext_aux lib r0.
Proof.
  intros. assert (SIM: approx_ext_aux lib (r0 \2/ l) x0 x1) by eauto.
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna c Hcl. repnd.
  unfold close_compute_ext.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp; auto.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    dorn Hap; spc.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd; auto.
    exists a' e'; dands; auto; repdors; auto.

  - introv comp; allsimpl.
    apply Hcl4 in comp; exrepnd; auto;[].
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0.
    repndors; auto.
Qed.

(* begin hide *)


(*
Ltac cleanToProp :=
(repeat match goal with
| [ H : (toProp _) |- _ ] => destruct H as [H]
end); try (
match goal with 
| [ |- toProp _ ] => constructor
end
).
*)

(* the order is important*)

(* not needed anymore
Lemma close_comput_mon: monotone2 close_comput. 
Proof.
  unfold monotone2, rel2.
  intros t1 t2 ra rb Hcl Hrab.
  allunfold close_comput. repnd.
  dands; auto;[]. intros ? ? Hcomp.
  apply Hcl in Hcomp. parallel tr_subterms Hrelbt.
  repnd. split;auto. cleanToProp.
  eapply le_lblift2; eauto with slow.

 (**
    apply le_blift_olift.
     exact Hrab.
    (* info eauto : *)
    exact Hrelbt.
   *)
Qed.
Hint Resolve close_comput_mon : paco.
*)

Lemma computes_to_value_ext_eq {o} :
  forall lib (t v1 v2 : @NTerm o),
    t =e=v>(lib) v1
    -> t =e=v>(lib) v2
    -> v1 = v2.
Proof.
  introv comp1 comp2.
  eapply computes_to_value_eq;[apply comp1|apply comp2]; apply lib_extends_refl.
Qed.

Lemma computes_to_exception_ext_eq {o} :
  forall lib (a b t e1 e2 : @NTerm o),
    t =e=e>(a,lib) e1
    -> t =e=e>(b,lib) e2
    -> e1 = e2 # a = b.
Proof.
  introv comp1 comp2.
  eapply computes_to_exception_eq;[apply comp1|apply comp2]; apply lib_extends_refl.
Qed.

Definition reduces_to_ext {o} (lib : library) (t u : @NTerm o) :=
  inExt lib (fun lib => reduces_to lib t u).

Lemma reduces_to_ext_eq_val_like {o} :
  forall lib (t v1 v2 : @NTerm o),
    reduces_to_ext lib t v1
    -> reduces_to_ext lib t v2
    -> isvalue_like v1
    -> isvalue_like v2
    -> v1 = v2.
Proof.
  introv r1 r2 isv1 isv2.
  eapply reduces_to_eq_val_like;
    [apply r1|apply r2|exact isv1|exact isv2];
    apply lib_extends_refl.
Qed.

(** inspited by dom2.pdf, Nuprl's type-continuous
  lub in dom2.pdf == intersect in Nuprl == and here *)
Definition continuous {p} (F : bin_rel NTerm -> bin_rel NTerm) :=
   forall (Rn : nat -> bin_rel (@NTerm p)) (t1 t2 : @NTerm p),
  (forall n : nat, (F (Rn n)) t1 t2)
   <=> (F (fun x y => forall n : nat, (Rn  n) x y)) t1 t2.

Lemma close_comp_cont {p} : forall lib, @continuous p (close_compute_ext lib).
Abort.

Lemma computes_to_seq_implies_hasvalue_like {o} :
  forall lib (t : @NTerm o) f,
    (t =s>(lib) f)
    -> hasvalue_like lib t.
Proof.
  introv comp.
  unfold hasvalue_like.
  eexists; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_seq_implies_hasvalue_like : slow.

(* end hide *)

(** %\noindent \\*%The following lemma says that for programs
    [a] and [b], if we have to prove [approx a b], the we
    can assume that [a] converges.
    Although, it is trivial to prove it by assuming the law of excluded
    middle, a constructive proof is almost as easy and follows directly from the
    definition of [approx].

 *)

Lemma computes_to_value_ext_implies_computes_to_value {o} :
  forall lib (t u : @NTerm o),
    t =e=v>(lib) u
    -> t =v>(lib) u.
Proof.
  introv h; apply h; eauto 2 with slow.
Qed.
Hint Resolve computes_to_value_ext_implies_computes_to_value : slow.

Lemma computes_to_exception_ext_implies_computes_to_exception {o} :
  forall lib (a t u : @NTerm o),
    t =e=e>(a,lib) u
    -> t =e>(a,lib) u.
Proof.
  introv h; apply h; eauto 2 with slow.
Qed.
Hint Resolve computes_to_exception_ext_implies_computes_to_exception : slow.

Definition reduces_to_alpha {o} lib (a b : @NTerm o) :=
  {c : NTerm & reduces_to lib a c # alpha_eq b c}.

Definition reduces_to_bar {o} {lib} (bar : @BarLib o lib) (a b : @NTerm o) :=
  all_in_bar_t bar (fun lib => reduces_to_alpha lib a b).

Definition hasvalue_like_bar {o} lib (a : @NTerm o) :=
  {bar : BarLib lib
   & {v : NTerm
   & reduces_to_bar bar a v
   # isvalue_like v}}.

Hint Resolve lib_extends_preserves_reduces_to : slow.

Lemma lib_extends_preserves_hasvalue_like {o} :
  forall lib' lib (t : @NTerm o),
    wf_term t
    -> lib_extends lib' lib
    -> hasvalue_like lib t
    -> hasvalue_like lib' t.
Proof.
  introv wf ext hv.
  unfold hasvalue_like in *; exrepnd.
  exists v; dands; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_hasvalue_like : slow.

Lemma reduces_to_implies_reduces_to_alpha {o} :
  forall lib (a b : @NTerm o),
    reduces_to lib a b -> reduces_to_alpha lib a b.
Proof.
  introv r; exists b; dands; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_implies_reduces_to_alpha : slow.

Lemma reduces_to_implies_reduces_to_bar {o} :
  forall lib (bar : BarLib lib) (a b : @NTerm o),
    wf_term a
    -> reduces_to lib a b
    -> reduces_to_bar bar a b.
Proof.
  introv wf r ext ext'.
  eauto 5 with slow.
Qed.
Hint Resolve reduces_to_implies_reduces_to_bar : slow.

Lemma hasvalue_like_implies_hasvalue_like_bar {o} :
  forall lib (a : @NTerm o),
    wf_term a
    -> hasvalue_like lib a
    -> hasvalue_like_bar lib a.
Proof.
  introv wf hv.
  unfold hasvalue_like, hasvalue_like_bar in *; exrepnd.

  exists (trivial_bar lib) v; dands; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_like_implies_hasvalue_like_bar : slow.

Lemma computes_to_value_alpha_implies_reduces_to_alpha {o} :
  forall lib (a b : @NTerm o),
    computes_to_value_alpha lib a b
    -> reduces_to_alpha lib a b.
Proof.
  introv comp.
  unfold computes_to_value_alpha in comp; exrepnd.
  exists c; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_alpha_implies_reduces_to_alpha : slow.

Lemma computes_to_value_bar_implies_reduces_to_bar {o} :
  forall lib (bar : BarLib lib) (a b : @NTerm o),
    computes_to_value_bar bar a b
    -> reduces_to_bar bar a b.
Proof.
  introv comp ext ext'.
  pose proof (comp lib' ext lib'0 ext') as q; simpl in q.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_bar_implies_reduces_to_bar : slow.

Lemma or_implies_isvalue_like {o} :
  forall (a : @NTerm o),
    iscan a \/ isexc a
    -> isvalue_like a.
Proof.
  introv h.
  destruct a as [v|f|op bs]; simpl in *; tcsp;
    try (complete (assert False; tcsp));
    try (complete (unfold isvalue_like; simpl; tcsp)).

  dopid op as [can|ncan|exc|abs] Case;
    try (complete (assert False; tcsp));
    try (complete (unfold isvalue_like; simpl; tcsp)).
Qed.

Lemma isvalue_like_implies_or {o} :
  forall (a : @NTerm o),
    isvalue_like a
    -> iscan a \/ isexc a.
Proof.
  introv h.
  unfold isvalue_like in h; repndors; tcsp.
Qed.

Lemma computes_to_value_implies_isvalue_like {o} :
  forall lib (a b : @NTerm o),
    computes_to_value lib a b
    -> isvalue_like b.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_implies_isvalue_like : slow.

Lemma alpha_eq_preserves_isvalue_like_left {o} :
  forall (b c : @NTerm o),
    isvalue_like c
    -> alpha_eq b c
    -> isvalue_like b.
Proof.
  introv isv aeq.
  unfold isvalue_like in *; repndors;[left|right].

  - apply iscan_implies in isv; repndors; exrepnd; subst;
      inversion aeq; subst; simpl; auto.

  - apply isexc_implies2 in isv; exrepnd; subst;
      inversion aeq; subst; simpl; auto.
Qed.
Hint Resolve alpha_eq_preserves_isvalue_like_left : slow.

Lemma computes_to_value_alpha_implies_isvalue_like {o} :
  forall lib (a b : @NTerm o),
    computes_to_value_alpha lib a b
    -> isvalue_like b.
Proof.
  introv comp.
  unfold computes_to_value_alpha in comp; exrepnd.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_alpha_implies_isvalue_like : slow.

Lemma computes_to_value_bar_implies_isvalue_like {o} :
  forall lib (bar : BarLib lib) (a b : @NTerm o),
    computes_to_value_bar bar a b
    -> isvalue_like b.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne.
  apply or_implies_isvalue_like.
  exrepnd.
  pose proof (comp lib' ne0 lib') as q.
  autodimp q hyp; eauto 3 with slow; simpl in q.
  apply isvalue_like_implies_or; eauto 4 with slow.
Qed.
Hint Resolve computes_to_value_bar_implies_isvalue_like : slow.

Lemma computes_to_value_bar_implies_hasvalue_like_bar {o} :
  forall lib (bar : BarLib lib) (a b : @NTerm o),
    wf_term a
    -> computes_to_value_bar bar a b
    -> hasvalue_like_bar lib a.
Proof.
  introv wf hv.
  unfold hasvalue_like_bar in *; exrepnd.
  exists bar b; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_bar_implies_hasvalue_like_bar : slow.

Lemma computes_to_exception_bar_implies_reduces_to_bar {o} :
  forall {lib} (bar : BarLib lib) (a n b : @NTerm o),
    a =b=e>(n, bar) b
    -> reduces_to_bar bar a (mk_exception n b).
Proof.
  introv comp ext ext'.
  pose proof (comp _ ext _ ext') as q; simpl in q; clear comp.
  unfold computes_to_exception_alpha in q; exrepnd.
  exists (mk_exception c d); dands; auto.
  apply implies_alphaeq_exception; auto.
Qed.
Hint Resolve computes_to_exception_bar_implies_reduces_to_bar : slow.

Lemma computes_to_exception_bar_implies_hasvalue_like_bar {o} :
  forall lib (bar : BarLib lib) (n a b : @NTerm o),
    wf_term a
    -> computes_to_exception_bar bar n a b
    -> hasvalue_like_bar lib a.
Proof.
  introv wf hv.
  unfold hasvalue_like_bar in *; exrepnd.
  exists bar (mk_exception n b); dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_exception_bar_implies_hasvalue_like_bar : slow.

Lemma computes_to_seq_bar_implies_reduces_to_bar {o} :
  forall {lib} (bar : BarLib lib) (a : @NTerm o) f,
    a =b=s>(bar) f
    -> reduces_to_bar bar a (sterm f).
Proof.
  introv comp ext ext'.
  pose proof (comp _ ext _ ext') as q; clear comp; simpl in q.
  unfold computes_to_seq_alpha in q; exrepnd.
  exists (sterm g); dands; auto.
Qed.
Hint Resolve computes_to_seq_bar_implies_reduces_to_bar : slow.

Lemma computes_to_seq_bar_implies_hasvalue_like_bar {o} :
  forall lib (bar : BarLib lib) (a : @NTerm o) f,
    wf_term a
    -> computes_to_seq_bar bar a f
    -> hasvalue_like_bar lib a.
Proof.
  introv wf hv.
  unfold hasvalue_like_bar in *; exrepnd.
  exists bar (sterm f); dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_seq_bar_implies_hasvalue_like_bar : slow.

Lemma approx_ext_assume_hasvalue {p} :
  forall lib a b,
    isprogram a
    -> @isprogram p b
    -> (hasvalue_like_bar lib a -> approx_ext lib a b)
    -> approx_ext lib a b.
Proof.
  introv Hpa Hpb Hha.
  constructor.
  unfold close_compute_ext.
  dands; auto; introv Hcomp.

  - autodimp Hha hyp;[eauto 4 with slow|];[].
    invertsn Hha.
    unfold close_compute_ext in Hha; repnd; eauto.

  - autodimp Hha hyp;[eauto 4 with slow|];[].
    invertsn Hha.
    unfold close_compute_ext in Hha; repnd; eauto.

(*
  - autodimp Hha hyp.
    { unfold computes_to_marker in Hcomp; repnd.
      eexists; dands; eauto with slow. }
    invertsn Hha.
    unfold close_compute_ext in Hha; repnd; eauto.*)

  - autodimp Hha hyp;[eauto 4 with slow|];[].
    invertsn Hha.
    unfold close_compute_ext in Hha; repnd; eauto.
Qed.

Lemma not_hasvalue_like_bottom {o} :
  forall (lib : @library o), !hasvalue_like lib mk_bottom.
Proof.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.
  apply not_bot_reduces_to_is_value_like in hv1; tcsp.
Qed.

Lemma reduces_to_alpha_isvalue_like_implies_hasvalue_like {o} :
  forall lib (a b : @NTerm o),
    isvalue_like b
    -> reduces_to_alpha lib a b
    -> hasvalue_like lib a.
Proof.
  introv isv r.
  unfold reduces_to_alpha in r; exrepnd.
  exists c; dands; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_alpha_isvalue_like_implies_hasvalue_like : slow.

Lemma not_hasvalue_like_bar_bottom {o} :
  forall (lib : @library o), !hasvalue_like_bar lib mk_bottom.
Proof.
  introv hv.
  unfold hasvalue_like_bar in hv; exrepnd.

  pose proof (bar_non_empty bar) as q; exrepnd.
  apply hv0 in q0.
  pose proof (q0 lib') as w; autodimp w hyp; eauto 3 with slow; simpl in w.

  pose proof (not_hasvalue_like_bottom lib') as q; destruct q.
  eauto 3 with slow.
Qed.

(** %\noindent \\*% The following is an easy corollary of the above.

 *)
Corollary bottom_approx_ext_any {p} :
  forall lib t, @isprogram p t -> approx_ext lib mk_bottom t.
Proof.
  introv Hpr.
  apply approx_ext_assume_hasvalue; auto.
  introv Hv; apply not_hasvalue_like_bar_bottom in Hv; tcsp.
Qed.

(* begin hide *)

Lemma axiom_doesnt_compute_to_seq {o} :
  forall lib (f : @ntseq o), !(mk_axiom =s>(lib) f).
Proof.
  introv comp.
  unfold computes_to_seq in comp.
  apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

Lemma computes_to_value_ext_isvalue_eq {o} :
  forall (lib : library) (t v : @NTerm o),
    (t =e=v>( lib) v) -> isvalue t -> t = v.
Proof.
  introv comp isv.
  eapply computes_to_value_isvalue_eq;[|auto].
  apply comp.
  apply lib_extends_refl.
Qed.
Hint Resolve computes_to_value_ext_isvalue_eq : slow.

Lemma computes_to_value_alpha_isvalue_alpha_eq {o} :
  forall lib (t v : @NTerm o),
    (t =a=v>(lib) v) -> isvalue t -> alpha_eq t v.
Proof.
  introv comp isv.
  unfold computes_to_value_alpha in comp; exrepnd.
  apply computes_to_value_isvalue_eq in comp1; auto.
  subst.
  apply alpha_eq_sym; auto.
Qed.
Hint Resolve computes_to_value_alpha_isvalue_alpha_eq : slow.

Lemma inExt_refl {o} :
  forall (lib : @library o) F,
    inExt lib F -> F lib.
Proof.
  introv i; apply i; eauto 2 with slow.
Qed.

Lemma computes_to_value_bar_isvalue_alpha_eq {o} :
  forall {lib} (bar : NeBarLib lib) (t v : @NTerm o),
    (t =b=v>(bar) v) -> isvalue t -> alpha_eq t v.
Proof.
  introv comp isv.

  pose proof (comp (ne_bar_lib_lib _ bar) (ne_bar_lib_ne _ bar)) as q.
  apply inExt_refl in q.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_bar_isvalue_alpha_eq : slow.

(*Lemma lib_extends_preserves_computes_to_value {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : computes_to_value lib1 a b),
    {b' : NTerm & computes_to_value lib2 a b' # alpha_eq b b'}.
Proof.
  introv ext wf r.
  unfold computes_to_value in *; repnd.
  dup r0 as comp.
  eapply reduces_to_preserves_lib_extends in r0;[|eauto|]; eauto 2 with slow.
  exrepnd.
  exists b'; dands; eauto 2 with slow.
Qed.*)

Lemma lib_extends_preserves_hasvalue {o} :
  forall lib lib' (t : @NTerm o),
    wf_term t
    -> lib_extends lib' lib
    -> hasvalue lib t
    -> hasvalue lib' t.
Proof.
  introv wf ext hv.
  unfold hasvalue in *; exrepnd.
  eapply lib_extends_preserves_computes_to_value in hv0;[|eauto|]; auto.
  exists t'; auto.
Qed.
Hint Resolve lib_extends_preserves_hasvalue : slow.

Lemma computes_to_value_ext_isvalue_refl {o} :
  forall lib (t : @NTerm o),
    isvalue t -> t =e=v>(lib) t.
Proof.
  introv isv ext.
  apply computes_to_value_isvalue_refl; auto.
Qed.
Hint Resolve computes_to_value_ext_isvalue_refl : slow.

Lemma computes_to_value_alpha_isvalue_refl {o} :
  forall lib (t : @NTerm o),
    isvalue t -> t =a=v>(lib) t.
Proof.
  introv isv.
  exists t; dands; auto.
  apply computes_to_value_isvalue_refl; auto.
Qed.
Hint Resolve computes_to_value_alpha_isvalue_refl : slow.

Lemma computes_to_value_bar_isvalue_refl {o} :
  forall {lib} (bar : BarLib lib) (t : @NTerm o),
    isvalue t -> t =b=v>(bar) t.
Proof.
  introv isv ext ext'.
  apply computes_to_value_alpha_isvalue_refl; auto.
Qed.
Hint Resolve computes_to_value_bar_isvalue_refl : slow.

Lemma computes_to_value_bar_implies_computes_to_value_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (t u : @NTerm o),
    t =b=v>(bar) u
    -> {lib : library & t =a=v>(lib) u}.
Proof.
  introv h.
  unfold computes_to_value_bar in h.
  pose proof (h (ne_bar_lib_lib _ bar) (ne_bar_lib_ne _ bar)) as q.
  apply inExt_refl in q.
  eexists; eauto.
Qed.
Hint Resolve computes_to_value_bar_implies_computes_to_value_alpha : slow.

Lemma computes_to_exception_bar_implies_computes_to_exception_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (a t u : @NTerm o),
    t =b=e>(a,bar) u
    -> {lib : library & t =a=e>(a,lib) u}.
Proof.
  introv h.
  unfold computes_to_value_bar in h.
  pose proof (h (ne_bar_lib_lib _ bar) (ne_bar_lib_ne _ bar)) as q.
  apply inExt_refl in q.
  eexists; eauto.
Qed.
Hint Resolve computes_to_exception_bar_implies_computes_to_exception_alpha : slow.

Lemma computes_to_seq_bar_implies_computes_to_seq_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (t : @NTerm o) f,
    t =b=s>(bar) f
    -> {lib : library & t =a=s>(lib) f}.
Proof.
  introv h.
  unfold computes_to_value_bar in h.
  pose proof (h (ne_bar_lib_lib _ bar) (ne_bar_lib_ne _ bar)) as q.
  apply inExt_refl in q.
  eexists; eauto.
Qed.
Hint Resolve computes_to_seq_bar_implies_computes_to_seq_alpha : slow.


Definition trivial_ne_bar {o} (lib : @library o) : NeBarLib lib.
Proof.
  eexists.
  assert (bar_lib_bar (trivial_bar lib) lib) as w.
  { simpl; eauto 2 with slow. }
  exact w.
Defined.

Definition hasvalue_all_bars {o} (lib : @library o) a :=
  forall (bar : NeBarLib lib), all_in_bar_t bar (fun lib => hasvalue lib a).

Lemma hasvalue_all_bars_implies_hasvalue {o} :
  forall lib (a : @NTerm o),
    hasvalue_all_bars lib a
    -> hasvalue lib a.
Proof.
  introv hv.
  pose proof (hv (trivial_ne_bar lib) lib) as h; autodimp h hyp; simpl; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_all_bars_implies_hasvalue : slow.

Lemma axiom_doesnt_raise_an_exception_alpha {p} :
  forall lib a (e : @NTerm p),
    computes_to_exception_alpha lib a mk_axiom e -> False.
Proof.
  introv c.
  unfold computes_to_exception_alpha in c; exrepnd.
  apply can_doesnt_raise_an_exception in c1; sp.
Qed.

Lemma axiom_doesnt_compute_to_seq_alpha {o} :
  forall lib (f : @ntseq o), !(mk_axiom =a=s>(lib) f).
Proof.
  introv comp.
  unfold computes_to_seq_alpha in comp; exrepnd.
  apply axiom_doesnt_compute_to_seq in comp1; auto.
Qed.

Lemma computes_to_value_alpha_axiom_implies {o} :
  forall lib (t : @NTerm o),
    t =a=v>(lib) mk_axiom
    -> t =v>(lib) mk_axiom.
Proof.
  introv comp.
  unfold computes_to_value_alpha in comp; exrepnd.
  inversion comp0; simpl in *; cpx.
Qed.
Hint Resolve computes_to_value_alpha_axiom_implies : slow.

Lemma hasvalue_as_approx_ext {o} :
  forall lib (a : @NTerm o),
    isprogram a
    -> (hasvalue_all_bars lib a
        <=>
        approx_ext lib mk_axiom (mk_cbv a nvarx mk_axiom)).
Proof.
  introv isp; split; intro k.

  - constructor.
    unfold close_compute_ext; dands; tcsp.

    + apply isprogram_cbv; sp.
      rw @nt_wf_eq; sp.

    + introv comp.
      exists ([] : list (@BTerm o)).

      apply computes_to_value_bar_isvalue_alpha_eq in comp; auto.
      inversion comp; subst; simpl in *; clear comp; cpx.
      dands; auto; fold_terms; tcsp.

      {
        introv ext ext'.
        exists (@mk_axiom o).
        unfold computes_to_value; sp.
        apply cbv_reduce0; eauto 4 with slow.
        eapply (lib_extends_preserves_hasvalue lib); eauto 3 with slow.
      }

      {
        constructor; simpl; sp.
      }

    + introv comp.
      apply computes_to_exception_bar_implies_computes_to_exception_alpha in comp; exrepnd.
      apply axiom_doesnt_raise_an_exception_alpha in comp0; sp.

    + introv comp.
      apply computes_to_seq_bar_implies_computes_to_seq_alpha in comp; exrepnd.
      apply axiom_doesnt_compute_to_seq_alpha in comp0; sp.

(*
    + introv cm.
      apply axiom_doesnt_mark in cm; sp.
*)

  - inversion k as [c].
    unfold close_compute_ext in c; repnd.

    introv ext ext'.
    pose proof (c2 NAxiom [] bar) as h.
    allfold (@mk_axiom o).
    repeat (autodimp h hyp); eauto 2 with slow.

    exrepnd.
    inversion h0 as [? imp]; allsimpl; cpx.
    allfold (@mk_axiom o).
    assert (hasvalue lib'0 (mk_cbv a nvarx mk_axiom)) as hv.

    + exists (@mk_axiom o); eauto 2 with slow.

      pose proof (h1 lib' ext lib'0 ext') as q; simpl in q; eauto 2 with slow.

    + apply if_hasvalue_cbv0 in hv; sp.

      rw @isprog_eq; sp.
Qed.


(*
(** Same as approx_ext but on well-formed terms *)
Definition approxw (a b : WTerm) :=
  approx_ext (get_wterm a) (get_wterm b).
*)

(* end hide *)

(**

  Because in the PER semantics, Nuprl's types are defined as partial
  equivalence relations on closed terms, we define a closed version of
  [approx] as follows:

 *)

Definition approxc_ext {p} lib (a b : @CTerm p) :=
  approx_ext lib (get_cterm a) (get_cterm b).

(* begin hide *)

Definition hasvalue_likec {p} lib (t : @CTerm p) :=
  hasvalue_like lib (get_cterm t).

Definition hasvalue_likec_bar {p} lib (t : @CTerm p) :=
  hasvalue_like_bar lib (get_cterm t).

Definition has_value_likec {p} lib (t : @CTerm p) :=
  has_value_like lib (get_cterm t).

Definition hasvaluec_all_bars {o} lib (a : @CTerm o) :=
  hasvalue_all_bars lib (get_cterm a).

Lemma approxc_ext_assume_hasvalue {p} :
  forall (lib : @library p) a b,
    (hasvalue_likec_bar lib a -> approxc_ext lib a b)
    -> approxc_ext lib a b.
Proof.
  destruct a; destruct b; unfold hasvalue_likec_bar, approxc_ext; allsimpl; sp.
  apply approx_ext_assume_hasvalue; sp; allrw @isprogram_eq; sp.
Qed.

Lemma hasvaluec_as_approxc_ext {p} :
  forall lib a,
    hasvaluec_all_bars lib a
    <=>
    approxc_ext lib mkc_axiom (mkc_cbv a nvarx (@mkcv_axiom p nvarx)).
Proof.
  destruct a; unfold hasvaluec, approxc_ext; simpl.
  apply hasvalue_as_approx_ext.
  allrw @isprogram_eq; sp.
Qed.

Lemma approx_ext_relates_only_progs {p} :
  forall lib (a b : @NTerm p), approx_ext lib a b -> isprogram a # isprogram b.
Proof.
  intros. invertsn X. repnud X; sp.
Qed.

Lemma preserve_program_exc2 {p} :
  forall lib a (t1 t2 : @NTerm p),
    computes_to_exception lib a t1 t2
    -> isprogram t1
    -> isprogram a # isprogram t2.
Proof.
  introv Hcv Hpt1.
  inverts Hcv as Hcv.
  inverts Hcv as Hcv.
  apply computek_preserves_program in Hcv; auto.
  rw @isprogram_exception_iff in Hcv; sp.
Qed.

Lemma isprogram_mk_ntseq {o} :
  forall (f : @ntseq o),
    isprogram (mk_ntseq f)
    <=> (forall n, isprogram (f n) # noutokens (f n)).
Proof.
  introv; split; intro h.
  - introv; inversion h as [c w]; clear c.
    rw @nt_wf_sterm_iff in w.
    pose proof (w n) as q; repnd.
    dands; auto.
    constructor; auto.
  - constructor; unfold closed; simpl; auto.
    constructor; introv.
    pose proof (h n) as q; repnd.
    inversion q0 as [c w]; dands; auto.
Qed.

(* end hide *)

(** %\noindent% We formalize a co-inductive proof
  of reflexivity of [approx] by using the [approx_acc] lemma above.
 *)

Lemma computes_to_value_ext_preserves_isprogram {o} :
  forall lib (t1 t2 : @NTerm o),
    t1 =e=v>(lib) t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv comp isp.
  eapply preserve_program; try (apply comp);[|auto]; apply lib_extends_refl.
Qed.
Hint Resolve computes_to_value_ext_preserves_isprogram : slow.

Lemma computes_to_exception_ext_preserves_isprogram {o} :
  forall lib (a t1 t2 : @NTerm o),
    t1 =e=e>(a, lib) t2
    -> isprogram t1
    -> isprogram a # isprogram t2.
Proof.
  introv comp isp.
  eapply preserve_program_exc2;[|eauto]; apply comp; apply lib_extends_refl.
Qed.
Hint Resolve computes_to_exception_ext_preserves_isprogram : slow.

Lemma computes_to_seq_ext_preserves_isprogram {o} :
  forall lib (t : @NTerm o) f,
    t =e=s>(lib) f
    -> isprogram t
    -> isprogram (mk_ntseq f).
Proof.
  introv comp isp.
  eapply reduces_to_preserves_program;[|eauto]; apply comp; apply lib_extends_refl.
Qed.
Hint Resolve computes_to_seq_ext_preserves_isprogram : slow.

Lemma computes_to_value_alpha_preserves_isprogram {o} :
  forall lib (t1 t2 : @NTerm o),
    t1 =a=v>(lib) t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv comp isp.
  unfold computes_to_value_alpha in comp; exrepnd.
  apply preserve_program in comp1; auto.
  apply alphaeq_preserves_program in comp0.
  apply comp0; auto.
Qed.
Hint Resolve computes_to_value_alpha_preserves_isprogram : slow.

Lemma computes_to_value_bar_preserves_isprogram {o} :
  forall {lib} (bar : NeBarLib lib) (t1 t2 : @NTerm o),
    t1 =b=v>(bar) t2
    -> isprogram t1
    -> isprogram t2.
Proof.
  introv comp isp.
  apply computes_to_value_bar_implies_computes_to_value_alpha in comp; exrepnd.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_bar_preserves_isprogram : slow.

Lemma computes_to_exception_alpha_preserves_isprogram {o} :
  forall lib (a t1 t2 : @NTerm o),
    t1 =a=e>(a,lib) t2
    -> isprogram t1
    -> isprogram a # isprogram t2.
Proof.
  introv comp isp.
  unfold computes_to_exception_alpha in comp; exrepnd.
  apply preserve_program_exc2 in comp0; auto; repnd.
  apply alphaeq_preserves_program in comp2.
  apply alphaeq_preserves_program in comp1.
  rw comp2; rw comp1; auto.
Qed.
Hint Resolve computes_to_exception_alpha_preserves_isprogram : slow.

Lemma computes_to_exception_bar_preserves_isprogram {o} :
  forall {lib} (bar : NeBarLib lib) (a t1 t2 : @NTerm o),
    t1 =b=e>(a,bar) t2
    -> isprogram t1
    -> isprogram a # isprogram t2.
Proof.
  introv comp isp.
  apply computes_to_exception_bar_implies_computes_to_exception_alpha in comp; exrepnd.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_exception_bar_preserves_isprogram : slow.

Lemma alphaeq_preserves_noutokens {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2 -> (noutokens t1 <=> noutokens t2).
Proof.
  introv aeq.
  apply alphaeq_preserves_utokens in aeq.
  unfold noutokens; allrw; tcsp.
Qed.

Lemma computes_to_seq_alpha_preserves_isprogram {o} :
  forall lib (t : @NTerm o) f,
    t =a=s>(lib) f
    -> isprogram t
    -> isprogram (mk_ntseq f).
Proof.
  introv comp isp.
  unfold computes_to_seq_alpha in comp; exrepnd.
  apply reduces_to_preserves_program in comp1; auto.
  allrw @isprogram_mk_ntseq.
  introv.
  pose proof (comp0 n) as z.
  pose proof (comp1 n) as w; repnd.
  applydup @alphaeq_preserves_program in z; rw z0.
  applydup @alphaeq_preserves_noutokens in z; rw z1; tcsp.
Qed.
Hint Resolve computes_to_seq_alpha_preserves_isprogram : slow.

Lemma computes_to_seq_bar_preserves_isprogram {o} :
  forall {lib} (bar : NeBarLib lib) (t : @NTerm o) f,
    t =b=s>(bar) f
    -> isprogram t
    -> isprogram (mk_ntseq f).
Proof.
  introv comp isp.
  apply computes_to_seq_bar_implies_computes_to_seq_alpha in comp; exrepnd.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_seq_bar_preserves_isprogram : slow.

Lemma approx_ext_refl {p} :
  forall lib (t : @NTerm p), isprogram t -> approx_ext lib t t.
Proof.
  unfold approx_ext.
  intro lib.
  pose proof (@approx_ext_acc p lib (fun x y => isprogram x # y=x)) as HH.
  allsimpl.
  assert (forall x0 x1 : @NTerm p, isprogram x0 # x1 = x0 -> approx_ext_aux lib bot2 x0 x1);[| spcf;fail].
  eapply HH.
  intros.
  rename x0 into t.
  exrepnd. subst.
  constructor.
  unfold close_compute_ext; dands; tcsp; introv comp; auto.

  - exists tl_subterms; split; auto.
    unfold lblift.
    split; auto.
    intros ? Hlt.
    unfold blift.

    apply computes_to_value_bar_preserves_isprogram in comp; auto.
    pose proof (selectbt_in2 _ tl_subterms Hlt) as Hbt.
    exrepnd.
    destruct bt as [lv nt].
    rw Hbt0.
    exists lv nt nt.
    split; eauto with slow.
    apply isprogram_ot_iff in comp. repnd.
    apply comp in Hbt1. repnud Hbt1.
    inverts Hbt1.
    unfold olift. spc;  eauto.

  - applydup @computes_to_exception_bar_preserves_isprogram in comp; auto; repnd.
    exists a e; dands; auto.

  - eexists; dands; eauto.
    introv.
    right.
    applydup @computes_to_seq_bar_preserves_isprogram in comp as wf; auto.
    apply CIH; dands; auto.
    rw @isprogram_mk_ntseq in wf.
    pose proof (wf n) as q; tcsp.
Qed.
Hint Resolve approx_ext_refl : slow.

Definition approx_ext_open {p} lib := olift (@approx_ext p lib).
Definition approx_ext_open_bterm {p} lib := blift (@approx_ext_open p lib).
Definition approx_ext_bts {p} lib := lblift (@approx_ext_open p lib).

Lemma approx_ext_open_refl {p} :
  forall lib (nt: @NTerm p), (nt_wf nt) -> approx_ext_open lib nt nt.
Proof.
  induction nt as [v|f| op bts Hind] using NTerm_better_ind; intros Hwf;
  constructor; try split; auto; intros  ? Hcl Hisp ?; apply approx_ext_refl; auto.
Qed.

Lemma vbot_doesnt_compute_to_seq {o} :
  forall lib v (f : @ntseq o), !(mk_vbot v =s>(lib) f).
Proof.
  introv comp.
  unfold computes_to_seq in comp.
  apply reduces_to_vbot_if_isvalue_like in comp; eauto 3 with slow.
Qed.

Lemma vbot_diverges_ext {o} :
  forall lib (v : NVar) (t : @NTerm o),
    !((mk_vbot v) =e=v>(lib) t).
Proof.
  introv h.
  pose proof (h lib) as q; autodimp q hyp; eauto 2 with slow; simpl in q.
  apply vbot_diverges in q; auto.
Qed.

Lemma vbot_doesnt_raise_an_exception_ext {o} :
  forall lib (a : @NTerm o) (v : NVar) (e : NTerm),
    !((mk_vbot v) =e=e>(a, lib) e).
Proof.
  introv h.
  pose proof (h lib) as q; autodimp q hyp; eauto 2 with slow; simpl in q.
  apply vbot_doesnt_raise_an_exception in q; auto.
Qed.

Lemma vbot_doesnt_compute_to_seq_ext {o} :
  forall lib (v : NVar) (f : @ntseq o),
    !((mk_vbot v) =e=s>(lib) f).
Proof.
  introv h.
  pose proof (h lib) as q; autodimp q hyp; eauto 2 with slow; simpl in q.
  apply vbot_doesnt_compute_to_seq in q; auto.
Qed.

Lemma vbot_diverges_alpha {o} :
  forall lib (v : NVar) (t : @NTerm o),
    !((mk_vbot v) =a=v>(lib) t).
Proof.
  introv h.
  unfold computes_to_value_alpha in h; exrepnd.
  apply vbot_diverges in h1; auto.
Qed.

Lemma vbot_diverges_bar {o} :
  forall {lib} (bar : NeBarLib lib) (v : NVar) (t : @NTerm o),
    !((mk_vbot v) =b=v>(bar) t).
Proof.
  introv h.
  apply computes_to_value_bar_implies_computes_to_value_alpha in h; exrepnd.
  apply vbot_diverges_alpha in h0; auto.
Qed.

Lemma vbot_doesnt_raise_an_exception_alpha {o} :
  forall lib (a : @NTerm o) (v : NVar) (e : NTerm),
    !((mk_vbot v) =a=e>(a,lib) e).
Proof.
  introv h.
  unfold computes_to_exception_alpha in h; exrepnd.
  apply vbot_doesnt_raise_an_exception in h0; auto.
Qed.

Lemma vbot_doesnt_raise_an_exception_bar {o} :
  forall {lib} (bar : NeBarLib lib) (a : @NTerm o) (v : NVar) (e : NTerm),
    !((mk_vbot v) =b=e>(a,bar) e).
Proof.
  introv h.
  apply computes_to_exception_bar_implies_computes_to_exception_alpha in h; exrepnd.
  apply vbot_doesnt_raise_an_exception_alpha in h0; auto.
Qed.

Lemma vbot_doesnt_compute_to_seq_alpha {o} :
  forall lib (v : NVar) (f : @ntseq o),
    !((mk_vbot v) =a=s>(lib) f).
Proof.
  introv h.
  unfold computes_to_seq_alpha in h; exrepnd.
  apply vbot_doesnt_compute_to_seq in h1; auto.
Qed.

Lemma vbot_doesnt_compute_to_seq_bar {o} :
  forall {lib} (bar : NeBarLib lib) (v : NVar) (f : @ntseq o),
    !((mk_vbot v) =b=s>(bar) f).
Proof.
  introv h.
  apply computes_to_seq_bar_implies_computes_to_seq_alpha in h; exrepnd.
  apply vbot_doesnt_compute_to_seq_alpha in h0; auto.
Qed.


(**

  The following lemma shows that approx_open doesn't preserve
  closeness because, for example, bottom is less than any variable.

 *)
Lemma approx_ext_open_doesnt_preserve_closeness {p} :
  forall lib, approx_ext_open lib mk_bot (@mk_var p nvarx).
Proof.
  introv; unfold approx_ext_open, olift; dands; auto.
  rw @nt_wf_eq; apply wf_bot.

  introv.
  generalize (lsubst_mk_bot sub); intro k; exrepnd; rw k0; clear k0.
  introv wfs ispb ispv.
  constructor.
  unfold close_compute_ext; dands; auto; introv comp; tcsp.

  - apply vbot_diverges_bar in comp; sp.

  - apply vbot_doesnt_raise_an_exception_bar in comp; sp.

(*
  - apply vbot_doesnt_mark in comp; sp.
 *)

  - apply vbot_doesnt_compute_to_seq_bar in comp; tcsp.
Qed.

(* begin hide *)

Lemma le_bin_rel_or :  forall (T:[univ] ) (l1 l2 r1 r2 : bin_rel T),
  le_bin_rel l1 r1
  -> le_bin_rel l2 r2
  -> le_bin_rel (l1 \2/  l2)  (r1 \2/ r2).
Proof.
  introv H1l H2l.
  introv Hb.
  dorn Hb; auto.
Defined.


Lemma close_comput_mon {p} :
  forall lib l r,
    le_bin_rel l r
    -> le_bin_rel (@close_compute_ext p lib l) (close_compute_ext lib r).
Proof.
  intros lib t1 t2 ra rb Hcl Hrab.
  allunfold @close_compute_ext. repnd.
  dands; auto; introv comp.

  - apply Hrab2 in comp.
    parallel tr_subterms Hrelbt.
    repnd.
    split;auto.
    eapply le_lblift2;[|eauto]; eauto 3 with slow.

  - apply Hrab3 in comp; exrepnd.
    exists a' e'; dands; auto.

  - apply Hrab4 in comp; exrepnd.
    eexists; dands; eauto.
Defined.

Lemma le_bin_rel_approx_ext {p} :
  forall lib l r,
  le_bin_rel l r
  -> le_bin_rel (@approx_ext_aux p lib l) (approx_ext_aux lib r).
Proof.
  cofix. introv Hle HH.
  invertsn HH.
  constructor.
  eapply close_comput_mon; eauto.
  apply le_bin_rel_or; auto.
Qed.



(*
Lemma approx_alpha_rw_l_aux: forall a b a' lva lvb lva',
  (alpha_eq a a'
  -> approx_ext a b
  -> approx_ext a' b) #
  (alpha_eq_bterm  (bterm lva a) (bterm lva' a')
  -> blift approx_open (bterm lva a) (bterm lvb b)
  -> blift approx_open (bterm lva' a') (bterm lvb b)).
Proof.
  unfold blift. unfold olift.
  cofix.
 *)

Lemma computes_to_seq_alpha_implies {o} :
  forall lib (t1 t2 : @NTerm o) f,
    nt_wf t1
    -> alpha_eq t1 t2
    -> (t1 =s>(lib) f)
    -> {f' : ntseq & (t2 =s>(lib) f') # (forall n, alpha_eq (f n) (f' n))}.
Proof.
  introv wf aeq comp.
  eapply computation3.reduces_to_alpha in comp; eauto 3 with slow.
  exrepnd.
  inversion comp0 as [|? ? imp|]; subst; clear comp0.
  eexists; dands; eauto.
Qed.

Lemma computes_to_seq_alpha_alpha_implies {o} :
  forall lib (t1 t2 : @NTerm o) f,
    nt_wf t1
    -> alpha_eq t1 t2
    -> (t1 =a=s>(lib) f)
    -> (t2 =a=s>(lib) f).
Proof.
  introv wf aeq comp.
  unfold computes_to_seq_alpha in *; exrepnd.
  eapply computes_to_seq_alpha_implies in comp1;[| |eauto];auto.
  exrepnd.
  exists f'; dands; auto.
  introv; eapply alpha_eq_trans; eauto.
Qed.
Hint Resolve computes_to_seq_alpha_alpha_implies : slow.

Lemma computes_to_value_alpha_alpha {o} :
  forall lib (t1 t2 : @NTerm o) v,
    nt_wf t1
    -> alpha_eq t1 t2
    -> (t1 =a=v>(lib) v)
    -> (t2 =a=v>(lib) v).
Proof.
  introv wf aeq comp.
  unfold computes_to_value_alpha in *; exrepnd.
  eapply compute_to_value_alpha in comp1;[| |eauto];auto.
  exrepnd.
  eexists; dands; eauto.
  eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_alpha_alpha : slow.

Lemma computes_to_exception_alpha_alpha_implies {o} :
  forall lib (t1 t2 : @NTerm o) a b,
    nt_wf t1
    -> alpha_eq t1 t2
    -> (t1 =a=e>(a,lib) b)
    -> (t2 =a=e>(a,lib) b).
Proof.
  introv wf aeq comp.
  unfold computes_to_exception_alpha in *; exrepnd.
  eapply compute_to_exception_alpha in comp0;[| |eauto];auto.
  exrepnd.
  eexists; eexists; dands; eauto; eauto 3 with slow.
Qed.
Hint Resolve computes_to_exception_alpha_alpha_implies : slow.

Lemma computes_to_value_bar_alpha_implies {o} :
  forall {lib} (bar : BarLib lib) (t t' : @NTerm o) v,
    nt_wf t
    -> alpha_eq t t'
    -> t =b=v>(bar) v
    -> t' =b=v>(bar) v.
Proof.
  introv wf aeq comp ext ext'.
  pose proof (comp lib' ext lib'0 ext') as q; simpl in q; eauto 2 with slow.
Qed.
Hint Resolve computes_to_value_bar_alpha_implies : slow.

Lemma computes_to_exception_bar_alpha_implies {o} :
  forall {lib} (bar : BarLib lib) (t t' : @NTerm o) a b,
    nt_wf t
    -> alpha_eq t t'
    -> t =b=e>(a,bar) b
    -> t' =b=e>(a,bar) b.
Proof.
  introv wf aeq comp ext ext'.
  pose proof (comp lib' ext lib'0 ext') as q; simpl in q; eauto 2 with slow.
Qed.
Hint Resolve computes_to_exception_bar_alpha_implies : slow.

Lemma computes_to_seq_bar_alpha_implies {o} :
  forall {lib} (bar : BarLib lib) (t t' : @NTerm o) b,
    nt_wf t
    -> alpha_eq t t'
    -> t =b=s>(bar) b
    -> t' =b=s>(bar) b.
Proof.
  introv wf aeq comp ext ext'.
  pose proof (comp lib' ext lib'0 ext') as q; simpl in q; eauto 2 with slow.
Qed.
Hint Resolve computes_to_seq_bar_alpha_implies : slow.

Lemma respects_alpha_r_approx_ext_aux_bot2 {p} :
  forall lib, respects_alpha_r (@approx_ext_aux p lib bot2).
Proof.
  cofix IND.
  introv aeq ap.
  destruct ap as [cc].
  destruct cc as [isp1 cc].
  destruct cc as [isp2 cc].
  destruct cc as [cv cc].
  destruct cc as [ce cc].
  destruct cc as [cs cc].
  constructor.
  unfold close_compute_ext; dands; auto.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear ce cs; introv ca; GC.
    applydup @alpha_prog_eauto in aeq as ispb'; eauto 3 with slow.
    apply cv in ca; exrepnd; clear cv.

    eapply computes_to_value_bar_alpha_implies in ca1;[| |eauto];eauto 2 with slow;[].
    eexists; dands; eauto.

  - clear cv; allunfold @close_compute_exc_ext; introv ca.
    applydup @alpha_prog_eauto in aeq as ispb'; eauto 3 with slow.
    apply ce in ca; exrepnd; clear ce.
    repdors; try (complete (allunfold @bot2; sp)).

    eapply computes_to_exception_bar_alpha_implies in ca0;[| |eauto];eauto 2 with slow;[].
    eexists; eexists; dands; eauto.

  - introv comp.
    applydup @alpha_prog_eauto in aeq as ispb'; eauto 3 with slow.
    apply cs in comp; exrepnd.

    eapply computes_to_seq_bar_alpha_implies in comp1;[| |eauto];eauto 2 with slow;[].
    eexists; eexists; dands; eauto.
Qed.

Lemma respects_alpha_r_approx_ext_aux_bot2_or_bot2 {p} :
  forall lib, respects_alpha_r (@approx_ext_aux p lib bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_r_approx_ext_aux_bot2 _ _ _ b') in ap; auto.
Qed.

Lemma computes_to_value_implies_computes_to_value_ext {o} :
  forall lib (a b : @NTerm o),
    wf_term a
    -> a =v>(lib) b
    -> a =e=v>(lib) b.
Proof.
  introv wf comp ext.
  eapply lib_extends_preserves_computes_to_value; eauto.
Qed.
Hint Resolve computes_to_value_implies_computes_to_value_ext : slow.

Lemma computes_to_value_implies_computes_to_value_bar {o} :
  forall {lib} (bar : BarLib lib) (a b : @NTerm o),
    wf_term a
    -> a =v>(lib) b
    -> a =b=v>(bar) b.
Proof.
  introv wf comp ext ext'.
  exists b; dands; eauto 2 with slow.
  eapply lib_extends_preserves_computes_to_value;[| |eauto]; eauto 3 with slow.
Qed.
Hint Resolve computes_to_value_implies_computes_to_value_bar : slow.

Lemma computes_to_exception_implies_computes_to_exception_bar {o} :
  forall {lib} (bar : BarLib lib) (a b c : @NTerm o),
    wf_term a
    -> a =e>(c,lib) b
    -> a =b=e>(c,bar) b.
Proof.
  introv wf comp ext ext'.
  eexists; eexists; dands; eauto 2 with slow.
  eapply (lib_extends_preserves_reduces_to _ lib'0) in comp; eauto 3 with slow.
Qed.
Hint Resolve computes_to_exception_implies_computes_to_exception_bar : slow.

Lemma computes_to_seq_implies_computes_to_seq_bar {o} :
  forall {lib} (bar : BarLib lib) (a : @NTerm o) f,
    wf_term a
    -> a =s>(lib) f
    -> a =b=s>(bar) f.
Proof.
  introv wf comp ext ext'.
  exists f; dands; eauto 2 with slow.
  eapply lib_extends_preserves_reduces_to;[| |eauto]; eauto 3 with slow.
Qed.
Hint Resolve computes_to_seq_implies_computes_to_seq_bar : slow.

Lemma computes_to_exception_implies_computes_to_exception_ext {o} :
  forall lib (a b c : @NTerm o),
    wf_term a
    -> a =e>(b,lib) c
    -> a =e=e>(b,lib) c.
Proof.
  introv wf comp ext.
  eapply lib_extends_preserves_reduces_to; eauto.
Qed.
Hint Resolve computes_to_exception_implies_computes_to_exception_ext : slow.

Lemma computes_to_seq_implies_computes_to_seq_ext {o} :
  forall lib (a : @NTerm o) f,
    wf_term a
    -> a =s>(lib) f
    -> a =e=s>(lib) f.
Proof.
  introv wf comp ext.
  eapply lib_extends_preserves_reduces_to; eauto.
Qed.
Hint Resolve computes_to_seq_implies_computes_to_seq_ext : slow.

Lemma respects_alpha_l_approx_ext_aux_bot2 {p} :
  forall lib, respects_alpha_l (@approx_ext_aux p lib bot2).
Proof.
  cofix IND.
  introv aeq ap.
  destruct ap as [cc].
  destruct cc as [isp1 cc].
  destruct cc as [isp2 cc].
  destruct cc as [cv cc].
  destruct cc as [ce cc].
  destruct cc as [cs cc].
  constructor.
  unfold close_compute_ext; dands; auto.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear ce cs; introv ca'.
    applydup @alpha_prog_eauto in aeq as ispa'; auto.
    apply alpha_eq_sym in aeq.
    eapply computes_to_value_bar_alpha_implies in ca';[| |eauto];eauto 2 with slow.

  - clear cv cs; introv ca.
    applydup @alpha_prog_eauto in aeq as ispa'; auto.
    apply alpha_eq_sym in aeq.
    eapply computes_to_exception_bar_alpha_implies in ca;[| |eauto];eauto 2 with slow.

  - introv comp.
    applydup @alpha_prog_eauto in aeq as wfa'; auto.
    apply alpha_eq_sym in aeq.
    eapply computes_to_seq_bar_alpha_implies in comp;[| |eauto];eauto 2 with slow.
Qed.

Lemma respects_alpha_l_approx_ext_aux_bot2_or_bot2 {p} :
  forall lib, respects_alpha_l (@approx_ext_aux p lib bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_l_approx_ext_aux_bot2 _ _ _ a') in ap; auto.
Qed.

Lemma respects_alphal_close_compute_ext {p} :
  forall lib R,
    respects_alpha_l R
    -> respects_alpha_l (@close_compute_ext p lib R).
Proof.
  introv rR Hal Hap.
  repnud Hap.
  unfolds_base.
  alpha_hyps Hal.
  dands; eauto 2 with slow.

  - introv Hcv.
    apply alpha_eq_sym in Hal.
    eapply computes_to_value_bar_alpha_implies in Hcv;[| |eauto];eauto 2 with slow.

  - introv comp.
    apply alpha_eq_sym in Hal.
    eapply computes_to_exception_bar_alpha_implies in comp;[| |eauto];eauto 2 with slow.

  - introv comp.
    apply alpha_eq_sym in Hal.
    eapply computes_to_seq_bar_alpha_implies in comp;[| |eauto];eauto 2 with slow.
Qed.

Lemma approxr_ext_alpha_rw_l_aux {p} :
  forall lib r a b a',
    respects_alpha_l (approx_ext_aux lib r \2/ r)
    -> @alpha_eq p a a'
    -> approx_ext_aux lib r a b
    -> approx_ext_aux lib r a' b.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphal_close_compute_ext; auto.
Qed.

Lemma approx_ext_alpha_rw_l_aux {p} :
  forall lib a b a',
    @alpha_eq p a a'
    -> approx_ext lib a b
    -> approx_ext lib a' b.
Proof.
 unfold approx_ext.
 introv.
 generalize (@respects_alpha_l_approx_ext_aux_bot2_or_bot2 p lib).
 revert a b a'.
 exact (approxr_ext_alpha_rw_l_aux lib bot2).
Qed.

Lemma respects_alphar_close_compute_ext {p} :
  forall lib R,
    respects_alpha_r R
    -> respects_alpha_r (@close_compute_ext p lib R).
Proof.
  introv rR Hal Hap.
  repnud Hap.
  unfolds_base.
  alpha_hyps Hal.
  dands; eauto 2 with slow.

  - introv Hcv.
    apply Hap2 in Hcv.
    exrepnd.
    eapply computes_to_value_bar_alpha_implies in Hcv1;[| |eauto];eauto 2 with slow;[].
    eexists; dands; eauto.

  - introv comp.
    apply Hap3 in comp; exrepnd.
    eapply computes_to_exception_bar_alpha_implies in comp0;[| |eauto];eauto 2 with slow;[].
    eexists; dands; eauto.

  - introv comp.
    apply Hap4 in comp; exrepnd.
    eapply computes_to_seq_bar_alpha_implies in comp1;[| |eauto];eauto 2 with slow;[].
    eexists; dands; eauto.
Qed.

Lemma approxr_ext_alpha_rw_r_aux {p} :
  forall lib r a b b',
    respects_alpha_r (approx_ext_aux lib r \2/ r)
    -> @alpha_eq p b b'
    -> approx_ext_aux lib r a b
    -> approx_ext_aux lib r a b'.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphar_close_compute_ext; auto.
Qed.

Lemma approx_ext_alpha_rw_r_aux {p} :
  forall lib a b b',
    @alpha_eq p b b'
    -> approx_ext lib a b
    -> approx_ext lib a b'.
Proof.
 unfold approx_ext.
 introv.
 generalize (@respects_alpha_r_approx_ext_aux_bot2_or_bot2 p lib).
 revert a b b'.
 exact (approxr_ext_alpha_rw_r_aux lib bot2).
Qed.

Hint Resolve approx_ext_alpha_rw_r_aux : slowbad.
Hint Resolve approx_ext_alpha_rw_l_aux : slowbad.

(* end hide *)
Lemma respects_alpha_close_compute_ext {p} :
  forall lib R, respects_alpha R -> respects_alpha (@close_compute_ext p lib R).
Proof.
  introv ra.
  destruct ra.
  split.
  - apply respects_alphal_close_compute_ext; auto.
  - apply respects_alphar_close_compute_ext; auto.
Qed.

Corollary respects_alpha_approx_ext {p} :
  forall lib, respects_alpha (@approx_ext p lib).
Proof.
  split; introv; intros; eauto with slowbad.
Qed.
Hint Immediate respects_alpha_approx_ext.


(* begin hide *)


Hint Resolve respects_alpha_close_compute_ext : respects.

Theorem approx_ext_open_relates_only_wf {p} :
  forall lib (t1 t2 : @NTerm p),
    approx_ext_open lib t1 t2
    -> nt_wf t1 # nt_wf t2.
Proof.
  introv.
  apply olift_relates_only_wf.
Qed.





Hint Resolve respects_alpha_approx_ext : respects.

(** key helper for lemma 0.6 in annotated paper *)
Theorem approx_ext_open_lsubst {p} :
  forall lib a b lvi lvo,
    let sub := @var_ren p lvi lvo in
    approx_ext_open lib a b
    -> approx_ext_open lib (lsubst a sub) (lsubst b sub).
Proof.
  simpl. intros. apply olift_vars_lsubst; eauto with respects.
Qed.

Lemma approx_ext_open_alpha_rw_l_aux {p} :
  forall lib a b a',
  @alpha_eq p a a'
  -> approx_ext_open lib a b
  -> approx_ext_open lib a' b.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold approx_ext_open.
  rwg Hal. trivial.
Qed.

Lemma approx_ext_open_alpha_rw_r_aux {p} :
  forall lib a b b',
  @alpha_eq p b b'
  -> approx_ext_open lib a b
  -> approx_ext_open lib a b'.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold approx_ext_open.
  rwg Hal. trivial.
Qed.

Hint Resolve approx_ext_open_alpha_rw_l_aux : slowbad.
Hint Resolve approx_ext_open_alpha_rw_r_aux : slowbad.


Hint Resolve alphaeqbt_numbvars : slow.




(** this lemma can simplify many proofs a lot
    e.g. approx_trans, some lemma at the beginning of cequiv.
    whenever we destruct 2 lblift we get 2 sets
    of variables and this lemma helps us inify the,*)


Lemma approxbtd_change2 {p} : forall lib bt1 bt2 (lvn lva: list NVar),
  approx_ext_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ approx_ext_open lib nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # disjoint ((bound_vars nt1') ++ (bound_vars nt2')) (lva ++ lvn)

   }.
Proof.
  introv Hab Hnr Hlen Hdis.
  invertsna Hab Hab. exrepnd.
  applydup @alphaeqbt_numbvars in Hab2.
  allunfold @num_bvars. allsimpl.

  dimp (alpha_bterm_pair_change4 _ _ _ _ _ lvn lva Hab2 Hab1); spcf;[].
  exrepnd.
  unfold approx_ext_open in Hab0.
  rwhg hyp0 Hab0.
  rwhg hyp2 Hab0.
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  split; spc;[|].
  - apply approx_ext_open_lsubst;sp.
  - disjoint_reasoningv; rw @boundvars_lsubst_vars; spc; disjoint_reasoningv.
Qed.

Lemma approxbtd_change {p} : forall lib bt1 bt2 (lvn : list NVar),
  approx_ext_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ approx_ext_open lib nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # disjoint ((bound_vars nt1') ++ (bound_vars nt2')) lvn

   }.
Proof. intros.  apply approxbtd_change2 with (lva:= []); spc.
Qed.

Lemma approxbtd {p} : forall lib bt1 bt2 lva,
  approx_ext_open_bterm lib bt1 bt2
  -> {lvn : (list NVar) & {nt1',nt2' : @NTerm p $ approx_ext_open lib nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # no_repeats lvn
          (* # disjoint lvn (all_vars (get_nt bt1) ++ all_vars (get_nt bt2)) *)
          # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva   } }.
Proof.
  introv Hab.
  pose proof (fresh_vars (num_bvars bt1) 
      (free_vars_bterm bt1  ++ free_vars_bterm bt2 ++ lva)  ).
  exrepnd. apply @approxbtd_change2 with (lvn := lvn) (lva:=lva) in Hab;spc;
      [| disjoint_reasoningv].
  exrepnd.
  exists lvn nt1' nt2';spc.
  disjoint_reasoningv.
Qed.

Hint Resolve lsubst_alpha_congr2: slow.
Hint Resolve alpha_eq_sym: slow.
Hint Resolve alpha_eq_trans: slow.
Hint Rewrite @alphaeq_preserves_free_vars : slow.


Lemma approx_ext_alpha_rw_l {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_ext lib a b <=> approx_ext lib a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.

Lemma approx_ext_alpha_rw_r {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_ext lib b a <=> approx_ext lib b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.


Lemma remove_bot_approx_ext {p} :
  forall lib, eq_bin_rel (approx_ext_aux lib bot2 \2/ bot2) (@approx_ext p lib).
Proof. unfold eq_bin_rel, le_bin_rel. split; eauto;[].
  introv Hp. dorn Hp; eauto. repnud Hp.
  allsimpl. contradiction.
Qed.

Hint Resolve remove_bot_approx_ext.

Lemma clearbots_olift {p} : forall lib nt1 nt2,
  (@olift p (approx_ext_aux lib bot2 \2/ bot2)) nt1 nt2
 <=> approx_ext_open lib nt1 nt2.
Proof.
  introv.
  destruct (@eq_blift_olift p _ _ (remove_bot_approx_ext lib)).
  unfold le_bin_rel in l. unfold le_bin_rel in l0.
  unfold approx_ext_open.
  split; auto.
Qed.

Lemma clearbot_relbt {p} : forall lib (l1bt l2bt : list (@BTerm p)),
 lblift (olift (approx_ext_aux lib bot2 \2/ bot2)) l1bt l2bt
  -> lblift (olift (approx_ext lib)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_approx_ext.
Qed.
Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: alphaeqbt.


(* end hide *)
(** %\noindent% Now, we wish to prove that [approx] is transitive.
    The proof is essentially a co-indictive argument.
    However, to get a strong enough co-induction hypothesis
    when we formalize the proof using the [approx_acc] lemma above,
    we have to state it in a more general way.
    Intuitively, this is because, alpha equality is
    baked into the definition of [blift].
*)

Lemma approx_ext_trans_aux {p} :
  forall lib a b c a' c',
    alpha_eq a a'
    -> @alpha_eq p c c'
    -> approx_ext lib a' b
    -> approx_ext lib b c'
    -> approx_ext lib a c.
Proof.
  intro lib.
  pose proof
  (approx_ext_acc lib (fun a c => { b,a',c' : NTerm $
       alpha_eq a a' # alpha_eq c c' # approx_ext lib a' b # approx_ext lib b c'   })
     (@bot2 p)) as HH.
  allsimpl.
  match goal with
  [ HH : _ -> ?B |- _ ] => assert B; [|
    intros; eapply X; eexists; eexists; eexists; eauto;fail]
  end.
  apply HH.
  intros.
  rename x0 into a.
  rename x1 into c.
  rename PR into HCCCC.
  exrepnd.
  rename HCCCC1 into Hala.
  rename HCCCC2 into Halc.
  rename HCCCC3 into Hab.
  rename HCCCC0 into Hbc.
  apply (approx_ext_alpha_rw_l _ _ _ _ Hala) in Hab; eauto.
  apply (approx_ext_alpha_rw_r _ _ _ _ Halc) in Hbc; eauto.
  clear Hala Halc.
  invertsn Hab.
  invertsn Hbc.
  constructor.
  unfold close_compute_ext in Hab at 1.
  unfold close_compute_ext in Hbc at 1.
  unfold close_compute_ext at 1; dands; spcf.

  - introv Hcv.
    applydup_clear Hab in Hcv. exrepnd.
    rename Hcv0 into Hcb.
    applydup_clear Hbc2 in Hcb. exrepnd.
    exists tr_subterms0; sp.
    allunfold @lblift; dands; spcf; try omega;[].

    introv Hlt.
    applydup Hcv1 in Hlt. repnd.
    rw  Hcv0 in Hlt.
    applydup Hcb1 in Hlt.
    rename Hlt1 into H1rb.
    rename Hlt0 into H2rb.
    allunfold @blift; exrepnd; try omega.
    pose proof (fresh_vars (length lv)
                           (all_vars nt1
                                     ++ all_vars nt2
                                     ++ all_vars nt0
                                     ++ all_vars nt3)) as Hfr.
    exrepnd.
    dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn H1rb0 H1rb2);
      try(rename hyp into H1c); exrepnd; spc;[| disjoint_reasoningv].
    assert (alpha_eq_bterm (bterm lv nt1) (bterm lv0 nt3)) as Hbt by (eauto with slow).
    (* transitivity of alpha_eq_bterm*)
    apply alphaeqbt_numbvars in Hbt.
    allunfold @num_bvars.
    allsimpl.
    dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn H2rb0 H2rb2); try(rename hyp into H2c);
    exrepnd;spc;[| disjoint_reasoningv;fail].
    exists lvn.
    exists (lsubst nt2n0 (var_ren lv0 lvn)).
    exists (lsubst nt1n (var_ren lv lvn)).
    dands; spc;[].
    assert (alpha_eq_bterm
              (bterm lvn (lsubst nt1n0 (var_ren lv0 lvn)))
              (bterm lvn (lsubst nt2n (var_ren lv lvn)))
           ) as Hlink by (eauto with alphaeqbt).
    apply alpha_eq_bterm_triv in Hlink.
    (repeat match goal with
              | [ H : alpha_eq_bterm _ _ |- _ ] => thin H
            end).

    apply clearbots_olift in H1rb1.
    apply clearbots_olift in H2rb1.

    unfold approx_ext_open in H2rb1.
    rwhg H2c0 H2rb1.
    rwhg H2c2 H2rb1.

    unfold approx_ext_open in H1rb1.
    rwhg H1c0 H1rb1.
    rwhg H1c2 H1rb1.

    rename H2rb1 into H2ap.
    rename H1rb1 into H1ap.

    clear H1c0 H1c2 H2c0 H2c2.

    apply approx_ext_open_lsubst with (lvi:=lv) (lvo:=lvn) in H1ap.
    apply approx_ext_open_lsubst with (lvi:=lv0) (lvo:=lvn) in H2ap.
    unfold approx_ext_open in H2ap.
    rwhg Hlink H2ap.
    assert(approx_ext_open
             lib
             (lsubst nt2n0 (var_ren lv0 lvn))
             (lsubst nt2n (var_ren lv lvn))) as Hapl by (eauto with slow).
    clear H2ap.
    (* setting the stage for approx_ext_open_trans proof .. identical var/hym names *)
    rename a into a999temp.
    rename b into b999temp.
    rename c into c999temp.

    remember (lsubst nt2n0 (var_ren lv0 lvn)) as a.
    remember (lsubst nt2n (var_ren lv lvn)) as b.
    remember (lsubst nt1n (var_ren lv lvn)) as c.
    rename Hapl into Hab.
    rename H1ap into Hbc2.

    clear Heqa Heqb Heqc.
    clear dependent a999temp.
    clear dependent b999temp.
    clear dependent c999temp.
    clear dependent lvn.
    clear dependent n.
    clear dependent tl_subterms.
    clear dependent tr_subterms.
    clear dependent lv.
    clear lv0 nt0 nt1 nt2 nt3 nt1n nt2n nt1n0 nt2n0 tr_subterms0 c0.

    repnud Hab. repnud Hbc2.
    unfold olift. split;auto;try(complete (allunfold @olift; sp)).
    split; auto;try(complete (allunfold @olift; sp)).
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.

    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    right.
    remember (sub_keep_first sub (free_vars c ++ free_vars a)) as subt.
    remember (@subst_axiom p (free_vars b)) as subb.
    remember (subt++subb) as sub'.
    assert (prog_sub subb) as Hsubb by (subst;auto).

    pose proof (prog_lsubst_app2 a subt subb Hispa Hsubb) as Heqa.
    pose proof (prog_lsubst_app2 c subt subb Hispc Hsubb) as Heqc.
    assert(isprogram (lsubst b (subt++subb))).
    + apply isprogram_lsubst; eauto; try(complete (allunfold @olift; sp)).
      apply sub_app_sat; auto.
      introv Hin. apply in_map_iff. exists (v, @mk_axiom p). split; auto.
      apply in_app_iff. right. subst.
      unfold subst_axiom. apply in_map_iff. eexists;eauto.
    + rw Heqc in Hispc. rw Heqa in Hispa.
      apply prog_sub_implies_wf in Hsubb.
      apply prog_sub_implies_wf in Xprog.
      assert (wf_sub (subt ++ subb)) by (apply sub_app_sat;auto).
      apply CIH.
      exists (lsubst b (subt++subb)).
      eexists (lsubst a subt).
      eexists (lsubst c subt).
      dands; spc;
      ((rw  Heqc; eapply Hbc2) || (rw Heqa; eapply Hab)); eauto.

  - repnd.
    clear Hab2 Hbc2 Hab Hbc.
    introv ce.
    allunfold @close_compute_exc_ext.
    applydup Hab3 in ce; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    applydup Hbc3 in ce1; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    exists a'1 e'0; dands; auto.
    + generalize (CIH a0 a'1); intro k.
      autodimp k hyp.
      exists a'0 a0 a'1; dands; auto.
    + generalize (CIH e e'0); intro k.
      autodimp k hyp.
      exists e' e e'0; dands; auto.

(*
  - repnd.
    clear Hab2 Hab3 Hbc2 Hbc3.
    introv comp.
    apply Hab in comp; apply Hbc in comp; auto.
 *)

  - repnd.
    introv comp.
    apply Hab4 in comp; exrepnd.
    apply Hbc4 in comp1; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp2 n) as h; clear comp2.
    pose proof (comp0 n) as q; clear comp0.
    repndors; eauto;[].

    right.
    apply CIH.
    eexists; eexists; eexists; dands; eauto.
Qed.


Corollary approx_ext_trans {p} :
  forall lib (a b c : @NTerm p),
    approx_ext lib a b
    -> approx_ext lib b c
    -> approx_ext lib a c.
Proof.
 intros. eapply approx_ext_trans_aux; eauto with slow.
Qed.

(* begin hide *)



Lemma approx_ext_wf_term {p} :
  forall lib (a b : @NTerm p),
    approx_ext lib a b -> wf_term a # wf_term b.
Proof.
  intros. inversion X; subst.
  unfold close_compute_ext in X0; sp; subst; allunfold @isprogram; sp; allrw @nt_wf_eq; sp.
Qed.

Lemma approx_ext_isprog {p} :
  forall lib (a b : @NTerm p),
    approx_ext lib a b -> isprog a # isprog b.
Proof.
  intros. inversion X; subst.
  unfold close_compute_ext in X0; sp; allrw @isprog_eq; sp.
Qed.

Lemma approxc_ext_refl {p} :
  forall lib (t : @CTerm p), approxc_ext lib t t.
Proof.
  intro; destruct t; unfold approxc_ext; simpl.
  apply approx_ext_refl; allrw @isprogram_eq; sp.
Qed.

Lemma approxc_ext_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p),
    approxc_ext lib t1 t2 -> approxc_ext lib t2 t3 -> approxc_ext lib t1 t3.
Proof.
  intro; destruct t1, t2, t3; unfold approxc_ext; simpl.
  apply approx_ext_trans.
Qed.

Lemma approx_ext_canonical_form {p} :
  forall lib t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> approx_ext lib t t'
    -> {bterms' : list (@BTerm p) &
         computes_to_value_alpha lib t' (oterm (Can op) bterms')
         # lblift (approx_ext_open lib) bterms bterms' }.
Proof.
  intros ? ? ? ? ? Hcomp Hap.
  invertsn Hap.
  repnud Hap.

  apply (computes_to_value_implies_computes_to_value_bar (trivial_ne_bar lib)) in Hcomp; eauto 3 with slow.
  apply Hap2 in Hcomp. exrepnd.

  apply clearbot_relbt in Hcomp0.
  eexists; dands; eauto 3 with slow.
  eapply Hcomp1;[|eapply lib_extends_refl]; simpl; eauto 3 with slow.
Qed.


Lemma exception_approx_ext {p} :
  forall lib t t' a e,
    (t =e>( a, lib)e)
    -> approx_ext lib t t'
    -> { a' : @NTerm p &
       { e' : @NTerm p &
         ( t' =a=e>( a', lib)e')
         # (approx_ext_aux lib bot2 a a'[+]bot2 a a')
         # (approx_ext_aux lib bot2 e e'[+]bot2 e e') }}.
Proof.
  introv Hcomp Hap.
  invertsn Hap. repnud Hap.

  apply (computes_to_exception_implies_computes_to_exception_bar (trivial_ne_bar lib)) in Hcomp; eauto 3 with slow.
  apply Hap3 in Hcomp. exrepnd.

  repndors; tcsp; try (complete (inversion Hcomp2)); try (complete (inversion Hcomp1)).
  eexists; eexists; dands; eauto 3 with slow.
  eapply Hcomp0;[|eapply lib_extends_refl]; simpl; eauto 3 with slow.
Qed.

Hint Resolve lib_extends_preserves_reduces_to : slow.

Lemma reduces_to_computes_to_value_alpha_trans {o} :
  forall lib (a b v : @NTerm o),
    reduces_to lib a b
    -> b =a=v>(lib) v
    -> a =a=v>(lib) v.
Proof.
  introv comp1 comp2.
  unfold computes_to_value_alpha in *; exrepnd.
  unfold computes_to_value in *; repnd.
  exists c; dands; auto.
  eapply reduces_to_trans; eauto.
Qed.
Hint Resolve reduces_to_computes_to_value_alpha_trans : slow.

Lemma reduces_to_computes_to_exception_alpha_trans {o} :
  forall lib (a b u v : @NTerm o),
    reduces_to lib a b
    -> b =a=e>(u,lib) v
    -> a =a=e>(u,lib) v.
Proof.
  introv comp1 comp2.
  unfold computes_to_exception_alpha in *; exrepnd.
  unfold computes_to_exception in *; repnd.
  exists c d; dands; auto.
  eapply reduces_to_trans; eauto.
Qed.
Hint Resolve reduces_to_computes_to_exception_alpha_trans : slow.

Lemma reduces_to_computes_to_seq_alpha_trans {o} :
  forall lib (a b : @NTerm o) f,
    reduces_to lib a b
    -> b =a=s>(lib) f
    -> a =a=s>(lib) f.
Proof.
  introv comp1 comp2.
  unfold computes_to_seq_alpha in *; exrepnd.
  unfold computes_to_seq in *; repnd.
  exists g; dands; auto.
  eapply reduces_to_trans; eauto.
Qed.
Hint Resolve reduces_to_computes_to_seq_alpha_trans : slow.

Lemma approx_ext_comput_functionality_left {p} :
  forall lib a a' b,
    @reduces_to p lib a a'
    -> approx_ext lib a b
    -> approx_ext lib a' b.
Proof.
  intros ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold close_compute_ext. applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2.
    allunfold @computes_to_value_ext.
    introv ext ext'; applydup comp in ext';auto.
    apply (lib_extends_preserves_reduces_to _ lib'0) in Hred; eauto 3 with slow.

  - apply Hap3.
    introv ext ext'; applydup comp in ext';auto.
    apply (lib_extends_preserves_reduces_to _ lib'0) in Hred; eauto 3 with slow.

  - apply Hap4.
    introv ext ext'; applydup comp in ext';auto.
    apply (lib_extends_preserves_reduces_to _ lib'0) in Hred; eauto 3 with slow.
Qed.

Lemma reduces_to_isvalue_like_eq {o} :
  forall lib (t u v : @NTerm o),
    isvalue_like v
    -> reduces_to lib t u
    -> reduces_to lib t v
    -> reduces_to lib u v.
Proof.
  introv isv r1 r2.
  eapply reduces_to_or in r1;[|exact r2].
  repndors; auto.
  apply reduces_to_if_isvalue_like in r1; auto; subst; eauto 3 with slow.
Qed.

Lemma reduces_to_value_ext_eq {o} :
  forall lib (t u v : @NTerm o),
    wf_term t
    -> t =e=v>(lib) v
    -> reduces_to lib t u
    -> u =e=v>(lib) v.
Proof.
  introv wf comp r ext; applydup comp in ext.
  eapply reduces_to_value_eq; eauto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_value_ext_eq : slow.

Lemma reduces_to_exception_ext_eq {o} :
  forall lib (a t u e : @NTerm o),
    wf_term t
    -> t =e=e>(a,lib) e
    -> reduces_to lib t u
    -> u =e=e>(a,lib) e.
Proof.
  introv wf comp r ext; applydup comp in ext.
  eapply reduces_to_exception_eq; eauto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_exception_ext_eq : slow.

Lemma reduces_to_isvalue_like_ext_eq {o} :
  forall lib (t u v : @NTerm o),
    wf_term t
    -> isvalue_like v
    -> reduces_to_ext lib t u
    -> reduces_to lib t v
    -> reduces_to_ext lib u v.
Proof.
  introv wf isv comp r ext; applydup comp in ext.
  eapply reduces_to_isvalue_like_eq; eauto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_isvalue_like_ext_eq : slow.

Lemma reduces_to_seq_ext_eq {o} :
  forall lib (t u : @NTerm o) f,
    wf_term t
    -> t =e=s>(lib) f
    -> reduces_to lib t u
    -> u =e=s>(lib) f.
Proof.
  introv wf comp r ext; applydup comp in ext.
  unfold computes_to_seq in *.
  eapply reduces_to_isvalue_like_eq;[| |eauto]; auto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_seq_ext_eq : slow.

Lemma reduces_to_value_alpha_eq {o} :
  forall lib (t u v : @NTerm o),
    wf_term t
    -> t =a=v>(lib) v
    -> reduces_to lib t u
    -> u =a=v>(lib) v.
Proof.
  introv wf comp r.
  unfold computes_to_value_alpha in *; exrepnd.
  exists c; dands; auto.
  eapply reduces_to_value_eq; eauto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_value_alpha_eq : slow.

Lemma reduces_to_value_bar_eq {o} :
  forall {lib} (bar : BarLib lib) (t u v : @NTerm o),
    wf_term t
    -> t =b=v>(bar) v
    -> reduces_to lib t u
    -> u =b=v>(bar) v.
Proof.
  introv wf comp r ext ext'.
  applydup comp in ext'; auto.
  apply (lib_extends_preserves_reduces_to _ lib'0) in r; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_value_bar_eq : slow.

Lemma reduces_to_exception_alpha_eq {o} :
  forall lib (t u v w : @NTerm o),
    wf_term t
    -> t =a=e>(w,lib) v
    -> reduces_to lib t u
    -> u =a=e>(w,lib) v.
Proof.
  introv wf comp r.
  unfold computes_to_exception_alpha in *; exrepnd.
  exists c d; dands; auto.
  eapply reduces_to_exception_eq; eauto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_exception_alpha_eq : slow.

Lemma reduces_to_exception_bar_eq {o} :
  forall {lib} (bar : BarLib lib) (t u v w : @NTerm o),
    wf_term t
    -> t =b=e>(w,bar) v
    -> reduces_to lib t u
    -> u =b=e>(w,bar) v.
Proof.
  introv wf comp r ext ext'.
  applydup comp in ext'; auto.
  apply (lib_extends_preserves_reduces_to _ lib'0) in r; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_exception_bar_eq : slow.

Lemma reduces_to_seq_alpha_eq {o} :
  forall lib (t u : @NTerm o) f,
    wf_term t
    -> t =a=s>(lib) f
    -> reduces_to lib t u
    -> u =a=s>(lib) f.
Proof.
  introv wf comp r.
  unfold computes_to_seq_alpha in *; exrepnd.
  exists g; dands; auto.
  eapply reduces_to_isvalue_like_eq;[| |eauto]; auto; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_seq_alpha_eq : slow.

Lemma reduces_to_seq_bar_eq {o} :
  forall {lib} (bar : BarLib lib) (t u : @NTerm o) f,
    wf_term t
    -> t =b=s>(bar) f
    -> reduces_to lib t u
    -> u =b=s>(bar) f.
Proof.
  introv wf comp r ext ext'.
  applydup comp in ext'; auto.
  apply (lib_extends_preserves_reduces_to _ lib'0) in r; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_seq_bar_eq : slow.

Lemma approx_ext_comput_functionality_right {p} :
  forall lib a b b',
    @reduces_to p lib b b'
    -> approx_ext lib a b
    -> approx_ext lib a b'.
Proof.
  intros ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold close_compute_ext.
  applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2 in comp. exrepnd. exists tr_subterms.
    split; auto; eauto 4 with slow.

  - apply Hap3 in comp; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    exists a' e'; dands; auto; eauto 4 with slow.

  - apply Hap4 in comp; exrepnd.
    exists f'; dands; auto; eauto 4 with slow.
Qed.

Lemma reduces_to_implies_approx_ext {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx_ext lib x t # approx_ext lib t x.
Proof.
  intros.
  duplicate H.
  apply approx_ext_comput_functionality_left with (b := t) in H; sp.
  apply approx_ext_comput_functionality_right with (a := t) in H0; sp.
  apply approx_ext_refl; sp.
  apply approx_ext_refl; sp.
Qed.

Lemma reduces_to_implies_approx_ext1 {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx_ext lib x t.
Proof.
  introv isp r.
  apply reduces_to_implies_approx_ext in r; sp.
Qed.

Lemma reduces_to_implies_approx_ext2 {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx_ext lib t x.
Proof.
  introv isp r.
  apply reduces_to_implies_approx_ext in r; sp.
Qed.

Lemma approx_ext_if_reduce_to_same {p} :
  forall lib a b c,
    @isprogram p a
    -> isprogram b
    -> reduces_to lib a c
    -> reduces_to lib b c
    -> approx_ext lib a b.
Proof.
  introv ispa ispb reda redb.
  apply @approx_ext_trans with (b := c).
  apply @approx_ext_comput_functionality_right with (b := a); auto.
  apply approx_ext_refl; auto.
  apply @approx_ext_comput_functionality_left with (a := b); auto.
  apply approx_ext_refl; auto.
Qed.

(* end hide *)

Lemma computes_to_value_implies_approx_ext {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx_ext lib x t # approx_ext lib t x.
Proof.
  introv p c.
  unfold computes_to_value in c; repd.
  apply reduces_to_implies_approx_ext in r; sp.
Qed.

Lemma computes_to_exception_implies_approx_ext {o} :
  forall lib a (t x : @NTerm o),
    isprogram t
    -> computes_to_exception lib a t x
    -> approx_ext lib (mk_exception a x) t # approx_ext lib t (mk_exception a x).
Proof.
  introv p c.
  unfold computes_to_exception in c; repd.
  apply reduces_to_implies_approx_ext in c; sp.
Qed.

(* begin hide *)

Lemma computes_to_value_implies_approx_ext1 {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx_ext lib x t.
Proof.
  introv p c.
  apply computes_to_value_implies_approx_ext in c; sp.
Qed.

Lemma computes_to_value_implies_approx_ext2 {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx_ext lib t x.
Proof.
  introv p c.
  apply computes_to_value_implies_approx_ext in c; sp.
Qed.

Lemma reduces_toc_implies_approxc_ext {p} :
  forall lib t x,
    @reduces_toc p lib t x
    -> approxc_ext lib x t # approxc_ext lib t x.
Proof.
  destruct t; destruct x0; unfold reduces_toc, approxc_ext; simpl.
  apply reduces_to_implies_approx_ext.
  rw @isprogram_eq; sp.
Qed.

Lemma computes_to_valc_implies_approxc_ext {p} :
  forall lib t x,
    @computes_to_valc p lib t x
    -> approxc_ext lib x t # approxc_ext lib t x.
Proof.
  destruct t; destruct x0; unfold computes_to_valc, approxc_ext; simpl.
  apply computes_to_value_implies_approx_ext.
  rw @isprogram_eq; sp.
Qed.

Lemma not_hasvalue_ncan {p} :
  forall lib c bts,
    ! hasvalue lib (oterm (@NCan p c) bts).
Proof.
  unfold hasvalue; sp.
Abort.

Lemma computes_to_value_implies_computes_to_value_alpha {o} :
  forall lib (t v : @NTerm o),
    t =v>(lib) v
    -> t =a=v>(lib) v.
Proof.
  introv comp; exists v; dands; auto.
Qed.
Hint Resolve computes_to_value_implies_computes_to_value_alpha : slow.

(* end hide *)
Lemma hasvalue_approx_ext {p} :
  forall lib t u,
    @approx_ext p lib t u
    -> hasvalue lib t
    -> hasvalue lib u.
Proof.
  unfold hasvalue; introv ap hvt; exrepd.
  inversion ap as [cc]; subst.
  unfold close_compute_ext in cc; repnd.
  applydup @computes_to_value_can in c; repndors; exrepd; subst.

  - apply (computes_to_value_implies_computes_to_value_bar (trivial_ne_bar lib)) in c; eauto 3 with slow.
    apply cc2 in c; sp.

    pose proof (p1 lib) as q; simpl in q; autodimp q hyp; eauto 2 with slow.
    pose proof (q lib) as q; autodimp q hyp; eauto 2 with slow; simpl in q.
    unfold computes_to_value_alpha in *; exrepnd.
    eexists; eauto.

  - unfold computes_to_value in c; repnd.
    apply (computes_to_seq_implies_computes_to_seq_bar (trivial_ne_bar lib)) in c0; eauto 3 with slow.
    apply cc4 in c0; sp.

    pose proof (p1 lib) as q; simpl in q; autodimp q hyp; eauto 2 with slow.
    pose proof (q lib) as q; autodimp q hyp; eauto 2 with slow; simpl in q.
    unfold computes_to_seq_alpha in *; exrepnd.
    unfold computes_to_value.
    unfold computes_to_seq in q1.
    eexists; dands; eauto; eauto 3 with slow.
Qed.
(* begin hide *)

Lemma subst_var {p} :
  forall v t,
    subst (@vterm p v) v t = t.
Proof.
  unfold subst; simpl; sp.
  unfold lsubst. simpl. rewrite <- beq_var_refl; sp.
Qed.

(*
    hasvalue (oterm o bts1)
    -> length bts1 = length bts2
    -> (forall vs1 t1 vs2 t2,
          LIn (bterm vs1 t1, bterm vs2 t2) (combine bts1 bts2)
          -> hasvalue t1
          -> hasvalue t2)
    -> hasvalue (oterm o bts2)
*)

Lemma isprog_vars_vterm {o} :
  forall v vs, @isprog_vars o vs (vterm v) <=> LIn v vs.
Proof.
  introv.
  unfold isprog_vars.
  simpl.
  rw @assert_sub_vars; simpl.
  split; intro h; repnd; dands; eauto 3 with slow.
  introv i; repndors; tcsp; subst; auto.
Qed.

Lemma hasvalue_subst_preserves_approx_ext {o} :
  forall lib x (t : @NTerm o) v u,
    isprog_vars [v] t (* wf_term t? *)
    -> hasvalue lib (subst t v u)
    -> approx_ext lib u x
    -> hasvalue lib (subst t v x).
Proof.
  introv pt hv ap.
  applydup @approx_ext_relates_only_progs in ap as p.
  destruct p as [pu px].

  nterm_ind t as [z|f ind|op bs ind] Case; auto.

  - Case "vterm".
    allrw @isprog_vars_vterm; allsimpl; repndors; tcsp; subst.
    unfsubst; unfsubst in hv; allsimpl; boolvar.
    apply hasvalue_approx_ext with (t := u); sp.

  - Case "oterm".
    allunfold @subst; allsimpl.
Abort.

(* Corollary of hasvalue_subst_preserves_approx_ext *)
Lemma hasvalue_subst_preserves_computation {p} :
  forall lib x t v u,
    isprogram t
    -> @isprog_vars p [v] u
    -> hasvalue lib (subst u v x)
    -> computes_to_value lib t x
    -> hasvalue lib (subst u v t).
Proof.
  sp.
  apply computes_to_value_implies_approx_ext in X1; sp.
(*  apply hasvalue_subst_preserves_approx_ext with (u := x); sp.*)
Abort.



(* end hide *)

Theorem alpha_implies_approx_ext2 {p} : forall lib nt1 nt2,
  @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> approx_ext lib nt1 nt2.
Proof.
  introv H2isp Hal.
  apply (approx_ext_alpha_rw_l _ _ _ _ Hal).
  apply approx_ext_refl; auto.
Qed.

(* begin hide *)
Theorem alpha_implies_approx_ext3 {p} : forall lib nt1 nt2,
  @isprogram p nt1
  -> alpha_eq nt1 nt2
  -> approx_ext lib nt1 nt2.
Proof.
  introv H2isp Hal. apply alpha_eq_sym in Hal.
  apply (approx_ext_alpha_rw_r _ _ _ _ Hal).
  apply approx_ext_refl; auto.
Qed.

Theorem alpha_implies_approx_ext {p} : forall lib nt1 nt2,
  isprogram nt1
  -> @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> approx_ext lib nt1 nt2.
Proof.
  intros. apply alpha_implies_approx_ext2; auto.
Qed.

Hint Resolve approx_ext_trans alpha_eq_sym alpha_implies_approx_ext: slow.



Lemma not_axiom_approx_ext_bot {pp} :
  forall lib, !@approx_ext pp lib mk_axiom mk_bot.
Proof.
  introv ap.
  inversion ap as [cc]; subst.
  unfold close_compute_ext in cc; repnd.
  generalize (cc2 NAxiom [] (trivial_ne_bar lib)); intro h.
  dest_imp h hyp; sp.
  { apply computes_to_value_bar_isvalue_refl; sp. }
  inversion p; allsimpl; cpx.
  pose proof (p0 lib) as q; autodimp q hyp; allsimpl; eauto 3 with slow.
  pose proof (q lib) as q; allsimpl; autodimp q hyp; eauto 3 with slow.
  unfold computes_to_value_alpha, computes_to_value in q; exrepnd.
  allfold @mk_axiom.
  apply not_bot_reduces_to_value in q2; sp.
Qed.

Lemma not_axiom_approxc_ext_bot {p} :
  forall lib, !@approxc_ext p lib mkc_axiom mkc_bot.
Proof.
  unfold approxc_ext, mkc_axiom, mkc_bot; simpl.
  apply not_axiom_approx_ext_bot.
Qed.

Hint Resolve approx_ext_open_relates_only_wf : slow.

Lemma approxbt_btwf {p} :
  forall lib,
    le_bin_rel
      (approx_ext_open_bterm lib)
      (fun b1 b2 => @bt_wf p b1 # bt_wf b2).
Proof.
  introv Hapb.
  repnud Hapb.
  repnud Hapb.
  exrepnd.
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb2)).
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb0)).
  rw @bt_wf_iff.
  rw @bt_wf_iff.

  eapply approx_ext_open_relates_only_wf; eauto.
Qed.



Lemma approxbt_fvars {p} :
  forall lib vsa vsb a b,
    approx_ext_open_bterm lib (bterm vsa a) (@bterm p vsb b)
    -> subset (free_vars a) vsa # subset (free_vars b) vsb.
Proof.
Abort. (** not true anymore? *)



Theorem approx_ext_implies_approx_ext_open {p} :
  forall lib t1 t2,
    @approx_ext p lib t1 t2
    -> approx_ext_open lib t1 t2.
Proof.
  introv Hap. applydup @approx_ext_relates_only_progs in Hap.
  repnd. unfold approx_ext_open, olift. dands; eauto 2 with slow.
  introv Hwf H1p H2p.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap1.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap0.
  rwg Hap0.
  rwg Hap1.
  trivial.
Qed.


Theorem approx_ext_open_approx_ext {p} :
  forall lib t1 t2,
    isprogram t1
    -> @isprogram p t2
    -> approx_ext_open lib t1 t2
    -> approx_ext lib t1 t2.
Proof.
  introv H1pr H2pr Hol.
  invertsna Hol Hol.
  exrepnd.
  assert (@wf_sub p [])  as Hwf by (apply sub_range_sat_nil).
  apply Hol0 in Hwf;allrw @lsubst_nil; auto.
Qed.

Hint Resolve computes_to_value_isvalue_refl computes_to_value_isvalue_eq : slow.
Hint Constructors isvalue : slow.

Lemma lblift_as_combine {o} :
  forall R (bs1 bs2 : list (@BTerm o)),
    lblift R bs1 bs2
    <=> (length bs1 = length bs2
         # forall b1 b2 : BTerm,
             LIn (b1,b2) (combine bs1 bs2) -> blift R b1 b2).
Proof.
  introv.
  unfold lblift; split; intro k; repnd; dands; auto; introv i.

  - allunfold @selectbt.
    apply (in_nth_combine_iff _ _ default_bt default_bt) in i.
    exrepnd; subst.
    apply k; auto.

  - allunfold @selectbt.
    pose proof (in_nth_combine _ _ bs1 bs2 n default_bt default_bt) as q.
    repeat (autodimp q hyp).
Qed.

Lemma combine_three :
  forall {A} (a b : A) l l1 l2,
    length l1 = length l
    -> length l2 = length l
    -> LIn (a, b) (combine l1 l2)
    -> {c : A & LIn (a,c) (combine l1 l) # LIn (b,c) (combine l2 l)}.
Proof.
  induction l; introv eqlen1 eqlen2 i; simpl in *; cpx;[].
  destruct l1; simpl in *; ginv; cpx.
  destruct l2; simpl in *; ginv; cpx.
  repndors; tcsp; ginv.

  - exists a0; dands; auto.

  - applydup IHl in i; auto.
    exrepnd.
    exists c; dands; auto.
Qed.

Lemma alpha_eq_bterms_preserves_lblift_approx_ext_right {o} :
  forall lib (bs : list (@BTerm o)) bs1 bs2,
    alpha_eq_bterms bs1 bs2
    -> lblift (approx_ext_open lib) bs bs2
    -> lblift (approx_ext_open lib) bs bs1.
Proof.
  introv aeq lbl.
  allrw @lblift_as_combine.
  unfold alpha_eq_bterms in *.
  repnd.
  dands; auto; try congruence.
  introv i.
  applydup (combine_three b1 b2 bs2) in i; auto.
  exrepnd.
  applydup aeq in i1.
  applydup lbl in i0.
  eapply respects_blift_alphabt;[|eauto].
  apply alpha_eq_bterm_sym; auto.
Qed.
Hint Resolve alpha_eq_bterms_preserves_lblift_approx_ext_right : slow.

Lemma alpha_eq_bterms_preserves_lblift_approx_ext_left {o} :
  forall lib (bs : list (@BTerm o)) bs1 bs2,
    alpha_eq_bterms bs1 bs2
    -> lblift (approx_ext_open lib) bs2 bs
    -> lblift (approx_ext_open lib) bs1 bs.
Proof.
  introv aeq lbl.
  allrw @lblift_as_combine.
  unfold alpha_eq_bterms in *.
  repnd.
  dands; auto; try congruence.
  introv i.
  applydup (combine_three b1 b2 bs2) in i; auto.
  exrepnd.
  applydup aeq in i0.
  apply in_combine_swap in i1; auto;[].
  applydup lbl in i1.
  eapply blift_alpha_fun_l;[eauto|].
  apply alpha_eq_bterm_sym; auto.
Qed.
Hint Resolve alpha_eq_bterms_preserves_lblift_approx_ext_left : slow.

Lemma approx_ext_canonical_form2 {p} :
  forall lib op bterms1 bterms2,
    approx_ext lib (oterm (@Can p op) bterms1) (oterm (Can op) bterms2)
    -> lblift (approx_ext_open lib) bterms1 bterms2.
Proof.
  introv Hap. applydup @approx_ext_relates_only_progs in Hap. repnd.
  eapply approx_ext_canonical_form in Hap; exrepnd; eauto with slow.
  apply computes_to_value_alpha_isvalue_alpha_eq in Hap3; eauto 3 with slow;[].
  apply alpha_eq_oterm_combine in Hap3.
  fold (alpha_eq_bterms bterms2 bterms') in Hap3; eauto 3 with slow.
Qed.

Lemma clearbot_relbt2 {p} : forall lib (l1bt l2bt : list (@BTerm p)),
  lblift (olift (approx_ext lib)) l1bt l2bt
  ->lblift (olift (approx_ext_aux lib bot2 \2/ bot2)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_approx_ext.
Qed.



Ltac alpharelbtd :=

  match goal with 
  | [H: 1 = length _ |- _ ] => symmetry in H; apply length1 in H; exrepnd; subst
  | [H: 2 = length _ |- _ ] => symmetry in H; apply length2 in H; exrepnd; subst
  | [H: 0 = length _ |- _ ] => symmetry in H; apply length0 in H; subst
  | [H: _ = S (length _) |- _ ] =>  inverts H as H
  | [H: (forall _:nat, (_< ?m) -> blift _ _ _)  |- _ ] => 
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps); clear H
  | [H: alpha_eq_bterm (bterm [] _) (bterm _ _) |- _] => apply alphaeqbt_nilv3 in H; exrepnd; subst
  | [H: alpha_eq_bterm _ (bterm [] _) |- _] => apply alpha_eq_bterm_sym in H
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H : blift _ _ _ |- _ ] => unfold blift in H; exrepnd
  end.

(*
  | [H: alpha_eq_bterm (bterm [] _) _ |- _] => apply alphaeqbt_nilv in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_] _) _ |- _] => apply alphaeqbt_1v in H; exrepnd; subst
  | [H: alpha_eq_bterm (bterm [_,_] _) _ |- _] => apply alphaeqbt_2v in H; exrepnd; subst
*)

Ltac dest_bterms :=
  repeat match goal with
  [ b : BTerm |- _] => destruct b
  end.

Lemma blift_approx_ext_open_nobnd {p} :
  forall lib nt1 nt2,
    blift (approx_ext_open lib) (nobnd nt1) (@nobnd p nt2)
    -> isprogram nt1
    -> isprogram nt2
    -> approx_ext lib nt1 nt2.
Proof.
  introv Hrel H1pr H2pr.
  unfold blift in Hrel. exrepnd.
  apply alphaeqbt_nilv3 in Hrel0; exrepnd; subst.
  apply alphaeqbt_nilv3 in Hrel2; exrepnd; subst. GC.
  apply approx_ext_open_approx_ext;  eauto 2 with slow.
  unfold approx_ext_open.
  rwg Hrel2.
  rwg Hrel0.
  trivial.
Qed.


Lemma blift_approx_ext_open_nobnd2 {p} :
  forall lib nt1 nt2,
    isprogram nt1
    -> @isprogram p nt2
    -> approx_ext lib nt1 nt2
    -> blift (approx_ext_open lib) (nobnd nt1) (nobnd nt2).
Proof.
  introv Hap H1pr H2pr.
  unfold blift. exists ([]: list NVar) nt1 nt2.
  dands; try (apply alphaeqbt_refl);[].
  apply approx_ext_implies_approx_ext_open; sp.
Qed.

Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.




Ltac prove_program :=
  allunfold isprogram; repnd; try(split;sp;fail);
 (
  match goal with
  | [ |- isprogram ?t] =>
    match goal with
    | [ H: approx_ext t ?t2 |- _] => apply approx_ext_relates_only_progs in H; repnd;sp
    | [ H: approx_ext ?t2 t |- _ ] => apply approx_ext_relates_only_progs in H; repnd;sp
    end
  end
  ).

Ltac alpha_to_approx_ext :=
(repeat match goal with
| [ H: (alpha_eq _ _) |- _ ] => 
  let Hs := fresh "Hsym" in
  pose proof (alpha_eq_sym _ _ H) as Hs;
  apply alpha_implies_approx_ext in H; try(prove_program);sp;
  apply alpha_implies_approx_ext in Hs; try(prove_program);sp; apply hide_hyp in H
end); allrw <- hide_hyp.

Ltac all_destruct_ands := repnd; dands.

(* end hide *)
(**  % \noindent \\*% Given [approx_trans], now have to prove
    that [approx_open] is transitive. It turned out that
    our proof of that worked exactly for the following stronger version below.

    The proof is not as trivial as suggested by
    Howe %\cite{Howe:1989}% and illustrates a very common pattern where
    seemingly trivial paper proofs take quite a lot of effort because
    the concrete proof requires delicate reasoning about details
    of Substitution. We will describe some of these complications
    below. The proof begins by introducing the hypothesis and 
    destructing all conjunctions to take care of the [nt_wf] parts
    of [approx_open]. (Recall that [approx_open] is a notation for [olift approx]).
    Then we introduce the additional hypothesis
    [Hwfs], [Hispa] and [Hispc]*)

Lemma olift_trans {p} :
  forall R,
    trans_rel R
    -> respects_alpha R 
    -> trans_rel (@olift p R).
(* begin show *)
Proof. (* exactly same as the last part of approx_trans *)
  intros R Ht Hra a b c Hab Hbc. allunfold @olift. all_destruct_ands; auto.
  clear Hbc0 Hbc1 Hab0. intros sub Hwfs Hispa Hispc.
(* end show *)
(** % \noindent \\*% At this point, we have the following proof state:

[[
1 subgoals
R : bin_rel NTerm
Ht : trans_rel R
Hra : respects_alpha R
a : NTerm
b : NTerm
c : NTerm
Hab1 : nt_wf b
Hab : forall sub : Substitution,
      wf_sub sub ->
      isprogram (lsubst a sub) ->
      isprogram (lsubst b sub) -> R (lsubst a sub) (lsubst b sub)
Hbc : forall sub : Substitution,
      wf_sub sub ->
      isprogram (lsubst b sub) ->
      isprogram (lsubst c sub) -> R (lsubst b sub) (lsubst c sub)
sub : Substitution
Hwfs : wf_sub sub
Hispa : isprogram (lsubst a sub)
Hispc : isprogram (lsubst c sub)
______________________________________(1/1)
R (lsubst a sub) (lsubst c sub)
]]

  We cannot just instantiate [Hab] and [Hbc] with [sub] because there is no
  reason why [(lsubst b sub)] would be a closed term.
  [b] might have free variables that are disjoint from the ones of [a] and [c].
  From [Hispa] and [Hispc], we can only conclude that the terms that
  [sub] substitutes for free variables of [a] and [c] are closed.
  But it might contain substitutions of 
  non-closed terms for variables not free in [a] or [c].


  So, we first filter [sub] to keep only the first pair
  that applies to a free variable of either [a] or [c].
  Let that [Substitution] be [subf].
  We then prove that the range of [subf] consists
  of only closed terms (because of [Hispa] and [Hispc]).
  
  Let [subb] be a substitution that substitutes some(arbitrary) closed terms for
  the free variables of [b].
  We then prove that [(lsubst b (subf ++ subb))] is closed and that
  [(lsubst a (subf ++ subb))] and [(lsubst c (subf ++ subb))] are 
  alpha equal to [(lsubst a sub)] and [(lsubst c sub)] respectively.
  The latter is implied by the definition of [lsubst_aux]
  because it uses the first pair in the [Substitution]
  that matches a variable.
  Then, we can instantiate [Hab] and [Hbc] with [(sub:=subf ++ subb)]
  and do some rewriting using alpha equality to finish the proof. %\\*%
*)
  pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
  pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
  allsimpl. repnd. rename Xtrim into Xtrima.
  rename Xtrim0 into Xtrimc.


  revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
  introv Hispa Hispc.
  
  rwg Xtrima.
  rwg Xtrimc.
    
  remember (sub_keep_first sub (free_vars c ++ free_vars a)) as subt.
  remember (@subst_axiom p (free_vars b)) as subb.
  remember (subt++subb) as sub'.
  assert (prog_sub subb) as Hsubb by (subst;auto).

  pose proof (prog_lsubst_app2 a subt subb Hispa Hsubb) as Heqa.
  pose proof (prog_lsubst_app2 c subt subb Hispc Hsubb) as Heqc.
  revert Hispa Hispc.
  rw Heqa. rw Heqc.
  introv Hispa Hispc.
  assert(isprogram (lsubst b (subt++subb))).
  - apply isprogram_lsubst; eauto. apply sub_app_sat; auto.
    introv Hin. apply in_map_iff. exists (v, @mk_axiom p). split; auto.
    apply in_app_iff. right. subst.
    unfold subst_axiom. apply in_map_iff. eexists;eauto.
  - repnud Ht. apply Ht with (y:=(lsubst b (subt++subb))); eauto.  
    apply Hab; eauto; apply sub_app_sat; apply prog_sub_implies_wf in Hsubb;
           apply prog_sub_implies_wf in Xprog; subst; allunfold @wf_sub; eauto.
    apply Hbc; eauto; apply sub_app_sat; apply prog_sub_implies_wf in Hsubb;
           apply prog_sub_implies_wf in Xprog; subst; allunfold @wf_sub; eauto.
Qed.

(* begin show *)
Corollary approx_ext_open_trans {p} :
  forall lib (a b c : @NTerm p),
    approx_ext_open lib a b
    -> approx_ext_open lib b c
    -> approx_ext_open lib a c.
Proof.
  intro lib.
  apply olift_trans; revert lib.
  - exact approx_ext_trans.
  - exact respects_alpha_approx_ext.
Qed.
Hint Resolve approx_ext_open_trans: slow.
(* end show *)

(* begin hide *)

Definition simpl_olift {p} R (t1 t2: @NTerm p) :=
  nt_wf t1
  # nt_wf t2
  # forall sub,
      prog_sub sub
      -> isprogram (lsubst t1 sub)
      -> isprogram (lsubst t2 sub)
      -> R (lsubst t1 sub) (lsubst t2 sub).

Definition simpl_close_compute_ext {p} lib (R : NTerm -> NTerm -> Type) (tl tr : NTerm) : Type  :=
  isprogram tl
  # isprogram tr
  # (* need to prove that all terms related by sqlen are programs *)
  forall (c : CanonicalOp) (tl_subterms : list BTerm),
    computes_to_value lib tl (oterm (Can c) tl_subterms)
    -> { tr_subterms : list BTerm &
         computes_to_value lib tr (oterm (Can c) tr_subterms)
         # @lblift p (simpl_olift R) tl_subterms tr_subterms }.


CoInductive simpl_approx_ext_aux {p} lib (R : bin_rel NTerm) (tl tr : @NTerm p) : [univ] :=
| simpl_approx_ext_fold :
    simpl_close_compute_ext lib (approx_ext_aux lib R \2/ R) tl tr
    -> simpl_approx_ext_aux lib R tl tr.


Lemma approx_ext_open_simpler_equiv {p} :
  forall lib a c,
    simpl_olift (@approx_ext p lib) a c <=> approx_ext_open lib a c.
Proof.
  introv.
  split.

  - intro Hos. repnud Hos.
    unfold approx_ext_open, olift.
    dands;auto.
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.
    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    apply (approx_ext_alpha_rw_l _ _ _ _ Xtrima).
    apply (approx_ext_alpha_rw_r _ _ _ _ Xtrimc).
    apply Hos; auto.

  - intro Hos.
    repnud Hos.
    unfold olift in Hos; unfold simpl_olift; repnd; dands; auto.
    introv ps isp1 isp2.
    pose proof (Hos sub) as h.
    repeat (autodimp h hyp); eauto with slow.
Qed.

(*
Lemma simpl_approxr_implies : forall r a c,
  simpl_approx_ext_aux r a c
  -> approx_ext_aux r a c.
Proof.
  intro r. 
  pose proof 
  (approx_acc (fun a c => { b,a',c' : NTerm $
       alpha_eq a a' # alpha_eq c c' # simpl_approx_ext_aux r a' c'  })
     r) as HH.
  allsimpl.
  match goal with 
  [ HH : _ -> ?B |- _ ] => assert B; [|
    intros; eapply X; eexists; eexists; eexists; eauto;fail]
  end.
*)

Ltac wfp :=
(repeat match goal with
| [ H: (isprogram _) |- _ ] => unfold isprogram in H; exrepnd
| [ H: (closed _) |- _ ] => progress(rewrite H)
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) (bound_vars _)) ] =>
      apply disjoint_sub_as_flat_map

end); try (
match goal with
| [ |- isprogram _] => split end);try trivial.


Tactic Notation "wfpc" :=
  try(wfp;fail).



Theorem alpha_implies_approx_ext_open {p} : forall lib nt1 nt2,
  @nt_wf p nt1
  -> alpha_eq nt1 nt2
  -> approx_ext_open lib nt1 nt2.
Proof.
  introv H1wf  Hal. repeat(split;[sp|]).
  alpha_hyps Hal;sp.
  introv Hpr H1pr H2pr.
  apply alpha_implies_approx_ext; sp.
  apply lsubst_alpha_congr2;sp.
Qed.

Hint Resolve alpha_implies_approx_ext_open : slowbad.

Hint Resolve approx_ext_open_relates_only_wf
  approx_ext_open_trans approx_ext_open_refl: slow.


Lemma approx_ext_open_alpha_rw_l {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_ext_open lib a b <=> approx_ext_open lib a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold approx_ext_open.
  split; introv Hyp;
  applydup @approx_ext_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma approx_ext_open_alpha_rw_r {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_ext_open lib b a <=> approx_ext_open lib b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold approx_ext_open.
  split; introv Hyp; 
  applydup @approx_ext_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0; 
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma approx_ext_open_alpha_rw_lr {p} : forall lib a b a' b',
  alpha_eq a a'
  -> @alpha_eq p b b'
  -> (approx_ext_open lib a b <=> approx_ext_open lib a' b').
Proof.
  introv Hala Halb.
  eapply @approx_ext_open_alpha_rw_l with (b:=b) in Hala.
  eapply @approx_ext_open_alpha_rw_r with (b:=a') in Halb.
  dtiffs.
  split; eauto.
Qed.

Ltac prove_wf1 :=
  sp;
 (
  match goal with
  | [ |- nt_wf ?t] =>
    match goal with
    | [ H: approx_ext_open t ?t2 |- _] => apply approx_ext_open_relates_only_wf in H; repnd;sp
    | [ H: approx_ext_open ?t2 t |- _ ] => apply approx_ext_open_relates_only_wf in H; repnd;sp
    end
  end
  ).

Hint Resolve approx_ext_open_trans : approx_ext_open_trans.


(* end hide *)

Hint Resolve isprogram_fix  isprogram_apply : slow.



Lemma approx_ext_open_lsubst_congr {p} : forall lib ta tb sub,
  @wf_sub p sub
  -> approx_ext_open lib ta tb
  -> approx_ext_open lib (lsubst ta sub) (lsubst tb sub).
Proof.
  introv Hwf Hap.
  applydup @approx_ext_open_relates_only_wf in Hap.
  repeat(split; [apply lsubst_wf_iff;sp;fail|]).
  intros subo Hwfs H1ps H2pr.
  unfold approx_ext_open in Hap.
  repnud Hap.
  pose proof (combine_sub_nest_wspec sub subo) as Hsub.
  repeat(dest_imp Hsub HH).
  exrepnd.
  pose proof (Hsub0 ta) as Hala. alpha_hyps Hala.
  pose proof (Hsub0 tb) as Halb. alpha_hyps Halb.
  pose proof (Hap sub3) as XX.
  repeat(dest_imp XX HH).
  rwg Hala.
  rwg Halb.
  trivial.
Qed.

(**  % \noindent \\*% We wish to prove that approx_ext is a congruence. However,
    it is a fairly non-trivial task and the main content of %\cite{Howe:1989}%.
    For now, the following lemmma
    asserts that approx_ext is a congruence w.r.t canonical [Opid]s.
    The general proof of congruence is discussed in the next subsection.
    *)

Lemma can_doesnt_raise_an_exception_bar {p} :
  forall {lib} (bar : NeBarLib lib) a c bterms (e : @NTerm p),
    computes_to_exception_bar bar a (oterm (Can c) bterms) e -> False.
Proof.
  introv ce.
  apply computes_to_exception_bar_implies_computes_to_exception_alpha in ce.
  exrepnd.
  unfold computes_to_exception_alpha in ce0; exrepnd.
  apply can_doesnt_raise_an_exception in ce1; auto.
Qed.

Lemma can_doesnt_compute_to_seq_bar {o} :
  forall {lib} (bar : NeBarLib lib) c (bterms : list (@BTerm o)) f,
    computes_to_seq_bar bar (oterm (Can c) bterms) f -> False.
Proof.
  introv comp.
  apply computes_to_seq_bar_implies_computes_to_seq_alpha in comp.
  exrepnd.
  unfold computes_to_seq_alpha in comp0; exrepnd.
  apply reduces_to_if_isvalue_like in comp0; eauto 3 with slow; ginv.
Qed.

Lemma approx_ext_canonical_form3 {p} :
  forall lib op bterms1 bterms2,
    isprogram (oterm (@Can p op) bterms1)
    -> isprogram (oterm (Can op) bterms2)
    -> lblift (approx_ext_open lib) bterms1 bterms2
    -> approx_ext lib (oterm (Can op) bterms1) (oterm (Can op) bterms2).
Proof.
  introv H1p H2p Hap. constructor. unfold close_compute_ext.
  dands; eauto; introv comp.

  - apply computes_to_value_bar_isvalue_alpha_eq in comp; eauto 3 with slow;[].
    apply alpha_eq_oterm_combine2 in comp.
    fold (alpha_eq_bterms bterms1 tl_subterms) in comp.
    repnd; ginv.
    exists bterms2; dands; eauto 3 with slow;[].
    apply clearbot_relbt2; eauto 3 with slow.
    eapply alpha_eq_bterms_preserves_lblift_approx_ext_left;[|eauto].
    apply alpha_eq_bterms_sym; auto.

  - apply can_doesnt_raise_an_exception_bar in comp; tcsp.

  - apply can_doesnt_compute_to_seq_bar in comp; tcsp.
Qed.

Lemma computes_to_value_bar_exception {p} :
  forall {lib} (bar : NeBarLib lib) a (e v : @NTerm p),
    computes_to_value_bar bar (mk_exception a e) v
    -> False.
Proof.
  introv comp.
  apply computes_to_value_bar_implies_computes_to_value_alpha in comp; exrepnd.
  unfold computes_to_value_alpha in comp0; exrepnd.
  apply computes_to_value_exception in comp0; auto.
Qed.

Lemma computes_to_exception_bar_refl {p} :
  forall {lib} (bar : BarLib lib) a (e : @NTerm p),
    computes_to_exception_bar bar a (mk_exception a e) e.
Proof.
  introv ext ext'.
  exists a e; dands; auto.
  apply computes_to_exception_refl.
Qed.
Hint Resolve computes_to_exception_bar_refl : slow.

Lemma computes_to_exception_bar_exception {p} :
  forall {lib} (bar : NeBarLib lib) a b (e v : @NTerm p),
    computes_to_exception_bar bar a (mk_exception b e) v
    -> alpha_eq v e # alpha_eq a b.
Proof.
  introv comp.
  apply computes_to_exception_bar_implies_computes_to_exception_alpha in comp; exrepnd.
  unfold computes_to_exception_alpha in comp0; exrepnd.
  apply computes_to_exception_exception in comp1; repnd; subst; tcsp.
Qed.

Lemma computes_to_seq_bar_exception {p} :
  forall {lib} (bar : NeBarLib lib) (a b : @NTerm p) f,
    computes_to_seq_bar bar (mk_exception a b) f
    -> False.
Proof.
  introv comp.
  apply computes_to_seq_bar_implies_computes_to_seq_alpha in comp; exrepnd.
  unfold computes_to_seq_alpha in comp0; exrepnd.
  apply reduces_to_exception in comp0; ginv; eauto 3 with slow.
Qed.

Lemma approx_ext_canonical_form_exc {o} :
  forall lib a1 a2 (e1 e2 : @NTerm o),
    approx_ext lib a1 a2
    -> approx_ext lib e1 e2
    -> approx_ext lib (mk_exception a1 e1) (mk_exception a2 e2).
Proof.
  introv ap1 ap2.
  applydup @approx_ext_relates_only_progs in ap1; repnd.
  applydup @approx_ext_relates_only_progs in ap2; repnd.
  constructor.
  unfold close_compute_ext.
  dands; eauto; try (rw @isprogram_exception_iff; tcsp); introv comp.

  - apply computes_to_value_bar_exception in comp; tcsp.

  - apply computes_to_exception_bar_exception in comp; repnd.
    exists a2 e2; dands; eauto 3 with slow;
      left; eauto 3 with slow; eapply approx_ext_alpha_rw_l_aux;
        try (exact ap1); try (exact ap2); apply alpha_eq_sym; auto.

  - apply computes_to_seq_bar_exception in comp; tcsp.
Qed.


(* begin hide *)

Lemma approx_ext_decomp_approx_ext {p} :
  forall lib a b c d,
    approx_ext lib (mk_approx a b) (@mk_approx p c d)
    <=> approx_ext lib a c # approx_ext lib b d.
Proof.
  split; unfold mk_approx; introv Hyp.
  - applydup @approx_ext_relates_only_progs in Hyp. repnd.
    apply  approx_ext_canonical_form2 in Hyp.
    unfold lblift in Hyp. repnd. allsimpl.
    alpharelbtd. GC.
    eapply blift_approx_ext_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_ext_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd. applydup @approx_ext_relates_only_progs in Hyp. repnd.
    applydup @approx_ext_relates_only_progs in Hyp0. repnd.
    apply approx_ext_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_ext_open_nobnd2; sp.
Qed.

Lemma approxbt_lsubst_prog {p} :
  forall lib lv1 lv2 t1 t2,
    isprogram_bt (bterm lv1 t1)
    -> isprogram_bt (bterm lv2 t2)
    -> approx_ext_open_bterm lib (bterm lv1 t1) (bterm lv2 t2)
    -> forall lnt,
       length lnt= length lv1
       -> (forall t, LIn t lnt -> @isprogram p t)
       ->  approx_ext lib (lsubst t1 (combine lv1 lnt)) (lsubst t2 (combine lv2 lnt)).
Proof.
  introv H1p H2p Ha0 Hlen Hlp.
  applydup @blift_numbvars in Ha0.
  unfold num_bvars in Ha1; simpl in Ha1.
  unfold approx_ext_open_bterm in Ha0.
  repnud Ha0. exrepnd.
  dimp (isprogram_bt_implies2 _ H1p _ Hlp); allunfold @num_bvars;
     allsimpl; [omega|].
  dimp (isprogram_bt_implies2 _ H2p _ Hlp); allunfold @num_bvars;
     allsimpl; [omega|].
  allunfold @apply_bterm. allsimpl.
  pose proof (fresh_vars (length lv1) (all_vars nt1 ++ all_vars nt2
               ++ all_vars t1 ++ all_vars t2)).
  exrepnd.
  apply @alphabt_change_var with (lv:=lvn) in Ha2; spc;[| disjoint_reasoningv];[].
  apply @alphabt_change_var with (lv:=lvn) in Ha3; spc;[| disjoint_reasoningv];[].
  apply approx_ext_open_lsubst with (lvi:=lv) (lvo:=lvn) in Ha0.
  apply alpha_eq_sym in Ha5.
  apply alpha_eq_sym in Ha4.
  unfold approx_ext_open in Ha0.
  rwhg Ha5 Ha0.
  rwhg Ha4 Ha0.

  assert (approx_ext_open lib
    (lsubst t1 (var_ren lv1 lvn)) (lsubst t2 (var_ren lv2 lvn)))
   as XX by auto. (** alpha replacement *)
  unfold approx_ext_open in XX.
  repnud XX.
  pose proof (XX (combine lvn lnt)) as XXX.
  clear XX.
  pose proof flat_map_progs _ Hlp as Hfl.
  rw @lsubst_nest_same in XXX;spc; disjoint_reasoningv;
    [ | rw Hfl; disjoint_reasoning; fail].
  rw @lsubst_nest_same in XXX;spc; disjoint_reasoningv;
    [ | rw Hfl; disjoint_reasoning; fail].
  apply XXX;sp.
  introv Hin.
  eauto 4 with slow.
Qed.

Ltac decomp_progh3 :=
  match goal with
    | [ H1 : (computes_to_value ?lib ?tl _), H2 : (isprogram  ?t1) |- _ ] =>
      let Hf := fresh H1 H2 "pr" in
      pose proof (preserve_program lib _ _ H1 H2) as Hf;
        hide_hyp  H1
    | [ H1 : (compute_at_most_k_steps ?lib _ ?tl = csuccess _), H2 : (isprogram  ?t1) |- _ ] =>
      let Hf := fresh H1 H2 "pr" in
      pose proof (computek_preserves_program lib _ _ _ H1 H2) as Hf;
        hide_hyp  H1
    | [ H : isprogram (oterm _ _) |- _ ] =>
      let Hf := fresh H "bts" in
      pose proof (isprogram_ot_implies_eauto2 _ _ H) as Hf;
        simpl in Hf;
        allrw map_length;
        hide_hyp H
    | [ H: (forall _:nat, (_< ?m) -> isprogram_bt _)  |- _ ] =>
      let Hf := fresh H "fbt" in
      dforall_lt_hyp  Hf;
        allunfold selectbt;
        allsimpl
    | [ H : isprogram_bt (bterm [] ?lbt) |- _ ] =>
      apply isprogram_bt_nobnd in H
end.

Ltac unfold_computes_to_alpha :=
  match goal with
  | [ H : computes_to_value_alpha _ _ _ |- _ ] =>
    unfold computes_to_value_alpha in H; exrepnd
  end.

Lemma decomp_forall_or :
  forall {A} (a b : A) F G,
    (forall x y, (a, b) = (x, y) [+] F x y -> G x y)
    -> G a b # (forall x y, F x y -> G x y).
Proof.
  introv h; tcsp.
Qed.

Ltac decomp_alpha_eq :=
  match goal with
  | [ H : alpha_eq (oterm ?op1 ?bs1) (oterm ?op2 ?bs2) |- _ ] =>
    let h := fresh H in
    apply alpha_eq_oterm_combine2 in H;
    destruct H as [H h]
  | [ H : alpha_eq (oterm ?op ?bs) _ |- _ ] =>
    apply alpha_eq_oterm_implies_combine in H; exrepnd; subst; simpl in *
  | [ H : 3 = length ?x |- _ ] =>
    destruct x; simpl in *;
    try (complete (inversion H));
    try (apply eq_add_S in H)
  | [ H : 2 = length ?x |- _ ] =>
    destruct x; simpl in *;
    try (complete (inversion H));
    try (apply eq_add_S in H)
  | [ H : 1 = length ?x |- _ ] =>
    destruct x; simpl in *;
    try (complete (inversion H));
    try (apply eq_add_S in H)
  | [ H : 0 = length ?x |- _ ] =>
    destruct x; simpl in *;
    try (complete (inversion H));
    try (apply eq_add_S in H)
  | [ H : ?x = ?x |- _ ] => clear H
  | [ H : forall _ _, _ |- _ ] => apply decomp_forall_or in H; repnd
  | [ H : forall _ _, False -> _ |- _ ] => clear H
  | [ H : alpha_eq_bterm (bterm [] _) _ |- _ ] => apply alphaeqbt_nilv in H; exrepnd; subst
  end.

Hint Resolve approx_ext_open_alpha_rw_l_aux : approx_alpha.
Hint Resolve approx_ext_open_alpha_rw_r_aux : approx_alpha.

(* based on prove_cequiv_mk from cequiv.v *)
Ltac prove_approx_mk :=
  let Hcomp   := fresh "Hcomp" in
  let Hcomp0  := fresh "Hcomp0" in
  let Hcomp1  := fresh "Hcomp1" in
  let Hcomp2  := fresh "Hcomp2" in
  let Hcomp3  := fresh "Hcomp3" in
  let bterms' := fresh "bterms'" in
  let Hceq    := fresh "Hceq" in
  let bt      := fresh "bt" in
  let Hbt     := fresh "Hbt" in
  introv Hcomp Hceq;
    applydup @approx_ext_relates_only_progs in Hceq; repnd;
    applydup @preserve_program in Hcomp as Hcomp0; auto;
    eapply @approx_ext_canonical_form in Hcomp; eauto;
    destruct Hcomp as [bterms' Hcomp];
    destruct Hcomp as [Hcomp1 Hcomp2];
    applydup @computes_to_value_alpha_preserves_isprogram in Hcomp1 as Hcomp3; auto;
    unfold_all_mk;
    match goal with
        [H : lblift _ _ ?bterms'  |- _ ] =>
        unfold lblift in H; simpl in H;
        let Hlen := fresh H "len" in
        destruct H as [Hlen H];
          dlist_len_name bterms' bt
    end;
    dforall_lt_hyp Hbt;
    allunfold @selectbt; allsimpl;
    destruct_bterms;
    blift_nums;
    allunfold @num_bvars; allsimpl;
    dlists_len;
    unfold_all_mk;
    repeat(decomp_progh3);
    remove_relbt_samevar;
    repeat unfold_computes_to_alpha;
    repeat decomp_alpha_eq;
    rep_eexists; dands; eauto;
    apply @approx_ext_open_approx_ext;
    eauto 2 with slow;
    eauto 4 with approx_alpha.

(* end hide *)
Lemma approx_ext_mk_pair {p} :
  forall lib (t t' a b : NTerm),
    computes_to_value lib t (mk_pair a b)
    -> approx_ext lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_pair a' b')
         # approx_ext lib a a'
         # approx_ext lib b b'}.
Proof.
  prove_approx_mk.
Qed.

(* begin hide *)


(*
Lemma approx_open_canonical_form :
  forall t t' op bterms,
    computes_to_value t (oterm (Can op) bterms)
    -> approx_open t t'
    -> exists bterms',
         computes_to_value t' (oterm (Can op) bterms')
         # lblift approx_open bterms bterms'.
Proof.
  intros ? ? ? ? Hcomp Hap.
  invertsn Hap.
  repd.
  generalize (H0 (map (fun v => (v,mk_axiom)) (free_vars t ++ free_vars t'))); sp.

  dimp H1.

  unfold prog_sub; sp.
  rewrite in_map_iff in H2; sp.
  inversion H2; subst.
  apply isprogram_axiom.

  sp.
  dimp H1.
  apply isprogram_lsubst; sp.
  exists mk_axiom.
  rewrite in_map_iff.
  exists v; sp.
  rewrite in_app_iff; left; auto.

  inversion hyp0; subst.
  unfold close_compute_ext in H2; sp.

Qed.

Definition approxow (a b : WTerm) :=
  approx_open (get_wterm a) (get_wterm b).
*)


Lemma computes_to_exception_trivial_ne_bar_implies_computes_to_exception_alpha {o} :
  forall lib (a : @NTerm o) b c,
    a =b=e>(b,trivial_ne_bar lib) c
    -> a =a=e>(b,lib) c.
Proof.
  introv comp.
  pose proof (comp lib) as comp; simpl in comp; autodimp comp hyp; eauto 2 with slow.
Qed.
Hint Resolve computes_to_exception_trivial_ne_bar_implies_computes_to_exception_alpha : slow.

Hint Resolve approx_ext_alpha_rw_r_aux : approx_alpha.
Hint Resolve approx_ext_alpha_rw_l_aux : approx_alpha.

Lemma approx_ext_exception {p} :
  forall lib en (a b : @NTerm p),
    approx_ext lib (mk_exception en a) b
    -> {x : NTerm
        & {c : @NTerm p
        & computes_to_exception lib x b c
        # approx_ext lib en x
        # approx_ext lib a c}}.
Proof.
  introv ap.
  invertsn ap.
  unfold close_compute_ext in ap; repnd.
  pose proof (ap3 en a (trivial_ne_bar lib)) as k; autodimp k hyp; eauto 3 with slow;[].
  exrepnd.
  apply computes_to_exception_trivial_ne_bar_implies_computes_to_exception_alpha in k0.
  unfold computes_to_exception_alpha in k0; exrepnd.
  repndors; tcsp; try (complete (unfold bot2 in *; tcsp)).
  eexists; eexists; dands; eauto; eauto 2 with slow; eauto 3 with approx_alpha.
Qed.

(*
Lemma approx_mk_marker {o} :
  forall lib (t : @NTerm o) m,
    approx_ext lib (mk_marker m) t
    -> computes_to_marker lib t m.
Proof.
  introv ap.
  inversion ap as [c]; clear ap.
  unfold close_compute_ext in c; repnd.
  pose proof (c m) as h.
  autodimp h hyp.
  apply compute_to_marker_mrk.
Qed.

Lemma approx_mk_marker_iff {o} :
  forall lib (t : @NTerm o) m,
    isprogram t
    -> (approx_ext lib (mk_marker m) t
        <=> computes_to_marker lib t m).
Proof.
  introv isp; split; intro k.
  - apply approx_mk_marker; auto.
  - constructor.
    unfold close_comput; dands; tcsp.
    + apply isprogram_marker.
    + introv comp.
      unfold computes_to_value in comp; repnd.
      apply reduces_to_if_isvalue_like in comp0;[|right; right; sp].
      inversion comp0.
    + introv comp.
      unfold computes_to_exception in comp; repnd.
      apply reduces_to_if_isvalue_like in comp;[|right; right; sp].
      inversion comp.
    + introv comp.
      assert (@mk_marker o m0 = @mk_marker o m) as e;[|inversion e; subst; auto].
      apply (reduces_to_eq_val_like lib (mk_marker m)); auto.
      * apply reduces_to_symm.
      * right; right; sp.
      * right; right; sp.
Qed.
*)

(* end hide *)
