(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export bar_induction2.


Lemma well_founded_lt :
  well_founded lt.
Proof.
  introv.
  induction a.
  - constructor; introv h; omega.
  - inversion IHa as [imp].
    constructor; introv h.
    rewrite Nat.lt_succ_r in h.
    destruct h; auto.
    apply imp; omega.
Qed.

Definition brel (A : Type) := A -> A -> Prop.

(* R is > *)
Definition strong_wf {A} (R : brel A) :=
  forall (f : nat -> A),
  exists n,
    not (R (f n) (f (S n))).

Definition weak_wf {A} (R : brel A) :=
  forall (f : nat -> A),
  exists n,
    not (forall m, m <= n -> R (f m) (f (S m))).

Lemma strong_wf_implies_weak_wf :
  forall {A} (R : brel A), strong_wf R -> weak_wf R.
Proof.
  introv h; introv.
  pose proof (h f) as q; clear h; exrepnd.
  exists n.
  intro h.
  destruct q0; apply h; auto.
Qed.

Definition swap_brel {A} (R : brel A) : brel A :=
  fun a b => R b a.

Definition dec_brel {A} (R : brel A) : Type :=
  forall a b, {R a b} + {~R a b}.

Lemma well_founded_implies_not_strong_wf :
  forall {A} (R : brel A),
    well_founded R
    -> !{f : nat -> A | forall n, R (f (S n)) (f n)}.
Proof.
  introv h q; introv.
  unfold well_founded in h.
  exrepnd.

  pose proof (h (f 0)) as q; clear h.
  remember (f 0) as a.
  remember 0 as n.
  clear Heqn.
  revert dependent n.

  induction q as [? imp ind]; introv e; subst.
  apply (ind (f (S n)) (q0 n) (S n) eq_refl).
Qed.

Lemma well_founded_implies_strong_wf :
  forall {A} (R : brel A),
    well_founded R
    -> dec_brel R
    -> strong_wf (swap_brel R).
Proof.
  introv wf dec; introv.
  unfold well_founded in wf.
  unfold swap_brel.

  pose proof (wf (f 0)) as q; clear wf.
  remember (f 0) as a.
  remember 0 as n.
  clear Heqn.
  revert dependent n.
  induction q as [? imp ind]; introv e; subst.
  destruct (dec (f (S n)) (f n)) as [d|d].
  - apply (ind (f (S n)) d (S n) eq_refl).
  - exists n; auto.
Qed.

Lemma strong_wf_implies_well_founded :
  forall {A} (R : brel A), strong_wf R -> well_founded (swap_brel R).
Proof.
  introv h; introv.
  unfold strong_wf in h.
  constructor.

Abort.

Inductive almost_full {X} : (brel X) -> Prop :=
| AZ_ZT : forall (R : brel X), (forall x y, R x y) -> almost_full R
| AZ_SUP :
    forall R,
      (forall x, almost_full (fun y z => R y z \/ R x y))
      -> almost_full R.

Lemma af_inf_chain (X : Set) (R : brel X) :
  almost_full R
  ->
  forall (f : nat -> X),
  exists n, exists m,
      n > m /\ R (f m) (f n).
Proof.
  introv af.
  induction af as [? imp|? imp ind]; introv.
  - exists 1 0; dands; auto.
  - pose proof (ind (f 0) (fun x => f (S x))) as h.
    exrepnd; repndors; eauto.
    + exists (S n) (S m); dands; auto; try omega.
    + exists (S m) 0; dands; auto; try omega.
Qed.

Definition update_seq_from {o} (s : @CTerm o) (n m : nat) (v : NVar) :=
  mkc_lam
    v
    (mkcv_less
       [v]
       (mkc_var v)
       (mkcv_nat [v] n)
       (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
       (mkcv_nat [v] m)).

Lemma is_seq_update_seq_from {o} :
  forall lib (s : @CTerm o) n m v,
    is_kseq lib s n
    -> is_seq lib (update_seq_from s n m v).
Proof.
  introv isk.
  unfold is_kseq, eq_kseq in isk.
  unfold is_seq, update_seq_from, nat2nat.
  apply equality_in_fun; dands; eauto 3 with slow;[].

  introv en.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  repeat (rewrite mkcv_less_substc).
  repeat (rewrite mkcv_apply_substc).
  repeat (rewrite mkc_var_substc).
  repeat (rewrite mkcv_nat_substc).
  repeat (rewrite csubst_mk_cv).

  apply equality_in_tnat in en.
  unfold equality_of_nat in en; exrepnd; spcast.
  allapply @computes_to_valc_implies_cequivc.

  eapply equality_respects_cequivc_left;
    [apply cequivc_mkc_less;
      [apply cequivc_sym;eauto
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_mkc_less;
      [apply cequivc_sym;eauto
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_mkc_less_nat
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_mkc_less_nat
    |].
  boolvar.

  - eapply equality_natk2nat_implies in isk;[|eauto]; exrepnd.
    allapply @computes_to_valc_implies_cequivc.
    eapply equality_respects_cequivc_left;
      [apply implies_cequivc_apply;
        [apply cequivc_refl
        |apply cequivc_sym;eauto]
      |].
    eapply equality_respects_cequivc_right;
      [apply implies_cequivc_apply;
        [apply cequivc_refl
        |apply cequivc_sym;eauto]
      |].
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;eauto
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;eauto
      |].
    eauto 3 with slow.

  - eauto 3 with slow.
Qed.

Definition barred {o} lib (P : @CTerm o) :=
  forall s,
    is_seq lib s ->
    {n : nat & inhabited_type lib (mkc_apply2 P (mkc_nat n) s)}.

Definition KSeq {o lib} := {s : @CTerm o & {n : nat & is_kseq lib s n}}.

Definition lenKSeq {o lib} (s : @KSeq o lib) : nat := projT1 (projT2 s).

Definition Seq {o lib} := {s : @CTerm o & is_seq lib s}.

(* s2 is of length n (from 0 to n-1) and s1 of length n+1 (from 0 to n) *)
Definition lt_seq {o}
           lib P (b : barred lib P) (v : NVar)
           (ks1 ks2 : @KSeq o lib) : Prop :=
  match ks1, ks2 with
    | existT s1 (existT n1 i1), existT s2 (existT n2 i2) =>
      n1 = n2 + 1
      /\ (forall m,
            m < n2 ->
            ccequivc lib (mkc_apply s1 (mkc_nat m)) (mkc_apply s2 (mkc_nat m)))
      /\ match b (update_seq_from s1 n1 0 v)
                 (is_seq_update_seq_from lib s1 n1 0 v i1) with
           | existT m inh => m >= n1
         end
  end.

(* c extends d *)
Definition extends {o} {lib}
           (c d : @KSeq o lib) : Prop :=
  match c, d with
    | existT s1 (existT n1 i1), existT s2 (existT n2 i2) =>
      n1 > n2
      /\ (forall m,
            m < n2 ->
            ccequivc lib (mkc_apply s1 (mkc_nat m)) (mkc_apply s2 (mkc_nat m)))
  end.

Definition apPred {o} {lib} (P : @CTerm o) (c : @KSeq o lib) :=
  match c with
  | existT s (existT n i) => inhabited_type lib (mkc_apply2 P (mkc_nat n) s)
  end.

Definition pastSecured {o} {lib} P (c : @KSeq o lib) :=
  {d : KSeq & extends c d # apPred P d}.

Definition gtSeq {o} {lib} P (c d : @KSeq o lib) :=
  extends d c # !(pastSecured P d).

Definition ltSeq {o} lib P (c d : @KSeq o lib) := gtSeq P d c.

Definition decPred {o} lib (P : @CTerm o) :=
  forall c : @KSeq o lib, {apPred P c} + {~apPred P c}.

Definition update_kseq_from {o} {lib} (c : @KSeq o lib) (m : nat) (v : NVar) :=
  match c with
  | existT s (existT n i) => update_seq_from s n m v
  end.

Lemma decidable_forall_lt :
  forall P n,
    (forall m, m < n -> decidable (P m))
    -> decidable (forall m : nat, m < n -> P m).
Proof.
  induction n; introv dec.
  - left; introv q; try omega.
  - autodimp IHn hyp.
    destruct IHn as [d|d].
    + destruct (dec n) as [e|e]; try omega.
      * left; introv q.
        destruct (deq_nat m n); subst; auto.
        apply d; omega.
      * right; intro q.
        pose proof (q n) as z; autodimp z hyp.
    + right.
      intro q; destruct d.
      introv h; apply q; omega.
Qed.

Lemma decidable_ccequivc_mkc_apply_is_kseq {o} :
  forall lib (s1 s2 : @CTerm o) n1 n2 m,
    m < n2
    -> n2 <= n1
    -> is_kseq lib s1 n1
    -> is_kseq lib s2 n2
    -> decidable (ccequivc lib (mkc_apply s1 (mkc_nat m)) (mkc_apply s2 (mkc_nat m))).
Proof.
  introv l1 l2 i1 i2.
  pose proof (is_kseq_implies lib m s1 n1) as h1.
  repeat (autodimp h1 hyp); try omega.
  pose proof (is_kseq_implies lib m s2 n2) as h2.
  repeat (autodimp h2 hyp); try omega.
  exrepnd.
  destruct (deq_nat k0 k) as [d|d]; subst.

  - left.
    spcast.
    eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact h2|].
    eapply cequivc_trans;[|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0].
    eauto 3 with slow.

  - right; intro h; spcast.
    eapply cequivc_trans in h;[|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2].
    apply cequivc_sym in h; apply cequivc_nat_implies_computes_to_valc in h.
    eapply computes_to_valc_eq in h;[|exact h0].
    inversion h as [q].
    apply Znat.Nat2Z.inj in q; subst; omega.
Qed.

Lemma extends_dec {o} {lib} :
  forall (c d : @KSeq o lib), decidable (extends c d).
Proof.
  introv.

  destruct c as [s1 c].
  destruct c as [n1 i1].

  destruct d as [s2 d].
  destruct d as [n2 i2].

  unfold extends.

  destruct (gt_dec n1 n2) as [d|d];
    [|right; sp].

  assert (decidable
            (forall m : nat,
                m < n2 ->
                (mkc_apply s1 (mkc_nat m)) ~=~( lib)(mkc_apply s2 (mkc_nat m))))
    as e;
    [|destruct e as [e|e];[left;auto|right;sp] ].

  apply decidable_forall_lt.
  introv ltm.
  eapply decidable_ccequivc_mkc_apply_is_kseq; try (exact i1); try (exact i2); try omega.
Qed.

(* Howard & Kreisel
    "Transfinite Induction and Bar Induction of Types Zero and One,
     and the Role of Continuity in Intuitionistic Analysis"
   Theorem 5C, page 341
 *)
Lemma strong_wf_ltSeq {o} :
  forall lib P,
    barred lib P
    -> decPred lib P
    -> strong_wf (@gtSeq o lib P).
Proof.
  introv bar dec; introv.

Lemma mk_extension {o} :
  forall (f : nat -> @KSeq o),
    {g : Seq
     & forall n, 

  (update_kseq_from 
Qed.

Lemma well_founded_ltSeq {o} :
  forall lib P,
    barred lib P
    -> decPred lib P
    -> well_founded (@ltSeq o lib P).
Proof.
  introv bar dec; introv.
  destruct a as [s a].
  destruct a as [n i].

  Print Acc.
Qed.

Lemma well_founded_lt_seq {o} :
  forall lib P (b : @barred o lib P) v,
    well_founded (lt_seq lib P b v).
Proof.
  introv; unfold well_founded; introv.
  destruct a as [s a].
  destruct a as [n i].

Qed.

Lemma bar_induction_meta_sp {o} :
  forall lib P (X c : @CTerm o) v,
    barind_meta2_fun_bar lib P X v
    -> barind_meta2_fun_ind lib P X v
    -> meta2_fun_on_seq lib P X 0 (seq2kseq c 0 v).
Proof.
  introv bar ind.
  unfold barind_meta2_fun_ind in ind.
  unfold barind_meta2_fun_bar in bar.
  Print meta2_fun_on_seq.

  (*

Can we prove that given the bar, the relation a < b,
 true if a is closer to the bar (by 1) than b,
is well-founded?

   *)

  Check well_founded_induction_type.
  Print well_founded.

Qed.
