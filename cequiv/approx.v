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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export bin_rels.
Require Export computation_seq.
Require Export rel_nterm.

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


Definition close_compute_val {p} lib (R: NTrel) (tl tr : NTerm) : [univ]:=
  forall (c : CanonicalOp) (tl_subterms : list BTerm),
    (tl =v>(lib) (oterm (Can c) tl_subterms))
    -> {tr_subterms : list (@BTerm p)
        & (tr =v>(lib) (oterm (Can c) tr_subterms))
        # lblift (olift R) tl_subterms tr_subterms }.

(*
Definition close_compute_exc (R: NTerm -> NTerm -> [univ]) (tl tr : NTerm): [univ]:=
  forall (e : NTerm), (tl =e> e) -> {e' : NTerm & (tr =e> e') # upto_alpha R e e' }.
*)

Definition close_compute_exc {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall a e,
    (tl =e>(a,lib) e)
    -> {a' : NTerm & {e' : NTerm & (tr =e>(a',lib) e') # R a a' # R e e' }}.

(*
Definition close_compute_seq {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall f,
    (tl =s>(lib) f)
    -> {f' : ntseq & (tr =s>(lib) f') # (forall n, R (f n) (f' n)) }.
*)

Definition close_compute_seq {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall f,
    (tl =s>(lib) f)
    -> {f' : ntseq & (tr =s>(lib) f') # (forall n, R (f n) (f' n)) }.


Definition close_compute_mrk {p} lib (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall m, (tl =m>(lib) m) -> (tr =m>(lib) m).

Definition close_comput {p} lib (R: NTrel) (tl tr : @NTerm p) : [univ]:=
  isprogram tl
  # isprogram tr
  # close_compute_val lib R tl tr
  # close_compute_exc lib R tl tr
  # close_compute_seq lib R tl tr
  # True (*close_compute_mrk lib R tl tr*).

(** % \noindent \\* %  At this point, one could directly define [approx] as: *)

CoInductive approx_bad {p} :
  @library p -> @NTerm p -> @NTerm p -> [univ] :=
| approxC: forall lib tl tr,
  close_comput lib (approx_bad lib) tl tr
  -> approx_bad lib tl tr.

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

CoInductive approx_aux {p}
            (lib : library)
            (R : bin_rel NTerm)
            (tl tr: @NTerm p): [univ] :=
|approx_fold:
   close_comput lib (approx_aux lib R \2/ R) tl tr
   -> approx_aux lib R tl tr.

Definition approx {p} lib := @approx_aux p lib bot2.


(** %\noindent % The first thing we do is to
  prove  "co-induction principle" for approx using [cofix]
  and then never ever use [cofix] again.
  An interested user can walk through the proof
  of [approx_refl] below to see this co-induction
  principle in action.

 *)

Theorem approx_acc {p} :
  forall (lib : library)
         (l r0 : bin_rel (@NTerm p))
         (OBG: forall (r: bin_rel NTerm)
                      (INC: r0 =2> r) (CIH: l =2> r),
                 l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros. assert (SIM: approx_aux lib (r0 \2/ l) x0 x1) by eauto.
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna c Hcl. repnd.
  unfold close_comput.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    dorn Hap; spc.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd.
    exists a' e'; dands; auto; repdors; auto.

  - introv comp; allsimpl.
    apply Hcl4 in comp; exrepnd.
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

(** inspited by dom2.pdf, Nuprl's type-continuous
  lub in dom2.pdf == intersect in Nuprl == and here *)
Definition continuous {p} (F : bin_rel NTerm -> bin_rel NTerm) :=
   forall (Rn : nat -> bin_rel (@NTerm p)) (t1 t2 : @NTerm p),
  (forall n : nat, (F (Rn n)) t1 t2)
   <=> (F (fun x y => forall n : nat, (Rn  n) x y)) t1 t2.

Lemma close_comp_cont {p} : forall lib, @continuous p (close_comput lib).
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

Lemma approx_assume_hasvalue {p} :
  forall lib a b,
    isprogram a
    -> @isprogram p b
    -> (hasvalue_like lib a -> approx lib a b)
    -> approx lib a b.
Proof.
  introv Hpa Hpb Hha.
  constructor.
  unfold close_comput.
  dands; auto; introv Hcomp.

  - assert (hasvalue lib a) as Xh by (eexists; eauto); sp.
    autodimp Hha hyp; eauto with slow.
    invertsn Hha.
    unfold close_comput in Hha; repnd; eauto.

  - assert (raises_exception lib a) as Xh by (eexists;eauto).
    autodimp Hha hyp; eauto with slow.
    invertsn Hha.
    unfold close_comput in Hha; repnd; eauto.

(*
  - autodimp Hha hyp.
    { unfold computes_to_marker in Hcomp; repnd.
      eexists; dands; eauto with slow. }
    invertsn Hha.
    unfold close_comput in Hha; repnd; eauto.*)

  - autodimp Hha hyp; eauto 3 with slow.
    invertsn Hha.
    unfold close_comput in Hha; repnd; eauto.
Qed.

(** %\noindent \\*% The following is an easy corollary of the above.

 *)
Corollary bottom_approx_any {p} :
  forall lib t, @isprogram p t -> approx lib mk_bottom t.
Proof.
  introv Hpr.
  apply approx_assume_hasvalue; auto.

  introv Hv.
  unfold hasvalue_like in Hv; exrepnd.
  apply not_bot_reduces_to_is_value_like in Hv1; tcsp.
Qed.

(* begin hide *)

Lemma axiom_doesnt_compute_to_seq {o} :
  forall lib (f : @ntseq o), !(mk_axiom =s>(lib) f).
Proof.
  introv comp.
  unfold computes_to_seq in comp.
  apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

Lemma hasvalue_as_approx {pp} :
  forall lib a,
    @isprogram pp a
    -> (hasvalue lib a
        <=>
        approx lib mk_axiom (mk_cbv a nvarx mk_axiom)).
Proof.
  introv isp; split; intro k.

  - constructor.
    unfold close_comput; dands; tcsp.

    + apply isprogram_cbv; sp.
      rw @nt_wf_eq; sp.

    + introv comp.
      exists ([] : list (@BTerm pp)).
      apply computes_to_value_isvalue_eq in comp; dands; auto;
      inversion comp; subst; fold_terms;
      fold (@mk_axiom pp); GC; tcsp.
      * unfold computes_to_value; sp.
        apply cbv_reduce0; sp.
        rw @isprog_eq; sp.
      * constructor; simpl; sp.

    + introv ce.
      apply axiom_doesnt_raise_an_exception in ce; sp.

    + introv comp.
      apply axiom_doesnt_compute_to_seq in comp; sp.

(*
    + introv cm.
      apply axiom_doesnt_mark in cm; sp.
*)

  - inversion k as [c].
    unfold close_comput in c; repnd.
    pose proof (c2 NAxiom []) as h.
    allfold (@mk_axiom pp).
    autodimp h hyp.
    + apply computes_to_value_isvalue_refl; sp.
    + exrepnd.
      inversion h0 as [? imp]; allsimpl; cpx.
      allfold (@mk_axiom pp).
      assert (hasvalue lib (mk_cbv a nvarx mk_axiom)) as hv.
      * unfold hasvalue.
        exists (@mk_axiom pp); sp.
      * apply if_hasvalue_cbv0 in hv; sp.
        rw @isprog_eq; sp.
Qed.


(*
(** Same as approx but on well-formed terms *)
Definition approxw (a b : WTerm) :=
  approx (get_wterm a) (get_wterm b).
*)

(* end hide *)

(**

  Because in the PER semantics, Nuprl's types are defined as partial
  equivalence relations on closed terms, we define a closed version of
  [approx] as follows:

 *)

Definition approxc {p} lib (a b : @CTerm p) :=
  approx lib (get_cterm a) (get_cterm b).

(* begin hide *)

Definition hasvalue_likec {p} lib (t : @CTerm p) :=
  hasvalue_like lib (get_cterm t).

Definition has_value_likec {p} lib (t : @CTerm p) :=
  has_value_like lib (get_cterm t).

Lemma approxc_assume_hasvalue {p} :
  forall (lib : @library p) a b,
    (hasvalue_likec lib a -> approxc lib a b)
    -> approxc lib a b.
Proof.
  destruct a; destruct b; unfold hasvaluec, approxc; allsimpl; sp.
  apply approx_assume_hasvalue; sp; allrw @isprogram_eq; sp.
Qed.

Lemma hasvaluec_as_approxc {p} :
  forall lib a,
    hasvaluec lib a
    <=>
    approxc lib mkc_axiom (mkc_cbv a nvarx (@mkcv_axiom p nvarx)).
Proof.
  destruct a; unfold hasvaluec, approxc; simpl.
  apply hasvalue_as_approx.
  allrw @isprogram_eq; sp.
Qed.

Lemma approx_relates_only_progs {p} :
  forall lib (a b : @NTerm p), approx lib a b -> isprogram a # isprogram b.
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
    <=> (forall n, isprogram (f n)).
Proof.
  introv; split; intro h.
  - introv; inversion h as [c w]; clear c.
    rw @nt_wf_sterm_iff in w.
    pose proof (w n) as q; repnd.
    dands; auto; try (constructor; auto).
  - constructor; unfold closed; simpl; auto.
    constructor; introv.
    pose proof (h n) as q; repnd.
    inversion q as [c w]; dands; auto.
Qed.

(* end hide *)

(** %\noindent% We formalize a co-inductive proof
  of reflexivity of [approx] by using the [approx_acc] lemma above.
*)

Lemma approx_refl {p} :
  forall lib (t : @NTerm p), isprogram t -> approx lib t t.
Proof.
  unfold approx.
  intro lib.
  pose proof (@approx_acc p lib (fun x y => isprogram x # y=x)) as HH.
  allsimpl.
  assert (forall x0 x1 : @NTerm p, isprogram x0 # x1 = x0 -> approx_aux lib bot2 x0 x1);[| spcf;fail].
  eapply HH.
  intros.
  rename x0 into t.
  exrepnd. subst.
  constructor.
  unfold close_comput; dands; tcsp; introv comp; auto.

  - exists tl_subterms. split; auto.
    unfold lblift.  split; auto.
    intros ? Hlt. unfold blift.
    apply preserve_program in comp; auto.
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

  - applydup @preserve_program_exc2 in comp; auto; repnd.
    exists a e; dands; auto.

  - eexists; dands; eauto.
    introv.
    right.
    applydup @reduces_to_preserves_program in comp as wf; auto.
    apply CIH; dands; auto.
    rw @isprogram_mk_ntseq in wf.
    pose proof (wf n) as q; tcsp.
Qed.

Definition approx_open {p} lib := olift (@approx p lib).
Definition approx_open_bterm {p} lib := blift (@approx_open p lib).
Definition approx_bts {p} lib := lblift (@approx_open p lib).

Lemma approx_open_refl {p} :
  forall lib (nt: @NTerm p), (nt_wf nt) -> approx_open lib nt nt.
Proof.
  induction nt as [v|f| op bts Hind] using NTerm_better_ind; intros Hwf;
  constructor; try split; auto; intros  ? Hcl Hisp ?; apply approx_refl; auto.
Qed.

Lemma vbot_doesnt_compute_to_seq {o} :
  forall lib v (f : @ntseq o), !(mk_vbot v =s>(lib) f).
Proof.
  introv comp.
  unfold computes_to_seq in comp.
  apply reduces_to_vbot_if_isvalue_like in comp; eauto 3 with slow.
Qed.

(**

  The following lemma shows that approx_open doesn't preserve
  closeness because, for example, bottom is less than any variable.

 *)
Lemma approx_open_doesnt_preserve_closeness {p} :
  forall lib, approx_open lib mk_bot (@mk_var p nvarx).
Proof.
  introv; unfold approx_open, olift; dands; auto.
  rw @nt_wf_eq; apply wf_bot.

  introv.
  generalize (lsubst_mk_bot sub); intro k; exrepnd; rw k0; clear k0.
  introv wfs ispb ispv.
  constructor.
  unfold close_comput; dands; auto; introv comp; tcsp.

  - apply vbot_diverges in comp; sp.

  - apply vbot_doesnt_raise_an_exception in comp; sp.

(*
  - apply vbot_doesnt_mark in comp; sp.
 *)

  - apply vbot_doesnt_compute_to_seq in comp; tcsp.
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
    -> le_bin_rel (@close_comput p lib l) (close_comput lib r).
Proof.
  intros lib t1 t2 ra rb Hcl Hrab.
  allunfold @close_comput. repnd.
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

Lemma le_bin_rel_approx {p} :
  forall lib l r,
  le_bin_rel l r
  -> le_bin_rel (@approx_aux p lib l) (approx_aux lib r).
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
  -> approx a b 
  -> approx a' b) # 
  (alpha_eq_bterm  (bterm lva a) (bterm lva' a')
  -> blift approx_open (bterm lva a) (bterm lvb b) 
  -> blift approx_open (bterm lva' a') (bterm lvb b)).
Proof.
  unfold blift. unfold olift.
  cofix.
 *)

Lemma computes_to_seq_alpha {o} :
  forall lib (t1 t2 : @NTerm o) f,
    nt_wf t1
    -> alpha_eq t1 t2
    -> (t1 =s>(lib) f)
    -> {f' : ntseq & (t2 =s>(lib) f') # (forall n, alpha_eq (f n) (f' n))}.
Proof.
  introv wf aeq comp.
  eapply reduces_to_alpha in comp; eauto 3 with slow.
  exrepnd.
  inversion comp0 as [|? ? imp|]; subst; clear comp0.
  eexists; dands; eauto.
Qed.

Lemma respects_alpha_r_approx_aux_bot2 {p} :
  forall lib, respects_alpha_r (@approx_aux p lib bot2).
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
  unfold close_comput; dands; auto.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear ce; allunfold @close_compute_val;
    introv ca.
    apply cv in ca; exrepnd; clear cv.
    eapply compute_to_value_alpha with (t1' := oterm (Can c) tr_subterms) in aeq;
      eauto 3 with slow; exrepnd.
    inversion aeq0 as [|f| ? ? ? leq aeqbt]; subst; eauto 3 with slow.
    exists lbt2; dands; auto.
    allunfold @lblift; dands; repnd; auto; try omega.
    introv k.
    applydup ca0 in k.
    rw ca2 in k.
    applydup aeqbt in k.
    apply blift_alpha_fun_r with (nt2 := (tr_subterms {[n]})); auto.

  - clear cv; allunfold @close_compute_exc;
    introv ca.
    apply ce in ca; exrepnd; clear ce.
    repdors; try (complete (allunfold @bot2; sp)).
    eapply compute_to_exception_alpha with (t1' := e') in aeq;
      eauto 3 with slow; exrepnd.
    exists a'0 t2'; dands; auto.
    + left.
      apply (IND _ _ _ a'0) in ca1; auto.
    + left.
      apply (IND _ _ _ t2') in ca3; auto.

(*
  - clear cv ce.
    allunfold @close_compute_mrk.
    introv ca.
    apply cm in ca.
    eapply compute_to_marker_alpha in ca; eauto.
 *)

  - introv comp.
    apply cs in comp; exrepnd.
    eapply computes_to_seq_alpha in comp1; eauto 3 with slow.
    exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0.
    pose proof (comp2 n) as q; clear comp2.
    repndors; eauto 3 with slow.
    left.
    eapply IND; eauto.
Qed.

Lemma respects_alpha_r_approx_aux_bot2_or_bot2 {p} :
  forall lib, respects_alpha_r (@approx_aux p lib bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_r_approx_aux_bot2 _ _ _ b') in ap; auto.
Qed.

Lemma respects_alpha_l_approx_aux_bot2 {p} :
  forall lib, respects_alpha_l (@approx_aux p lib bot2).
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
  unfold close_comput; dands; auto.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear ce; allunfold @close_compute_val;
    introv ca'.
    applydup @alpha_prog_eauto in aeq as ispa'; auto.
    apply alpha_eq_sym in aeq.
    eapply compute_to_value_alpha with (t1' := oterm (Can c) tl_subterms) in aeq;
      eauto 3 with slow; exrepnd.
    inversion aeq0 as [|?| ? ? ? leq aeqbt]; subst.
    apply cv in aeq1; exrepnd; clear cv.
    exists tr_subterms; dands; auto.
    allunfold @lblift; dands; repnd; auto; try omega.
    introv k.
    applydup aeqbt in k.
    rw leq in k.
    applydup aeq2 in k.
    apply blift_alpha_fun_l with (nt1 := (lbt2 {[n]})); auto.
    apply alpha_eq_bterm_sym; auto.

  - clear cv; allunfold @close_compute_exc;
    introv ca.
    applydup @alpha_prog_eauto in aeq as ispa'; auto.
    apply alpha_eq_sym in aeq.
    eapply compute_to_exception_alpha with (t1' := e) in aeq;
      eauto 3 with slow; exrepnd.
    apply ce in aeq0; exrepnd; clear ce.
    repdors; try (complete (allunfold @bot2; sp)).
    exists a'1 e'; dands; auto.
    + left.
      apply (IND _ _ _ a0) in aeq0; auto.
      apply alpha_eq_sym; auto.
    + left.
      apply (IND _ _ _ e) in aeq5; auto.
      apply alpha_eq_sym; auto.

(*
  - clear cv ce.
    introv ca.
    apply alpha_eq_sym in aeq.
    eapply compute_to_marker_alpha in ca;[|eauto].
    apply cm in ca; auto.
 *)

  - introv comp.
    applydup @alpha_prog_eauto in aeq as wfa'; auto.
    apply alpha_eq_sym in aeq.
    eapply computes_to_seq_alpha in comp;[| |eauto]; eauto 3 with slow.
    exrepnd.
    apply cs in comp1; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0.
    pose proof (comp2 n) as q; clear comp2.
    repndors; eauto 3 with slow.
    left.
    apply alpha_eq_sym in h.
    eapply IND; eauto.
Qed.

Lemma respects_alpha_l_approx_aux_bot2_or_bot2 {p} :
  forall lib, respects_alpha_l (@approx_aux p lib bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_l_approx_aux_bot2 _ _ _ a') in ap; auto.
Qed.

Lemma respects_alphal_closed_comput {p} :
  forall lib R,
    respects_alpha_l R
    -> respects_alpha_l (@close_comput p lib R).
Proof.
  introv rR Hal Hap.
  repnud Hap.
  unfolds_base.
  alpha_hyps Hal.
  dands; eauto 2 with slow.

  - introv Hcv.
    eapply compute_to_value_alpha with (t2:=a) in Hcv; eauto with slow.
    exrepnd.
    applydup @computes_to_value_can in Hcv1.
    repndors; exrepnd.

    + rename bts into clbt2.
      subst. duplicate Hcv0 as H1cv. inverts Hcv0 as Hclen Hcal. rename c0 into c.
      apply Hap2 in Hcv1. eauto.
      exrepnd.
      exists tr_subterms.
      split; auto;[].
      repnud Hcv0.
      split;spcf;[].
      introv Hlt. duplicate Hlt.
      apply_clear Hcal in Hlt.
      dimp (Hcv0 n); [omega|].
      repnud hyp.
      exrepnd.
      unfold blift.
      exists lv nt1 nt2.
      spc; eauto.
      eauto with slow.

    + subst; allsimpl.
      inversion Hcv0.

  - introv comp.
    eapply compute_to_exception_alpha with (t2:=a) in comp; eauto with slow.
    exrepnd.
    apply Hap3 in comp0; exrepnd.
    exists a'1 e'; dands; auto.
    + apply (rR _ _ a0) in comp4; auto.
      apply alpha_eq_sym; auto.
    + apply (rR _ _ e) in comp0; auto.
      apply alpha_eq_sym; auto.

(*
  - introv comp.
    eapply compute_to_marker_alpha in comp;[|apply alpha_eq_sym; eauto].
    apply Hap in comp; auto.
 *)

  - introv comp.
    applydup @alpha_prog_eauto in Hal as wfa'; auto.
    apply alpha_eq_sym in Hal.
    eapply computes_to_seq_alpha in comp;[| |eauto]; eauto 3 with slow; exrepnd.
    apply Hap4 in comp1; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp2 n) as q; clear comp2.
    pose proof (comp0 n) as h; clear comp0.
    eauto 3 with slow.
(*    apply alpha_eq_sym in h.
    eapply rR; eauto.*)
Qed.

Lemma approxr_alpha_rw_l_aux {p} :
  forall lib r a b a',
    respects_alpha_l (approx_aux lib r \2/ r)
    -> @alpha_eq p a a'
    -> approx_aux lib r a b
    -> approx_aux lib r a' b.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphal_closed_comput; auto.
Qed.

Lemma approx_alpha_rw_l_aux {p} :
  forall lib a b a',
    @alpha_eq p a a'
    -> approx lib a b
    -> approx lib a' b.
Proof.
 unfold approx.
 introv.
 generalize (@respects_alpha_l_approx_aux_bot2_or_bot2 p lib).
 revert a b a'.
 exact (approxr_alpha_rw_l_aux lib bot2).
Qed.

Lemma respects_alphar_closed_comput {p} :
  forall lib R,
    respects_alpha_r R
    -> respects_alpha_r (@close_comput p lib R).
Proof.
  introv rR Hal Hap.
  repnud Hap.
  unfolds_base.
  alpha_hyps Hal.
  dands; eauto 2 with slow.

  - introv Hcv.
    apply Hap2 in Hcv.
    exrepnd.
    eapply compute_to_value_alpha with (t2:=b') in Hcv1; eauto with slow.
    exrepnd.
    invertsna Hcv2 Hbal.
    exists lbt2.
    split; eauto with slow;[].

    repnud Hcv0.
    split;spcf;[].

    introv Hlt. duplicate Hlt.
    apply_clear Hcv0 in Hlt.
    dimp (Hbal0 n); [omega|].
    repnud Hlt.
    exrepnd.
    unfold blift.
    exists lv nt1 nt2.
    spc; eauto.
    eauto with slow.

  - introv comp.
    apply Hap3 in comp; exrepnd.
    eapply compute_to_exception_alpha with (t2:=b') in comp0; eauto with slow.
    exrepnd.
    exists a'0 t2'; dands; auto.
    + apply (rR _ _ a'0) in comp2; auto.
    + apply (rR _ _ t2') in comp1; auto.

(*
  - introv comp.
    apply Hap in comp.
    eapply compute_to_marker_alpha in comp; eauto.
 *)

  - introv comp.
    apply Hap4 in comp; exrepnd.
    eapply computes_to_seq_alpha in comp1;[| |eauto]; eauto 3 with slow; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma approxr_alpha_rw_r_aux {p} :
  forall lib r a b b',
    respects_alpha_r (approx_aux lib r \2/ r)
    -> @alpha_eq p b b'
    -> approx_aux lib r a b
    -> approx_aux lib r a b'.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphar_closed_comput; auto.
Qed.

Lemma approx_alpha_rw_r_aux {p} :
  forall lib a b b',
    @alpha_eq p b b'
    -> approx lib a b
    -> approx lib a b'.
Proof.
 unfold approx.
 introv.
 generalize (@respects_alpha_r_approx_aux_bot2_or_bot2 p lib).
 revert a b b'.
 exact (approxr_alpha_rw_r_aux lib bot2).
Qed.

Hint Resolve approx_alpha_rw_r_aux : slowbad.
Hint Resolve approx_alpha_rw_l_aux : slowbad.

(* end hide *)
Lemma respects_alpha_closed_comput {p} :
  forall lib R, respects_alpha R -> respects_alpha (@close_comput p lib R).
Proof.
  introv ra.
  destruct ra.
  split.
  - apply respects_alphal_closed_comput; auto.
  - apply respects_alphar_closed_comput; auto.
Qed.

Corollary respects_alpha_approx {p} :
  forall lib, respects_alpha (@approx p lib).
Proof.
  split; introv; intros; eauto with slowbad.
Qed.
Hint Immediate respects_alpha_approx.


(* begin hide *)


Hint Resolve respects_alpha_closed_comput : respects.

Theorem approx_open_relates_only_wf {p} :
  forall lib (t1 t2 : @NTerm p),
    approx_open lib t1 t2
    -> nt_wf t1 # nt_wf t2.
Proof.
  introv.
  apply olift_relates_only_wf.
Qed.





Hint Resolve respects_alpha_approx : respects.

(** key helper for lemma 0.6 in annotated paper *)
Theorem approx_open_lsubst {p} :
  forall lib a b lvi lvo,
    let sub := @var_ren p lvi lvo in 
    approx_open lib a b
    -> approx_open lib (lsubst a sub) (lsubst b sub).
Proof.
  simpl. intros. apply olift_vars_lsubst; eauto with respects.
Qed.

Lemma approx_open_alpha_rw_l_aux {p} :
  forall lib a b a',
  @alpha_eq p a a'
  -> approx_open lib a b
  -> approx_open lib a' b.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold approx_open.
  rwg Hal. trivial.
Qed.

Lemma approx_open_alpha_rw_r_aux {p} :
  forall lib a b b',
  @alpha_eq p b b'
  -> approx_open lib a b
  -> approx_open lib a b'.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold approx_open.
  rwg Hal. trivial.
Qed.

Hint Resolve approx_open_alpha_rw_l_aux : slowbad.
Hint Resolve approx_open_alpha_rw_r_aux : slowbad.


Hint Resolve alphaeqbt_numbvars : slow.




(** this lemma can simplify many proofs a lot
    e.g. approx_trans, some lemma at the beginning of cequiv.
    whenever we destruct 2 lblift we get 2 sets
    of variables and this lemma helps us inify the,*)


Lemma approxbtd_change2 {p} : forall lib bt1 bt2 (lvn lva: list NVar),
  approx_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ approx_open lib nt1' nt2'
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
  unfold approx_open in Hab0.
  rwhg hyp0 Hab0.
  rwhg hyp2 Hab0.
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  split; spc;[|].
  - apply approx_open_lsubst;sp.
  - disjoint_reasoningv; rw @boundvars_lsubst_vars; spc; disjoint_reasoningv.
Qed.

Lemma approxbtd_change {p} : forall lib bt1 bt2 (lvn : list NVar),
  approx_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ approx_open lib nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # disjoint ((bound_vars nt1') ++ (bound_vars nt2')) lvn

   }.
Proof. intros.  apply approxbtd_change2 with (lva:= []); spc.
Qed.

Lemma approxbtd {p} : forall lib bt1 bt2 lva,
  approx_open_bterm lib bt1 bt2
  -> {lvn : (list NVar) & {nt1',nt2' : @NTerm p $ approx_open lib nt1' nt2'
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


Lemma approx_alpha_rw_l {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx lib a b <=> approx lib a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.

Lemma approx_alpha_rw_r {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx lib b a <=> approx lib b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.


Lemma remove_bot_approx {p} :
  forall lib, eq_bin_rel (approx_aux lib bot2 \2/ bot2) (@approx p lib).
Proof. unfold eq_bin_rel, le_bin_rel. split; eauto;[].
  introv Hp. dorn Hp; eauto. repnud Hp.
  allsimpl. contradiction.
Qed.

Hint Resolve remove_bot_approx.

Lemma clearbots_olift {p} : forall lib nt1 nt2,
  (@olift p (approx_aux lib bot2 \2/ bot2)) nt1 nt2
 <=> approx_open lib nt1 nt2.
Proof.
  introv.
  destruct (@eq_blift_olift p _ _ (remove_bot_approx lib)).
  unfold le_bin_rel in l. unfold le_bin_rel in l0.
  unfold approx_open.
  split; auto.
Qed.

Lemma clearbot_relbt {p} : forall lib (l1bt l2bt : list (@BTerm p)),
 lblift (olift (approx_aux lib bot2 \2/ bot2)) l1bt l2bt
  -> lblift (olift (approx lib)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_approx.
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

Lemma approx_trans_aux {p} :
  forall lib a b c a' c',
    alpha_eq a a'
    -> @alpha_eq p c c'
    -> approx lib a' b
    -> approx lib b c'
    -> approx lib a c.
Proof.
  intro lib.
  pose proof
  (approx_acc lib (fun a c => { b,a',c' : NTerm $
       alpha_eq a a' # alpha_eq c c' # approx lib a' b # approx lib b c'   })
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
  apply (approx_alpha_rw_l _ _ _ _ Hala) in Hab; eauto.
  apply (approx_alpha_rw_r _ _ _ _ Halc) in Hbc; eauto.
  clear Hala Halc.
  invertsn Hab.
  invertsn Hbc.
  constructor.
  unfold close_comput in Hab at 1.
  unfold close_comput in Hbc at 1.
  unfold close_comput at 1; dands; spcf.

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

    unfold approx_open in H2rb1.
    rwhg H2c0 H2rb1.
    rwhg H2c2 H2rb1.

    unfold approx_open in H1rb1.
    rwhg H1c0 H1rb1.
    rwhg H1c2 H1rb1.

    rename H2rb1 into H2ap.
    rename H1rb1 into H1ap.

    clear H1c0 H1c2 H2c0 H2c2.

    apply approx_open_lsubst with (lvi:=lv) (lvo:=lvn) in H1ap.
    apply approx_open_lsubst with (lvi:=lv0) (lvo:=lvn) in H2ap.
    unfold approx_open in H2ap.
    rwhg Hlink H2ap.
    assert(approx_open lib (lsubst nt2n0 (var_ren lv0 lvn))
                 (lsubst nt2n (var_ren lv lvn))) as Hapl by (eauto with slow).
    clear H2ap.
    (* setting the stage for approx_open_trans proof .. identical var/hym names *)
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
    allunfold @close_compute_exc.
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


Corollary approx_trans {p} :
  forall lib (a b c : @NTerm p),
    approx lib a b
    -> approx lib b c
    -> approx lib a c.
Proof.
 intros. eapply approx_trans_aux; eauto with slow.
Qed.

(* begin hide *)



Lemma approx_wf_term {p} :
  forall lib (a b : @NTerm p),
    approx lib a b -> wf_term a # wf_term b.
Proof.
  intros. inversion X; subst.
  unfold close_comput in X0; sp; subst; allunfold @isprogram; sp; allrw @nt_wf_eq; sp.
Qed.

Lemma approx_isprog {p} :
  forall lib (a b : @NTerm p),
    approx lib a b -> isprog a # isprog b.
Proof.
  intros. inversion X; subst.
  unfold close_comput in X0; sp; allrw @isprog_eq; sp.
Qed.

Lemma approxc_refl {p} :
  forall lib (t : @CTerm p), approxc lib t t.
Proof.
  intro; destruct t; unfold approxc; simpl.
  apply approx_refl; allrw @isprogram_eq; sp.
Qed.

Lemma approxc_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p),
    approxc lib t1 t2 -> approxc lib t2 t3 -> approxc lib t1 t3.
Proof.
  intro; destruct t1, t2, t3; unfold approxc; simpl.
  apply approx_trans.
Qed.


Lemma approx_canonical_form {p} :
  forall lib t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> approx lib t t'
    -> {bterms' : list (@BTerm p) &
         computes_to_value lib t' (oterm (Can op) bterms')
         # lblift (approx_open lib) bterms bterms' }.
Proof.
  intros ? ? ? ? ? Hcomp Hap.
  invertsn Hap. repnud Hap.
  apply Hap2 in Hcomp. exrepnd.

  apply clearbot_relbt in Hcomp0.
  eexists; eauto with slow.
Qed.


Lemma exception_approx {p} :
  forall lib t t' a e,
    (t =e>( a, lib)e)
    -> approx lib t t'
    -> { a' : @NTerm p &
       { e' : @NTerm p &
         ( t' =e>( a', lib)e')
         # (approx_aux lib bot2 a a'[+]bot2 a a')
         # (approx_aux lib bot2 e e'[+]bot2 e e') }}.
Proof.
  introv Hcomp Hap.
  invertsn Hap. repnud Hap.

  apply Hap3 in Hcomp. exrepnd.
  exists a' e'. split. auto. split; auto.
Qed.

Lemma approx_comput_functionality_left {p} :
  forall lib a a' b,
    @reduces_to p lib a a'
    -> approx lib a b
    -> approx lib a' b.
Proof.
  intros ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold close_comput. applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2.
    allunfold @computes_to_value.
    repnd; dands; auto.
    apply @reduces_to_trans with (b:=a'); auto.

  - apply Hap3.
    apply @reduces_to_computes_to_exception with (b := a'); auto.

(*
  - apply Hap.
    allunfold @computes_to_marker; repnd; dands; auto.
    eapply reduces_to_trans; eauto.
 *)

  - apply Hap4.
    eapply reduces_to_trans; eauto.
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

Lemma approx_comput_functionality_right {p} :
  forall lib a b b',
    @reduces_to p lib b b'
    -> approx lib a b
    -> approx lib a b'.
Proof.
  intros ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold close_comput. applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2 in comp. exrepnd. exists tr_subterms.
    split; auto.
    apply reduces_to_value_eq with (t:=b); auto.

  - apply Hap3 in comp; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    exists a' e'; dands; auto.
    apply reduces_to_exception_eq with (t := b); auto.

(*
  - apply Hap in comp.
    eapply reduces_to_marker_eq in comp; eauto.
 *)

  - apply Hap4 in comp; exrepnd.
    exists f'; dands; auto.
    eapply reduces_to_isvalue_like_eq; eauto 3 with slow.
Qed.

Lemma reduces_to_implies_approx {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx lib x t # approx lib t x.
Proof.
  intros.
  duplicate H.
  apply approx_comput_functionality_left with (b := t) in H; sp.
  apply approx_comput_functionality_right with (a := t) in H0; sp.
  apply approx_refl; sp.
  apply approx_refl; sp.
Qed.

Lemma reduces_to_implies_approx1 {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx lib x t.
Proof.
  introv isp r.
  apply reduces_to_implies_approx in r; sp.
Qed.

Lemma reduces_to_implies_approx2 {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx lib t x.
Proof.
  introv isp r.
  apply reduces_to_implies_approx in r; sp.
Qed.

Lemma approx_if_reduce_to_same {p} :
  forall lib a b c,
    @isprogram p a
    -> isprogram b
    -> reduces_to lib a c
    -> reduces_to lib b c
    -> approx lib a b.
Proof.
  introv ispa ispb reda redb.
  apply @approx_trans with (b := c).
  apply @approx_comput_functionality_right with (b := a); auto.
  apply approx_refl; auto.
  apply @approx_comput_functionality_left with (a := b); auto.
  apply approx_refl; auto.
Qed.

(* end hide *)

Lemma computes_to_value_implies_approx {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx lib x t # approx lib t x.
Proof.
  introv p c.
  unfold computes_to_value in c; repd.
  apply reduces_to_implies_approx in r; sp.
Qed.

Lemma computes_to_exception_implies_approx {o} :
  forall lib a (t x : @NTerm o),
    isprogram t
    -> computes_to_exception lib a t x
    -> approx lib (mk_exception a x) t # approx lib t (mk_exception a x).
Proof.
  introv p c.
  unfold computes_to_exception in c; repd.
  apply reduces_to_implies_approx in c; sp.
Qed.

(* begin hide *)

Lemma computes_to_value_implies_approx1 {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx lib x t.
Proof.
  introv p c.
  apply computes_to_value_implies_approx in c; sp.
Qed.

Lemma computes_to_value_implies_approx2 {pp} :
  forall lib t x,
    @isprogram pp t
    -> computes_to_value lib t x
    -> approx lib t x.
Proof.
  introv p c.
  apply computes_to_value_implies_approx in c; sp.
Qed.

Lemma reduces_toc_implies_approxc {p} :
  forall lib t x,
    @reduces_toc p lib t x
    -> approxc lib x t # approxc lib t x.
Proof.
  destruct t; destruct x0; unfold reduces_toc, approxc; simpl.
  apply reduces_to_implies_approx.
  rw @isprogram_eq; sp.
Qed.

Lemma computes_to_valc_implies_approxc {p} :
  forall lib t x,
    @computes_to_valc p lib t x
    -> approxc lib x t # approxc lib t x.
Proof.
  destruct t; destruct x0; unfold computes_to_valc, approxc; simpl.
  apply computes_to_value_implies_approx.
  rw @isprogram_eq; sp.
Qed.

Lemma not_hasvalue_ncan {p} :
  forall lib c bts,
    ! hasvalue lib (oterm (@NCan p c) bts).
Proof.
  unfold hasvalue; sp.
Abort.

(* end hide *)
Lemma hasvalue_approx {p} :
  forall lib t u,
    @approx p lib t u
    -> hasvalue lib t
    -> hasvalue lib u.
Proof.
  unfold hasvalue; introv ap hvt; exrepd.
  inversion ap as [cc]; subst.
  unfold close_comput in cc; repnd.
  applydup @computes_to_value_can in c; repndors; exrepd; subst.
  - apply cc2 in c; sp.
    exists (oterm (Can c1) tr_subterms); sp.
  - unfold computes_to_value in c; repnd.
    apply cc4 in c0; exrepnd.
    unfold computes_to_value.
    eexists; dands; eauto 3 with slow.
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

Lemma hasvalue_subst_preserves_approx {o} :
  forall lib x (t : @NTerm o) v u,
    isprog_vars [v] t (* wf_term t? *)
    -> hasvalue lib (subst t v u)
    -> approx lib u x
    -> hasvalue lib (subst t v x).
Proof.
  introv pt hv ap.
  applydup @approx_relates_only_progs in ap as p.
  destruct p as [pu px].

  nterm_ind t as [z|f ind|op bs ind] Case; auto.

  - Case "vterm".
    allrw @isprog_vars_vterm; allsimpl; repndors; tcsp; subst.
    unfsubst; unfsubst in hv; allsimpl; boolvar.
    apply hasvalue_approx with (t := u); sp.

  - Case "oterm".
    allunfold @subst; allsimpl.
Abort.

(* Corollary of hasvalue_subst_preserves_approx *)
Lemma hasvalue_subst_preserves_computation {p} :
  forall lib x t v u,
    isprogram t
    -> @isprog_vars p [v] u
    -> hasvalue lib (subst u v x)
    -> computes_to_value lib t x
    -> hasvalue lib (subst u v t).
Proof.
  sp.
  apply computes_to_value_implies_approx in X1; sp.
(*  apply hasvalue_subst_preserves_approx with (u := x); sp.*)
Abort.



(* end hide *)

Theorem alpha_implies_approx2 {p} : forall lib nt1 nt2,
  @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> approx lib nt1 nt2.
Proof.
  introv H2isp Hal.
  apply (approx_alpha_rw_l _ _ _ _ Hal).
  apply approx_refl; auto.
Qed.

(* begin hide *)
Theorem alpha_implies_approx3 {p} : forall lib nt1 nt2,
  @isprogram p nt1
  -> alpha_eq nt1 nt2
  -> approx lib nt1 nt2.
Proof.
  introv H2isp Hal. apply alpha_eq_sym in Hal.
  apply (approx_alpha_rw_r _ _ _ _ Hal).
  apply approx_refl; auto.
Qed.

Theorem alpha_implies_approx {p} : forall lib nt1 nt2,
  isprogram nt1
  -> @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> approx lib nt1 nt2.
Proof.
  intros. apply alpha_implies_approx2; auto.
Qed.

Hint Resolve approx_trans alpha_eq_sym alpha_implies_approx: slow.



Lemma not_axiom_approx_bot {pp} :
  forall lib, !@approx pp lib mk_axiom mk_bot.
Proof.
  introv ap.
  inversion ap as [cc]; subst.
  unfold close_comput in cc; repnd.
  generalize (cc2 NAxiom []); intro h.
  dest_imp h hyp; sp.
  apply computes_to_value_isvalue_refl; sp.
  inversion p; allsimpl; cpx.
  inversion p0.
  allfold @mk_axiom.
  apply not_bot_reduces_to_value in H; sp.
Qed.

Lemma not_axiom_approxc_bot {p} :
  forall lib, !@approxc p lib mkc_axiom mkc_bot.
Proof.
  unfold approxc, mkc_axiom, mkc_bot; simpl.
  apply not_axiom_approx_bot.
Qed.

Hint Resolve approx_open_relates_only_wf : slow.

Lemma approxbt_btwf {p} :
  forall lib, le_bin_rel (approx_open_bterm lib) (fun b1 b2 => @bt_wf p b1 # bt_wf b2).
Proof.
  introv Hapb.
  repnud Hapb.
  repnud Hapb.
  exrepnd.
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb2)).
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb0)).
  rw @bt_wf_iff.
  rw @bt_wf_iff.

  eapply approx_open_relates_only_wf; eauto.
Qed.



Lemma approxbt_fvars {p} :
  forall lib vsa vsb a b,
    approx_open_bterm lib (bterm vsa a) (@bterm p vsb b)
    -> subset (free_vars a) vsa # subset (free_vars b) vsb.
Proof.
Abort. (** not true anymore? *)



Theorem approx_implies_approx_open {p} :
  forall lib t1 t2,
    @approx p lib t1 t2
    -> approx_open lib t1 t2.
Proof.
  introv Hap. applydup @approx_relates_only_progs in Hap.
  repnd. unfold approx_open, olift. dands; eauto 2 with slow.
  introv Hwf H1p H2p.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap1.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap0.
  rwg Hap0.
  rwg Hap1.
  trivial.
Qed.


Theorem approx_open_approx {p} :
  forall lib t1 t2,
    isprogram t1
    -> @isprogram p t2
    -> approx_open lib t1 t2
    -> approx lib t1 t2.
Proof.
  introv H1pr H2pr Hol.
  invertsna Hol Hol.
  exrepnd.
  assert (@wf_sub p [])  as Hwf by (apply sub_range_sat_nil).
  apply Hol0 in Hwf;allrw @lsubst_nil; auto.
Qed.

Hint Resolve computes_to_value_isvalue_refl computes_to_value_isvalue_eq : slow.
Hint Constructors isvalue : slow.

Lemma approx_canonical_form2 {p} :
  forall lib op bterms1 bterms2,
    approx lib (oterm (@Can p op) bterms1) (oterm (Can op) bterms2)
    -> lblift (approx_open lib) bterms1 bterms2.
Proof.
  introv Hap. applydup @approx_relates_only_progs in Hap. repnd.
  eapply approx_canonical_form in Hap; exrepnd; eauto with slow.
  apply computes_to_value_isvalue_eq in Hap3;
  inverts Hap3; eauto with slow.
Qed.

Lemma clearbot_relbt2 {p} : forall lib (l1bt l2bt : list (@BTerm p)),
  lblift (olift (approx lib)) l1bt l2bt
  ->lblift (olift (approx_aux lib bot2 \2/ bot2)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_approx.
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

Lemma blift_approx_open_nobnd {p} :
  forall lib nt1 nt2,
    blift (approx_open lib) (nobnd nt1) (@nobnd p nt2)
    -> isprogram nt1
    -> isprogram nt2
    -> approx lib nt1 nt2.
Proof.
  introv Hrel H1pr H2pr.
  unfold blift in Hrel. exrepnd.
  apply alphaeqbt_nilv3 in Hrel0; exrepnd; subst.
  apply alphaeqbt_nilv3 in Hrel2; exrepnd; subst. GC.
  apply approx_open_approx;  eauto 2 with slow.
  unfold approx_open.
  rwg Hrel2.
  rwg Hrel0.
  trivial.
Qed.


Lemma blift_approx_open_nobnd2 {p} :
  forall lib nt1 nt2,
    isprogram nt1
    -> @isprogram p nt2
    -> approx lib nt1 nt2
    -> blift (approx_open lib) (nobnd nt1) (nobnd nt2).
Proof.
  introv Hap H1pr H2pr.
  unfold blift. exists ([]: list NVar) nt1 nt2.
  dands; try (apply alphaeqbt_refl);[].
  apply approx_implies_approx_open; sp.
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
    | [ H: approx t ?t2 |- _] => apply approx_relates_only_progs in H; repnd;sp
    | [ H: approx ?t2 t |- _ ] => apply approx_relates_only_progs in H; repnd;sp
    end
  end
  ).

Ltac alpha_to_approx :=
(repeat match goal with
| [ H: (alpha_eq _ _) |- _ ] => 
  let Hs := fresh "Hsym" in
  pose proof (alpha_eq_sym _ _ H) as Hs;
  apply alpha_implies_approx in H; try(prove_program);sp;
  apply alpha_implies_approx in Hs; try(prove_program);sp; apply hide_hyp in H
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
Corollary approx_open_trans {p} :
  forall lib (a b c : @NTerm p),
    approx_open lib a b
    -> approx_open lib b c
    -> approx_open lib a c.
Proof.
  intro lib.
  apply olift_trans; revert lib.
  - exact approx_trans.
  - exact respects_alpha_approx.
Qed.
Hint Resolve approx_open_trans: slow.
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

Definition simpl_close_comput {p} lib (R : NTerm -> NTerm -> Type) (tl tr : NTerm) : Type  :=
  isprogram tl
  # isprogram tr
  # (* need to prove that all terms related by sqlen are programs *)
  forall (c : CanonicalOp) (tl_subterms : list BTerm),
    computes_to_value lib tl (oterm (Can c) tl_subterms)
    -> { tr_subterms : list BTerm &
         computes_to_value lib tr (oterm (Can c) tr_subterms)
         # @lblift p (simpl_olift R) tl_subterms tr_subterms }.


CoInductive simpl_approx_aux {p} lib (R : bin_rel NTerm) (tl tr : @NTerm p) : [univ] :=
| simpl_approx_fold :
    simpl_close_comput lib (approx_aux lib R \2/ R) tl tr
    -> simpl_approx_aux lib R tl tr.


Lemma approx_open_simpler_equiv {p} :
  forall lib a c,
    simpl_olift (@approx p lib) a c <=> approx_open lib a c.
Proof.
  introv.
  split.

  - intro Hos. repnud Hos.
    unfold approx_open, olift.
    dands;auto.
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.
    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    apply (approx_alpha_rw_l _ _ _ _ Xtrima).
    apply (approx_alpha_rw_r _ _ _ _ Xtrimc).
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
  simpl_approx_aux r a c
  -> approx_aux r a c.
Proof.
  intro r. 
  pose proof 
  (approx_acc (fun a c => { b,a',c' : NTerm $
       alpha_eq a a' # alpha_eq c c' # simpl_approx_aux r a' c'  })
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



Theorem alpha_implies_approx_open {p} : forall lib nt1 nt2,
  @nt_wf p nt1
  -> alpha_eq nt1 nt2
  -> approx_open lib nt1 nt2.
Proof.
  introv H1wf  Hal. repeat(split;[sp|]).
  alpha_hyps Hal;sp.
  introv Hpr H1pr H2pr.
  apply alpha_implies_approx; sp.
  apply lsubst_alpha_congr2;sp.
Qed.

Hint Resolve alpha_implies_approx_open : slowbad.

Hint Resolve approx_open_relates_only_wf
  approx_open_trans approx_open_refl: slow.


Lemma approx_open_alpha_rw_l {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_open lib a b <=> approx_open lib a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold approx_open.
  split; introv Hyp;
  applydup @approx_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma approx_open_alpha_rw_r {p} : forall lib a b a',
  @alpha_eq p a a'
  -> (approx_open lib b a <=> approx_open lib b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold approx_open.
  split; introv Hyp; 
  applydup @approx_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0; 
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma approx_open_alpha_rw_lr {p} : forall lib a b a' b',
  alpha_eq a a'
  -> @alpha_eq p b b'
  -> (approx_open lib a b <=> approx_open lib a' b').
Proof.
  introv Hala Halb.
  eapply @approx_open_alpha_rw_l with (b:=b) in Hala.
  eapply @approx_open_alpha_rw_r with (b:=a') in Halb.
  dtiffs.
  split; eauto.
Qed.

Ltac prove_wf1 :=
  sp;
 (
  match goal with
  | [ |- nt_wf ?t] =>
    match goal with
    | [ H: approx_open t ?t2 |- _] => apply approx_open_relates_only_wf in H; repnd;sp
    | [ H: approx_open ?t2 t |- _ ] => apply approx_open_relates_only_wf in H; repnd;sp
    end
  end
  ).

Hint Resolve approx_open_trans : approx_open_trans.


(* end hide *)

Hint Resolve isprogram_fix  isprogram_apply : slow.



Lemma approx_open_lsubst_congr {p} : forall lib ta tb sub,
  @wf_sub p sub
  -> approx_open lib ta tb
  -> approx_open lib (lsubst ta sub) (lsubst tb sub).
Proof.
  introv Hwf Hap.
  applydup @approx_open_relates_only_wf in Hap.
  repeat(split; [apply lsubst_wf_iff;sp;fail|]).
  intros subo Hwfs H1ps H2pr.
  unfold approx_open in Hap.
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

(**  % \noindent \\*% We wish to prove that approx is a congruence. However,
    it is a fairly non-trivial task and the main content of %\cite{Howe:1989}%.
    For now, the following lemmma
    asserts that approx is a congruence w.r.t canonical [Opid]s.
    The general proof of congruence is discussed in the next subsection.
    *)

Lemma approx_canonical_form3 {p} :
  forall lib op bterms1 bterms2,
    isprogram (oterm (@Can p op) bterms1)
    -> isprogram (oterm (Can op) bterms2)
    -> lblift (approx_open lib) bterms1 bterms2
    -> approx lib (oterm (Can op) bterms1) (oterm (Can op) bterms2).
Proof.
  introv H1p H2p Hap. constructor. unfold close_comput.
  dands; eauto; introv comp.

  - apply computes_to_value_isvalue_eq in comp; eauto with slow;[].
    inverts comp.
    eexists; dands; eauto with slow.
    apply clearbot_relbt2. auto.

  - apply can_doesnt_raise_an_exception in comp; sp.

(*
  - apply can_doesnt_mark in comp; sp.
*)

  - apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

Lemma approx_canonical_form_exc {o} :
  forall lib a1 a2 (e1 e2 : @NTerm o),
    approx lib a1 a2
    -> approx lib e1 e2
    -> approx lib (mk_exception a1 e1) (mk_exception a2 e2).
Proof.
  introv ap1 ap2.
  applydup @approx_relates_only_progs in ap1; repnd.
  applydup @approx_relates_only_progs in ap2; repnd.
  constructor.
  unfold close_comput.
  dands; eauto; try (rw @isprogram_exception_iff; tcsp); introv comp.

  - apply computes_to_value_exception in comp; sp.

  - apply computes_to_exception_exception in comp; repnd; subst.
    exists a2 e2; dands; auto.
    apply computes_to_exception_refl.

(*
  - apply exception_doesnt_mark in comp; sp.
*)

  - apply reduces_to_exception in comp; eauto 3 with slow; ginv.
Qed.


(* begin hide *)

Lemma approx_decomp_approx {p} :
  forall lib a b c d,
    approx lib (mk_approx a b) (@mk_approx p c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_approx; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp. repnd. allsimpl.
    alpharelbtd. GC.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd. applydup @approx_relates_only_progs in Hyp. repnd.
    applydup @approx_relates_only_progs in Hyp0. repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma approxbt_lsubst_prog {p} :
  forall lib lv1 lv2 t1 t2,
    isprogram_bt (bterm lv1 t1)
    -> isprogram_bt (bterm lv2 t2)
    -> approx_open_bterm lib (bterm lv1 t1) (bterm lv2 t2)
    -> forall lnt,
       length lnt= length lv1
       -> (forall t, LIn t lnt -> @isprogram p t)
       ->  approx lib (lsubst t1 (combine lv1 lnt)) (lsubst t2 (combine lv2 lnt)).
Proof.
  introv H1p H2p Ha0 Hlen Hlp.
  applydup @blift_numbvars in Ha0.
  unfold num_bvars in Ha1; simpl in Ha1.
  unfold approx_open_bterm in Ha0.
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
  apply approx_open_lsubst with (lvi:=lv) (lvo:=lvn) in Ha0.
  apply alpha_eq_sym in Ha5.
  apply alpha_eq_sym in Ha4.
  unfold approx_open in Ha0.
  rwhg Ha5 Ha0.
  rwhg Ha4 Ha0.

  assert (approx_open lib
    (lsubst t1 (var_ren lv1 lvn)) (lsubst t2 (var_ren lv2 lvn)))
   as XX by auto. (** alpha replacement *)
  unfold approx_open in XX.
  repnud XX.
  pose proof (XX (combine lvn lnt)) as XXX.
  clear XX.
  pose proof flat_map_progs _ Hlp as Hfl.
  rw @lsubst_nest_same in XXX;spc; disjoint_reasoningv;
    [ | rw Hfl; disjoint_reasoning; fail].
  rw @lsubst_nest_same in XXX;spc; disjoint_reasoningv;
    [ | rw Hfl; disjoint_reasoning; fail].
  apply XXX;sp.
  introv Hin. eauto with slow.
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
    applydup @approx_relates_only_progs in Hceq; repnd;
    applydup @preserve_program in Hcomp as Hcomp0; auto;
    eapply @approx_canonical_form in Hcomp; eauto;
    destruct Hcomp as [bterms' Hcomp];
    destruct Hcomp as [Hcomp1 Hcomp2];
    applydup @preserve_program in Hcomp1 as Hcomp3; auto;
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
    rep_eexists; dands; eauto; apply @approx_open_approx;
    eauto 2 with slow.

(* end hide *)
Lemma approx_mk_pair {p} :
  forall lib (t t' a b : NTerm),
    computes_to_value lib t (mk_pair a b)
    -> approx lib t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_pair a' b')
         # approx lib a a'
         # approx lib b b'}.
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
  unfold close_comput in H2; sp.

Qed.

Definition approxow (a b : WTerm) :=
  approx_open (get_wterm a) (get_wterm b).
*)


Lemma approx_exception {p} :
  forall lib en (a b : @NTerm p),
    approx lib (mk_exception en a) b
    -> {x : NTerm
        & {c : @NTerm p
        & computes_to_exception lib x b c
        # approx lib en x
        # approx lib a c}}.
Proof.
  introv ap.
  invertsn ap.
  unfold close_comput in ap; repnd.
  generalize (ap3 en a); intro k; autodimp k hyp.
  { apply computes_to_exception_refl. }
  exrepnd.
  exists a' e'; sp; inversion b0.
Qed.

(*
Lemma approx_mk_marker {o} :
  forall lib (t : @NTerm o) m,
    approx lib (mk_marker m) t
    -> computes_to_marker lib t m.
Proof.
  introv ap.
  inversion ap as [c]; clear ap.
  unfold close_comput in c; repnd.
  pose proof (c m) as h.
  autodimp h hyp.
  apply compute_to_marker_mrk.
Qed.

Lemma approx_mk_marker_iff {o} :
  forall lib (t : @NTerm o) m,
    isprogram t
    -> (approx lib (mk_marker m) t
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
