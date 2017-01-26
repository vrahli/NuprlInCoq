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

  Authors: Mark Bickford
           Abhishek Anand
           Vincent Rahli

*)


Require Export approx.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #<=># *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** We make a variants of  [close_comput], and [approx]
    that treat exceptions of a given name e like bottom.
    That is, when the canonical form of the first, approximating, term
    is exception, then the relation holds if the name computes to e.
    Otherwise the definition is the same as for [close_comput].
 *)


(** printing =v>  $\Downarrow$ #=v># *)

Definition ex_close_compute_exc {p} lib ex (R: @NTrel p) (tl tr : @NTerm p) : [univ]:=
  forall a e,
    (tl =e>(a,lib) e)
    -> R a ex + {a' : NTerm & {e' : NTerm & (tr =e>(a',lib) e') # R a a' # R e e' }}.

Definition ex_close_comput {p} lib ex (R: NTrel) (tl tr : @NTerm p) : [univ]:=
  isprogram tl
  # isprogram tr
  # close_compute_val lib R tl tr
  # ex_close_compute_exc lib ex R tl tr
  # close_compute_seq lib R tl tr
  # True (*close_compute_mrk lib R tl tr*).

CoInductive ex_approx_bad {o} :
  @library o -> @NTerm o -> @NTerm o -> @NTerm o -> [univ] :=
| ex_approxC: forall lib ex tl tr,
    ex_close_comput lib ex (ex_approx_bad lib ex) tl tr
    -> ex_approx_bad lib ex tl tr.

CoInductive ex_approx_aux {p}
            (lib : library)
            (ex : NTerm)
            (R : bin_rel NTerm)
            (tl tr: @NTerm p): [univ] :=
| ex_approx_fold:
   ex_close_comput lib ex (ex_approx_aux lib ex R \2/ R) tl tr
   -> ex_approx_aux lib ex R tl tr.

Definition ex_approx {p} lib ex := @ex_approx_aux p lib ex bot2.


(** %\noindent % The first thing we do is to
  prove  "co-induction principle" for ex_approx using [cofix]
  and then never ever use [cofix] again.
  An interested user can walk through the proof
  of [ex_approx_refl] below to see this co-induction
  principle in action.

 *)

Theorem ex_approx_acc {p} :
  forall (lib : library)
         (ex : NTerm)
         (l r0 : bin_rel (@NTerm p))
         (OBG: forall (r: bin_rel NTerm)
                      (INC: r0 =2> r) (CIH: l =2> r),
                 l =2> ex_approx_aux lib ex r),
    l =2> ex_approx_aux lib ex r0.
Proof.
  intros. assert (SIM: ex_approx_aux lib ex (r0 \2/ l) x0 x1) by eauto.
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna e Hcl. repnd.
  unfold ex_close_comput.
  dands; eauto; GC.

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
    destruct Hcomp.
    + left; dands; auto; repdors; auto.
    + right.
      exrepnd.
      exists a' e'; dands; auto; repdors; auto.

  - introv Hcomp.
    apply Hcl4 in Hcomp; exrepnd.
    exists f'; dands; auto.
    introv.
    pose proof (Hcomp0 n) as q; repndors; auto.
Qed.

Corollary ex_approx_acc2 {p} :
  forall (lib : library)
         (ex : NTerm)
         (l: bin_rel (@NTerm p))
         (OBG: forall (r: bin_rel NTerm)
                      (CIH: l =2> r),
                 l =2> ex_approx_aux lib ex r),
    l =2> ex_approx lib ex .
Proof.
  intros. pose proof @ex_approx_acc p lib ex l bot2. apply X in PR. unfold ex_approx. auto.
  intros. pose proof OBG r CIH x2 x3 PR0. auto.
Qed.

(** %\noindent% Reflexivity of [ex_approx] follows from reflexivity
               of [approx] and this lemma.
*)

Lemma approx_implies_ex_approx {p} :
  forall lib (ex tl tr : @NTerm p), approx lib tl tr -> ex_approx lib ex tl tr.
Proof.
  introv app.
  pose proof (@ex_approx_acc2 p lib ex (fun x y => approx lib x y)) as HH.
  allsimpl. apply HH; auto. introv CIH apr.
  clear tl tr app HH. rename x0 into tl. rename x1 into tr.
  constructor.
  applydup @approx_relates_only_progs in apr.
  rename apr0 into pr.
  exrepnd.
  unfold ex_close_comput; dands; tcsp; introv comp; auto.

  - eapply approx_canonical_form in comp; eauto; exrepnd.
    exists bterms'; split; auto.
    eapply le_lblift2; eauto. introv apo.
    pose proof @le_olift p r (ex_approx_aux lib ex r \2/ r) as X.
    unfold le_bin_rel in X. eapply X; auto. clear X.
    destruct apo; exrepnd. split; auto.

  - destruct apr. destruct c; exrepnd. pose proof p3 a e comp as X; exrepnd.
    right. exists a' e'. split; auto; split; right.
    + clear X1. destruct X2.
      * pose proof CIH a a' a0; auto.
      * destruct b.
    + clear X2. destruct X1. pose proof CIH e e' a0; auto. destruct b.

  - destruct apr as [cl].
    destruct cl; exrepnd; GC.
    apply p4 in comp; exrepnd.
    exists f'; dands; auto.
    introv.
    pose proof (comp0 n) as q; repndors; dands; auto.
    unfold bot2 in *; simpl in *; tcsp.
Qed.

Lemma ex_approx_refl {p}:
  forall (lib : library) (ex t : @NTerm p),
  isprogram t -> ex_approx lib ex t t.
Proof.
 intros. apply approx_implies_ex_approx. apply approx_refl. auto.
Qed.


(** %\noindent \\*%The following lemma says that for programs
    [a] and [b], if we have to prove [ex_approx a b], the we
    can assume that [a] converges.
    Although, it is trivial to prove it by assuming the law of excluded
    middle, a constructive proof is almost as easy and follows directly from the
    definition of [approx].

*)

Lemma ex_approx_assume_hasvalue {p} :
  forall lib ex a b,
    isprogram a
    -> @isprogram p b
    -> (hasvalue_like lib a -> ex_approx lib ex a b)
    -> ex_approx lib ex a b.
Proof.
  introv Hpa Hpb Hha.
  constructor.
  unfold ex_close_comput.
  dands; auto; introv Hcomp.

  - assert (hasvalue lib a) as Xh by (eexists; eauto); sp.
    autodimp Hha hyp; eauto with slow.
    invertsn Hha.
    unfold ex_close_comput in Hha; repnd; eauto.

  - assert (raises_exception lib a) as Xh by (eexists;eauto).
    autodimp Hha hyp; eauto with slow.
    invertsn Hha.
    unfold ex_close_comput in Hha; repnd; eauto.

  - autodimp Hha hyp; eauto 3 with slow.
    invertsn Hha.
    unfold ex_close_comput in Hha; repnd; eauto.
Qed.

(** %\noindent \\*% The following is an easy corollary of the above.

 *)
Corollary bottom_ex_approx_any {p} :
  forall lib ex t, @isprogram p t -> ex_approx lib ex mk_bottom t.
Proof.
  introv Hpr.
  apply ex_approx_assume_hasvalue; auto.

  introv Hv.
  unfold hasvalue_like in Hv; exrepnd.
  apply not_bot_reduces_to_is_value_like in Hv1; tcsp.
Qed.

Lemma ntseq_reduces_to {p} :
  forall lib s t,  reduces_to lib (@mk_ntseq p s) t -> (mk_ntseq s) = t.
Proof.
  introv red.
  apply reduces_to_if_isvalue_like in red; simpl; eauto 3 with slow.
Qed.

Lemma computes_to_exception_and_seq_false {p} :
forall (lib : library) (en a v : @NTerm p) (s: ntseq),
  (a =e>(en, lib)v) -> (a =s>(lib)s) -> False.
Proof.
  introv ce cs.
  unfold computes_to_seq in cs; repnd.
  unfold computes_to_exception in ce; repnd.
  apply reduces_to_or with (u := mk_exception en v) in cs; auto.
  destruct cs as [r|r].
  + apply reduces_to_exception in r; subst; sp.
    invert r.
  + apply ntseq_reduces_to in r. invert r.
Qed.

(** %\noindent \\*%Terms that compute to exception(ex,_) 
    approximate with [ex_approx] any term.
*)
Lemma computes_to_exception_ex_approx_any {p} :
  forall lib ex te e t, @isprogram p te
                        -> isprogram t
                        -> (te =e>(ex,lib) e) 
                        -> ex_approx lib ex te t.
Proof.
  introv Hpr Jpr comp.
  constructor.
  unfold ex_close_comput.
  dands; auto.
  - unfold close_compute_val; intros. 
    eapply computes_to_value_and_exception_false in comp. destruct comp. eauto.
  - unfold ex_close_compute_exc. intros. left. left.
    pose proof @computes_to_exception_eq p lib ex a te e e0 comp H.
    exrepnd. subst. apply ex_approx_refl. apply preserve_program_exc2 in comp; exrepnd; auto.
 - unfold close_compute_seq. introv scomp.
    eapply computes_to_exception_and_seq_false in comp. destruct comp. eauto.
Qed.

(**

  Because in the PER semantics, Nuprl's types are defined as partial
  equivalence relations on closed terms, we define a closed version of
  [ex_approx] as follows:

 *)

Definition ex_approxc {p} lib ex (a b : @CTerm p) :=
  ex_approx lib ex (get_cterm a) (get_cterm b).

Lemma ex_approx_relates_only_progs {p} :
  forall lib (ex a b : @NTerm p), ex_approx lib ex a b -> isprogram a # isprogram b.
Proof.
  intros. invertsn X. repnud X; sp.
Qed.

Lemma ex_approxc_assume_hasvalue {p} :
  forall (lib : @library p) ex a b,
    (hasvalue_likec lib a -> ex_approxc lib ex a b)
    -> ex_approxc lib ex a b.
Proof.
  destruct a; destruct b; unfold hasvaluec, approxc; allsimpl; sp.
  apply ex_approx_assume_hasvalue; sp; allrw @isprogram_eq; sp.
Qed.

Lemma hasvalue_as_ex_approx {o} :
  forall lib ex (a : @NTerm o),
    isprogram a
    -> (hasvalue lib a
        <=>
        ex_approx lib ex mk_axiom (mk_cbv a nvarx mk_axiom)).
Proof.
  introv isp; split; intro k.

  - constructor.
    unfold ex_close_comput; dands; tcsp.

    + apply isprogram_cbv; sp.
      rw @nt_wf_eq; sp.

    + introv comp.
      exists ([] : list (@BTerm o)).
      apply computes_to_value_isvalue_eq in comp; dands; auto;
      inversion comp; subst; fold_terms;
      fold (@mk_axiom o); GC; tcsp.
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
    unfold ex_close_comput in c; repnd.
    pose proof (c2 NAxiom []) as h.
    allfold (@mk_axiom o).
    autodimp h hyp.
    + apply computes_to_value_isvalue_refl; sp.
    + exrepnd.
      inversion h0 as [? imp]; allsimpl; cpx.
      allfold (@mk_axiom o).
      assert (hasvalue lib (mk_cbv a nvarx mk_axiom)) as hv.
      * unfold hasvalue.
        exists (@mk_axiom o); sp.
      * apply if_hasvalue_cbv0 in hv; sp.
        rw @isprog_eq; sp.
Qed.

Lemma hasvaluec_as_ex_approxc {p} :
  forall lib ex a,
    hasvaluec lib a
    <=>
    ex_approxc lib ex mkc_axiom (mkc_cbv a nvarx (@mkcv_axiom p nvarx)).
Proof.
  destruct a; unfold hasvaluec, approxc; simpl.
  apply hasvalue_as_ex_approx.
  allrw @isprogram_eq; sp.
Qed.



Definition ex_approx_open {p} lib ex := olift (@ex_approx p lib ex).
Definition ex_approx_open_bterm {p} lib ex := blift (@ex_approx_open p lib ex).
Definition ex_approx_bts {p} lib ex := lblift (@ex_approx_open p lib ex).

Lemma ex_approx_open_refl {p} :
  forall lib (ex nt: @NTerm p), (nt_wf nt) -> ex_approx_open lib ex nt nt.
Proof.
  induction nt as [v|f| op bts Hind] using NTerm_better_ind; intros Hwf;
  constructor; try split; auto; intros  ? Hcl Hisp ?; apply ex_approx_refl; auto.
Qed.
Hint Resolve approx_open_refl: slow.

Lemma ex_close_comput_mon {p} :
  forall lib ex l r,
    le_bin_rel l r
    -> le_bin_rel (@ex_close_comput p lib ex l) (ex_close_comput lib ex r).
Proof.
  intros lib ex t1 t2 ra rb Hcl Hrab.
  allunfold @ex_close_comput. repnd.
  dands; auto; introv comp.

  - apply Hrab2 in comp.
    parallel tr_subterms Hrelbt.
    repnd.
    split;auto.
    eapply le_lblift2;[|eauto]; eauto 3 with slow.

  - apply Hrab3 in comp; exrepnd.
    destruct comp; exrepnd.
    left. auto. right.
    exists a' e'; dands; auto.

  - apply Hrab4 in comp; exrepnd.
    exists f'; dands; auto.
Defined.


Lemma le_bin_rel_ex_approx {p} :
  forall lib ex l r,
  le_bin_rel l r
  -> le_bin_rel (@ex_approx_aux p lib ex l) (ex_approx_aux lib ex r).
Proof.
  cofix. introv Hle HH.
  invertsn HH.
  constructor.
  eapply ex_close_comput_mon; eauto.
  apply le_bin_rel_or; auto.
Qed.


Lemma respects_alpha_r_ex_approx_aux_bot2 {p} :
  forall lib ex, respects_alpha_r (@ex_approx_aux p lib ex bot2).
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
  unfold ex_close_comput; dands; auto.

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

  - clear cv; allunfold @ex_close_compute_exc;
    introv ca.
    apply ce in ca; exrepnd; clear ce.
    repdors; try (complete (allunfold @bot2; sp)). right. exrepnd.
    repdors; try (complete (allunfold @bot2; sp)).
    eapply compute_to_exception_alpha with (t1' := e') in aeq;
      eauto 3 with slow; exrepnd.
    exists a'0 t2'; dands; auto; left.
    + apply (IND _ _ _ _ a'0) in ca1; auto.
    + apply (IND _ _ _ _ t2') in ca3; auto.

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

Lemma respects_alpha_r_ex_approx_aux_bot2_or_bot2 {p} :
  forall lib ex, respects_alpha_r (@ex_approx_aux p lib ex bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_r_ex_approx_aux_bot2 _ _ _ _ b') in ap; auto.
Qed.

Lemma respects_alpha_l_ex_approx_aux_bot2 {p} :
  forall lib ex, respects_alpha_l (@ex_approx_aux p lib ex bot2).
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
  unfold ex_close_comput; dands; auto.

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

  - clear cv; allunfold @ex_close_compute_exc;
    introv ca.
    applydup @alpha_prog_eauto in aeq as ispa'; auto.
    apply alpha_eq_sym in aeq.
    eapply compute_to_exception_alpha with (t1' := e) in aeq;
      eauto 3 with slow; exrepnd.
    apply ce in aeq0; exrepnd; clear ce.
    destruct aeq0.
    + left. repdors; try (complete (allunfold @bot2; sp));  left.
      apply (IND _ _ _ _ a0) in s0; auto. apply alpha_eq_sym; auto.
    + right. exrepnd. repdors; try (complete (allunfold @bot2; sp)).
      exists a'1 e'; dands; auto; left.
    * apply (IND _  _ _ _ a0) in s1. auto.
      apply alpha_eq_sym; auto.
    * apply (IND _ _ _ _ e) in s3; auto.
      apply alpha_eq_sym; auto.

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
    left; eapply IND;[apply alpha_eq_sym;eauto|]; auto.
Qed.

Lemma respects_alpha_l_ex_approx_aux_bot2_or_bot2 {p} :
  forall lib ex, respects_alpha_l (@ex_approx_aux p lib ex bot2 \2/ bot2).
Proof.
  introv aeq ap.
  allsimpl; destruct ap as [ap|ap]; auto.
  left.
  apply (respects_alpha_l_ex_approx_aux_bot2 _ _ _ _ a') in ap; auto.
Qed.


Lemma respects_alphal_ex_closed_comput {p} :
  forall lib ex R,
    respects_alpha_l R
    -> respects_alpha_l (@ex_close_comput p lib ex R).
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
    destruct comp0. left. auto. apply alpha_eq_sym in comp2.
    pose proof rR a'0 ex a0 comp2 r; auto.
    exrepnd. right.
    exists a'1 e'; dands; auto.
    + apply alpha_eq_sym in comp2; pose proof rR a'0 a'1 a0; auto.
    + apply alpha_eq_sym in comp1. pose proof rR t2' e' e comp1; auto.

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
Qed.

Lemma ex_approxr_alpha_rw_l_aux {p} :
  forall lib ex r a b a',
    respects_alpha_l (ex_approx_aux lib ex r \2/ r)
    -> @alpha_eq p a a'
    -> ex_approx_aux lib ex r a b
    -> ex_approx_aux lib ex r a' b.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphal_ex_closed_comput; auto.
Qed.

Lemma ex_approx_alpha_rw_l_aux {p} :
  forall lib ex a b a',
    @alpha_eq p a a'
    -> ex_approx lib ex a b
    -> ex_approx lib ex a' b.
Proof.
 unfold ex_approx.
 introv.
 generalize (@respects_alpha_l_ex_approx_aux_bot2_or_bot2 p lib ex).
 revert a b a'.
 exact (ex_approxr_alpha_rw_l_aux lib ex bot2).
Qed.

Lemma respects_alphar_ex_closed_comput {p} :
  forall lib ex R,
    respects_alpha_r R
    -> respects_alpha_r (@ex_close_comput p lib ex R).
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
    apply Hap3 in comp; exrepnd. destruct comp. left. auto. right. exrepnd.
    eapply compute_to_exception_alpha with (t2:=b') in s0; eauto with slow.
    exrepnd.
    exists a'0 t2'; dands; auto.
    + pose proof rR a0 a' a'0 s4; auto.
    + pose proof rR e e' t2' s0; auto.

  - introv comp.
    apply Hap4 in comp; exrepnd.
    eapply computes_to_seq_alpha in comp1;[| |eauto]; eauto 3 with slow; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma ex_approxr_alpha_rw_r_aux {p} :
  forall lib ex r a b b',
    respects_alpha_r (ex_approx_aux lib ex r \2/ r)
    -> @alpha_eq p b b'
    -> ex_approx_aux lib ex r a b
    -> ex_approx_aux lib ex r a b'.
Proof.
  intro r.
  introv rR Hal Hap.
  invertsn  Hap.
  constructor.
  revert Hal Hap.
  apply respects_alphar_ex_closed_comput; auto.
Qed.

Lemma ex_approx_alpha_rw_r_aux {p} :
  forall lib ex a b b',
    @alpha_eq p b b'
    -> ex_approx lib ex a b
    -> ex_approx lib ex a b'.
Proof.
 unfold approx.
 introv.
 generalize (@respects_alpha_r_ex_approx_aux_bot2_or_bot2 p lib ex).
 revert a b b'.
 exact (ex_approxr_alpha_rw_r_aux lib ex bot2).
Qed.

Hint Resolve ex_approx_alpha_rw_r_aux : slowbad.
Hint Resolve ex_approx_alpha_rw_l_aux : slowbad.


Lemma respects_alpha_ex_closed_comput {p} :
  forall lib ex R, respects_alpha R -> respects_alpha (@ex_close_comput p lib ex R).
Proof.
  introv ra.
  destruct ra.
  split.
  - apply respects_alphal_ex_closed_comput; auto.
  - apply respects_alphar_ex_closed_comput; auto.
Qed.
Hint Resolve respects_alpha_ex_closed_comput : respects.

Corollary respects_alpha_ex_approx {p} :
  forall lib ex, respects_alpha (@ex_approx p lib ex).
Proof.
  split; introv; intros; eauto with slowbad.
Qed.
Hint Immediate respects_alpha_ex_approx.
Hint Resolve respects_alpha_ex_approx : respects.

Theorem ex_approx_open_relates_only_wf {p} :
  forall lib ex (t1 t2 : @NTerm p),
    ex_approx_open lib ex t1 t2
    -> nt_wf t1 # nt_wf t2.
Proof.
  introv.
  apply olift_relates_only_wf.
Qed.
Hint Resolve ex_approx_open_relates_only_wf : slow.



(** key helper for lemma 0.6 in annotated paper *)
Theorem ex_approx_open_lsubst {p} :
  forall lib ex a b lvi lvo,
    let sub := @var_ren p lvi lvo in
    ex_approx_open lib ex a b
    -> ex_approx_open lib ex (lsubst a sub) (lsubst b sub).
Proof.
  simpl. intros. apply olift_vars_lsubst; eauto with respects.
Qed.

Lemma ex_approx_open_alpha_rw_l_aux {p} :
  forall lib ex a b a',
  @alpha_eq p a a'
  -> ex_approx_open lib ex a b
  -> ex_approx_open lib ex a' b.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold ex_approx_open.
  rwg Hal. trivial.
Qed.

Lemma ex_approx_open_alpha_rw_r_aux {p} :
  forall lib ex a b b',
  @alpha_eq p b b'
  -> ex_approx_open lib ex a b
  -> ex_approx_open lib ex a b'.
Proof.
  introv Hal HH. apply alpha_eq_sym in Hal.
  unfold ex_approx_open.
  rwg Hal. trivial.
Qed.

Hint Resolve ex_approx_open_alpha_rw_l_aux : slowbad.
Hint Resolve ex_approx_open_alpha_rw_r_aux : slowbad.


Hint Resolve alphaeqbt_numbvars : slow.




(** this lemma can simplify many proofs a lot
    e.g. ex_approx_trans, some lemma at the beginning of cequiv.
    whenever we destruct 2 lblift we get 2 sets
    of variables and this lemma helps us inify the,*)


Lemma ex_approxbtd_change2 {p} : forall lib ex bt1 bt2 (lvn lva: list NVar),
  ex_approx_open_bterm lib ex bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ ex_approx_open lib ex nt1' nt2'
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
  unfold ex_approx_open in Hab0.
  rwhg hyp0 Hab0.
  rwhg hyp2 Hab0.
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  split; spc;[|].
  - apply ex_approx_open_lsubst;sp.
  - disjoint_reasoningv; rw @boundvars_lsubst_vars; spc; disjoint_reasoningv.
Qed.

Lemma ex_approxbtd_change {p} : forall lib ex bt1 bt2 (lvn : list NVar),
  ex_approx_open_bterm lib ex bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2) 
  ->  {nt1',nt2' : @NTerm p $ ex_approx_open lib ex nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # disjoint ((bound_vars nt1') ++ (bound_vars nt2')) lvn

   }.
Proof. intros.  apply ex_approxbtd_change2 with (lva:= []); spc.
Qed.

Lemma ex_approxbtd {p} : forall lib ex bt1 bt2 lva,
  ex_approx_open_bterm lib ex bt1 bt2
  -> {lvn : (list NVar) & {nt1',nt2' : @NTerm p $ ex_approx_open lib ex nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # no_repeats lvn
          (* # disjoint lvn (all_vars (get_nt bt1) ++ all_vars (get_nt bt2)) *)
          # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva   } }.
Proof.
  introv Hab.
  pose proof (fresh_vars (num_bvars bt1) 
      (free_vars_bterm bt1  ++ free_vars_bterm bt2 ++ lva)  ).
  exrepnd. apply @ex_approxbtd_change2 with (lvn := lvn) (lva:=lva) in Hab;spc;
      [| disjoint_reasoningv].
  exrepnd.
  exists lvn nt1' nt2';spc.
  disjoint_reasoningv.
Qed.

Hint Resolve lsubst_alpha_congr2: slow.
Hint Resolve alpha_eq_sym: slow.
Hint Resolve alpha_eq_trans: slow.
Hint Rewrite @alphaeq_preserves_free_vars : slow.


Lemma ex_approx_alpha_rw_l {p} : forall lib ex a b a',
  @alpha_eq p a a'
  -> (ex_approx lib ex a b <=> ex_approx lib ex a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.

Lemma ex_approx_alpha_rw_r {p} : forall lib ex a b a',
  @alpha_eq p a a'
  -> (ex_approx lib ex b a <=> ex_approx lib ex b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; introv Hyp; eauto with slowbad.
Qed.


Lemma remove_bot_ex_approx {p} :
  forall lib ex, eq_bin_rel (ex_approx_aux lib ex bot2 \2/ bot2) (@ex_approx p lib ex).
Proof. unfold eq_bin_rel, le_bin_rel. split; eauto;[].
  introv Hp. dorn Hp; eauto. repnud Hp.
  allsimpl. contradiction.
Qed.

Hint Resolve remove_bot_ex_approx.

Lemma clearbots_olift {p} : forall lib ex nt1 nt2,
  (@olift p (ex_approx_aux lib ex bot2 \2/ bot2)) nt1 nt2
 <=> ex_approx_open lib ex nt1 nt2.
Proof.
  introv.
  destruct (@eq_blift_olift p _ _ (remove_bot_ex_approx lib ex)).
  unfold le_bin_rel in l. unfold le_bin_rel in l0.
  unfold ex_approx_open.
  split; auto.
Qed.

Lemma ex_clearbot_relbt {p} : forall lib ex (l1bt l2bt : list (@BTerm p)),
 lblift (olift (ex_approx_aux lib ex bot2 \2/ bot2)) l1bt l2bt
  -> lblift (olift (ex_approx lib ex)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_ex_approx.
Qed.
Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: alphaeqbt.



(** %\noindent% Now, we wish to prove that [ex_approx] is transitive.
    The proof is essentially a co-indictive argument.
    However, to get a strong enough co-induction hypothesis
    when we formalize the proof using the [ex_approx_acc] lemma above,
    we have to state it in a more general way.
    Intuitively, this is because, alpha equality is
    baked into the definition of [blift].
*)

Lemma ex_approx_trans_aux {p} :
  forall lib ex a b c a' c',
    alpha_eq a a'
    -> @alpha_eq p c c'
    -> ex_approx lib ex a' b
    -> ex_approx lib ex b c'
    -> ex_approx lib ex a c.
Proof.
  introv aa cc.
  pose proof
  (ex_approx_acc lib ex (fun a c => { b,a',c' : NTerm $
       alpha_eq a a' # alpha_eq c c' # ex_approx lib ex a' b # ex_approx lib ex b c'   })
     (@bot2 p) ) as HH.
  allsimpl.
  match goal with
  [ HH : _ -> ?B |- _ ] => assert B; [|
    intros; eapply X; eexists; eexists; eexists; eauto;fail]
  end.
  apply HH.
  intros.
  rename x0 into ax.
  rename x1 into cx.
  rename PR into HCCCC.
  exrepnd.
  rename HCCCC1 into Hala.
  rename HCCCC2 into Halc.
  rename HCCCC3 into Hab.
  rename HCCCC0 into Hbc.
  apply (ex_approx_alpha_rw_l _ _ _ _ _ Hala) in Hab; eauto.
  apply (ex_approx_alpha_rw_r _ _ _ _ _ Halc) in Hbc; eauto.
  clear Hala Halc.
  invertsn Hab.
  invertsn Hbc.
  constructor.
  unfold ex_close_comput in Hab at 1.
  unfold ex_close_comput in Hbc at 1.
  unfold ex_close_comput at 1; dands; spcf.

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

    unfold ex_approx_open in H2rb1.
    rwhg H2c0 H2rb1.
    rwhg H2c2 H2rb1.

    unfold ex_approx_open in H1rb1.
    rwhg H1c0 H1rb1.
    rwhg H1c2 H1rb1.

    rename H2rb1 into H2ap.
    rename H1rb1 into H1ap.

    clear H1c0 H1c2 H2c0 H2c2.

    apply ex_approx_open_lsubst with (lvi:=lv) (lvo:=lvn) in H1ap.
    apply ex_approx_open_lsubst with (lvi:=lv0) (lvo:=lvn) in H2ap.
    unfold ex_approx_open in H2ap.
    rwhg Hlink H2ap.
    assert(ex_approx_open lib ex (lsubst nt2n0 (var_ren lv0 lvn))
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
    clear lv0 nt0 nt1 nt2 nt3 nt1n nt2n nt1n0 nt2n0.
    clear Hcb0.
   clear  tr_subterms0 c0.

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
    clear Hab2 Hbc2 Hab Hbc Hbc4 Hab4 HH.
    introv ce.
    allunfold @ex_close_compute_exc.
    applydup Hab3 in ce. destruct ce0;exrepnd;repdors; try (complete (allunfold @bot2; sp)).
    + left. left. pose proof @le_bin_rel_ex_approx p lib ex bot2 r as X. apply X.
      introv xx. destruct xx. auto.
    + applydup Hbc3 in s0; repdors; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    * left. right.
      generalize (CIH a0 ex); intro k.
       autodimp k hyp.
      exists a'1 a0 ex. dands; auto.
    * right.
      exists a'2 e'0; dands; auto; right.
     { generalize (CIH a0 a'2); intro k.
       autodimp k hyp.
      exists a'1 a0 a'2. dands; auto.
     }
      { generalize (CIH e e'0); intro k.
       autodimp k hyp.
      exists e' e e'0. dands; auto.
     }

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
    apply CIH; auto.
    exists (f' n) (f n) (f'0 n); dands; auto.
Qed.


Corollary ex_approx_trans {p} :
  forall lib (ex a b c : @NTerm p),
    ex_approx lib ex a b
    -> ex_approx lib ex b c
    -> ex_approx lib ex a c.
Proof.
 intros. eapply ex_approx_trans_aux; eauto with slow.
Qed.

Lemma ex_approx_wf_term {p} :
  forall lib (ex a b : @NTerm p),
    ex_approx lib ex a b -> wf_term a # wf_term b.
Proof.
  intros. inversion X; subst.
  unfold ex_close_comput in X0; sp; subst; allunfold @isprogram; sp; allrw @nt_wf_eq; sp.
Qed.

Lemma ex_approx_isprog {p} :
  forall lib (ex a b : @NTerm p),
    ex_approx lib ex a b -> isprog a # isprog b.
Proof.
  intros. inversion X; subst.
  unfold ex_close_comput in X0; sp; allrw @isprog_eq; sp.
Qed.

Lemma ex_approxc_refl {p} :
  forall lib ex (t : @CTerm p), ex_approxc lib ex t t.
Proof.
  intro; destruct t; unfold ex_approxc; simpl.
  apply ex_approx_refl; allrw @isprogram_eq; sp.
Qed.

Lemma ex_approxc_trans {p} :
  forall lib ex (t1 t2 t3 : @CTerm p),
    ex_approxc lib ex t1 t2 -> ex_approxc lib ex t2 t3 -> ex_approxc lib ex t1 t3.
Proof.
  intro; destruct t1, t2, t3; unfold ex_approxc; simpl.
  apply ex_approx_trans.
Qed.


Lemma ex_approx_canonical_form {p} :
  forall lib ex t t' op bterms,
    computes_to_value lib t (oterm (Can op) bterms)
    -> ex_approx lib ex t t'
    -> {bterms' : list (@BTerm p) &
         computes_to_value lib t' (oterm (Can op) bterms')
         # lblift (ex_approx_open lib ex) bterms bterms' }.
Proof.
  intros ? ? ? ? ? ? Hcomp Hap.
  invertsn Hap. repnud Hap.
  apply Hap2 in Hcomp. exrepnd.

  apply ex_clearbot_relbt in Hcomp0.
  eexists; eauto with slow.
Qed.


Lemma ex_exception_approx {p} :
  forall lib ex t t' a e,
    (t =e>( a, lib)e)
    -> ex_approx lib ex t t'
    -> ex_approx_aux lib ex bot2 a ex + 
       { a' : @NTerm p &
       { e' : @NTerm p &
         ( t' =e>( a', lib)e')
         # (ex_approx_aux lib ex bot2 a a'[+]bot2 a a')
         # (ex_approx_aux lib ex bot2 e e'[+]bot2 e e') }}.
Proof.
  introv Hcomp Hap.
  invertsn Hap. repnud Hap.

  apply Hap3 in Hcomp. exrepnd.
  destruct Hcomp; [left; repdors; auto; destruct s | right; exrepnd ].
  exists a' e'. split. auto. split; auto.
Qed.

Lemma ex_approx_comput_functionality_left {p} :
  forall lib ex a a' b,
    @reduces_to p lib a a'
    -> ex_approx lib ex a b
    -> ex_approx lib ex a' b.
Proof.
  intros ? ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold ex_close_comput. applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2.
    allunfold @computes_to_value.
    repnd; dands; auto.
    apply @reduces_to_trans with (b:=a'); auto.

  - apply Hap3.
    apply @reduces_to_computes_to_exception with (b := a'); auto.

  - apply Hap4.
    eapply reduces_to_trans; eauto.
Qed.


Lemma ex_approx_comput_functionality_right {p} :
  forall lib ex a b b',
    @reduces_to p lib b b'
    -> ex_approx lib ex a b
    -> ex_approx lib ex a b'.
Proof.
  intros ? ? ? ? ? Hred Hap. invertsn Hap. constructor. repnud Hap.
  unfold ex_close_comput. applydup @reduces_to_preserves_program in Hred; auto.
  dands; tcsp; introv comp.

  - apply Hap2 in comp. exrepnd. exists tr_subterms.
    split; auto.
    apply reduces_to_value_eq with (t:=b); auto.

  - apply Hap3 in comp; exrepnd; repdors; try (complete (allunfold @bot2; sp)).
    exrepnd. right.
    exists a' e'; dands; auto.
    apply reduces_to_exception_eq with (t := b); auto.

  - apply Hap4 in comp; exrepnd.
    exists f'; dands; auto.
    eapply reduces_to_isvalue_like_eq; eauto 3 with slow.
Qed.


Lemma approxc_implies_ex_approxc {p} :
  forall lib ex t t',
  @approxc p lib t t' -> ex_approxc lib ex t t'.
Proof.
  intros. unfold ex_approxc. apply approx_implies_ex_approx.
  auto.
Qed.

Lemma hasvalue_ex_approx {p} :
  forall lib ex t u,
    @ex_approx p lib ex t u
    -> hasvalue lib t
    -> hasvalue lib u.
Proof.
  unfold hasvalue; introv ap hvt; exrepd.
  inversion ap as [cc]; subst.
  unfold ex_close_comput in cc; repnd.
  applydup @computes_to_value_can in c; repndors; exrepd; subst.
  - apply cc2 in c; sp.
    exists (oterm (Can c1) tr_subterms); sp.
  - unfold computes_to_value in c; repnd.
    apply cc4 in c0; exrepnd.
    unfold computes_to_value.
    eexists; dands; eauto 3 with slow.
Qed.


Lemma not_axiom_ex_approx_bot {pp} :
  forall lib ex, !@ex_approx pp lib ex mk_axiom mk_bot.
Proof.
  introv ap.
  inversion ap as [cc]; subst.
  unfold ex_close_comput in cc; repnd.
  generalize (cc2 NAxiom []); intro h.
  dest_imp h hyp; sp.
  apply computes_to_value_isvalue_refl; sp.
  inversion p; allsimpl; cpx.
  inversion p0.
  allfold @mk_axiom.
  apply not_bot_reduces_to_value in H; sp.
Qed.

Lemma not_axiom_ex_approxc_bot {p} :
  forall lib ex, !@ex_approxc p lib ex mkc_axiom mkc_bot.
Proof.
  unfold ex_approxc, mkc_axiom, mkc_bot; simpl.
  apply not_axiom_ex_approx_bot.
Qed.

Hint Resolve ex_approx_open_relates_only_wf : slow.

Lemma ex_approxbt_btwf {p} :
  forall lib ex, le_bin_rel (ex_approx_open_bterm lib ex) (fun b1 b2 => @bt_wf p b1 # bt_wf b2).
Proof.
  introv Hapb.
  repnud Hapb.
  repnud Hapb.
  exrepnd.
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb2)).
  rw  (alphaeqbt_preserves_wf _ _ (alpha_eq_bterm_sym _ _ Hapb0)).
  rw @bt_wf_iff.
  rw @bt_wf_iff.

  eapply ex_approx_open_relates_only_wf; eauto.
Qed.

Theorem ex_approx_implies_ex_approx_open {p} :
  forall lib ex t1 t2,
    @ex_approx p lib ex t1 t2
    -> ex_approx_open lib ex t1 t2.
Proof.
  introv Hap. applydup @ex_approx_relates_only_progs in Hap.
  repnd. unfold ex_approx_open, olift. dands; eauto 2 with slow.
  introv Hwf H1p H2p.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap1.
  apply @lsubst_on_closed_term with (sub:=sub) in Hap0.
  rwg Hap0.
  rwg Hap1.
  trivial.
Qed.


Theorem ex_approx_open_ex_approx {p} :
  forall lib ex t1 t2,
    isprogram t1
    -> @isprogram p t2
    -> ex_approx_open lib ex t1 t2
    -> ex_approx lib ex t1 t2.
Proof.
  introv H1pr H2pr Hol.
  invertsna Hol Hol.
  exrepnd.
  assert (@wf_sub p [])  as Hwf by (apply sub_range_sat_nil).
  apply Hol0 in Hwf;allrw @lsubst_nil; auto.
Qed.

Hint Resolve computes_to_value_isvalue_refl computes_to_value_isvalue_eq : slow.
Hint Constructors isvalue : slow.

Lemma ex_approx_canonical_form2 {p} :
  forall lib ex op bterms1 bterms2,
    ex_approx lib ex (oterm (@Can p op) bterms1) (oterm (Can op) bterms2)
    -> lblift (ex_approx_open lib ex) bterms1 bterms2.
Proof.
  introv Hap. applydup @ex_approx_relates_only_progs in Hap. repnd.
  eapply ex_approx_canonical_form in Hap; exrepnd; eauto with slow.
  apply computes_to_value_isvalue_eq in Hap3;
  inverts Hap3; eauto with slow.
Qed.

Lemma ex_clearbot_relbt2 {p} : forall lib ex (l1bt l2bt : list (@BTerm p)),
  lblift (olift (ex_approx lib ex)) l1bt l2bt
  ->lblift (olift (ex_approx_aux lib ex bot2 \2/ bot2)) l1bt l2bt.
Proof.
  introv.
  apply le_lblift.
  apply le_olift.
  apply remove_bot_ex_approx.
Qed.


Lemma blift_ex_approx_open_nobnd {p} :
  forall lib ex  nt1 nt2,
    blift (ex_approx_open lib ex) (nobnd nt1) (@nobnd p nt2)
    -> isprogram nt1
    -> isprogram nt2
    -> ex_approx lib ex nt1 nt2.
Proof.
  introv Hrel H1pr H2pr.
  unfold blift in Hrel. exrepnd.
  apply alphaeqbt_nilv3 in Hrel0; exrepnd; subst.
  apply alphaeqbt_nilv3 in Hrel2; exrepnd; subst. GC.
  apply ex_approx_open_ex_approx;  eauto 2 with slow.
  unfold ex_approx_open.
  rwg Hrel2.
  rwg Hrel0.
  trivial.
Qed.


Lemma blift_ex_approx_open_nobnd2 {p} :
  forall lib ex nt1 nt2,
    isprogram nt1
    -> @isprogram p nt2
    -> ex_approx lib ex nt1 nt2
    -> blift (ex_approx_open lib ex) (nobnd nt1) (nobnd nt2).
Proof.
  introv Hap H1pr H2pr.
  unfold blift. exists ([]: list NVar) nt1 nt2.
  dands; try (apply alphaeqbt_refl);[].
  apply ex_approx_implies_ex_approx_open; sp.
Qed.

Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.




Ltac ex_prove_program :=
  allunfold isprogram; repnd; try(split;sp;fail);
 (
  match goal with
  | [ |- isprogram ?t] =>
    match goal with
    | [ H: ex_approx _ _ t ?t2 |- _] => apply ex_approx_relates_only_progs in H; repnd;sp
    | [ H: ex_approx _ _ ?t2 t |- _ ] => apply ex_approx_relates_only_progs in H; repnd;sp
    end
  end
  ).

Lemma ex_approx_open_trans {p} :
  forall lib ex (a b c : @NTerm p),
    ex_approx_open lib ex a b
    -> ex_approx_open lib ex b c
    -> ex_approx_open lib ex a c.
Proof.
  intro lib. intro ex.
  apply olift_trans; revert ex; revert lib.
  - exact ex_approx_trans.
  - exact respects_alpha_ex_approx.
Qed.
Hint Resolve ex_approx_open_trans: slow approx_open_trans.


(* =======================================================================
   below here, I haven't changed from lemmas about approx to lemmas about
   ex_approx.
  ========================================================================
*)

Definition simpl_olift {p} R (t1 t2: @NTerm p) :=
  nt_wf t1
  # nt_wf t2
  # forall sub,
      prog_sub sub
      -> isprogram (lsubst t1 sub)
      -> isprogram (lsubst t2 sub)
      -> R (lsubst t1 sub) (lsubst t2 sub).

(*
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
*)

Lemma ex_approx_open_simpler_equiv {p} :
  forall lib a c ex,
    simpl_olift (@ex_approx p lib ex) a c <=> ex_approx_open lib ex a c.
Proof.
  introv.
  split.

  - intro Hos. repnud Hos.
    unfold ex_approx_open, olift.
    dands;auto.
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.
    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    apply (ex_approx_alpha_rw_l _ _ _ _ _ Xtrima).
    apply (ex_approx_alpha_rw_r _ _ _ _ _ Xtrimc).
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



Theorem alpha_implies_ex_approx2 {p} : forall lib ex nt1 nt2,
  @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> ex_approx lib ex nt1 nt2.
Proof.
  introv H2isp Hal.
  apply (ex_approx_alpha_rw_l _ _ _ _ _ Hal).
  apply ex_approx_refl; auto.
Qed.

Theorem alpha_implies_ex_approx3 {p} : forall lib ex nt1 nt2,
  @isprogram p nt1
  -> alpha_eq nt1 nt2
  -> ex_approx lib ex nt1 nt2.
Proof.
  introv H2isp Hal. apply alpha_eq_sym in Hal.
  apply (ex_approx_alpha_rw_r _ _ _ _ _ Hal).
  apply ex_approx_refl; auto.
Qed.

Theorem alpha_implies_ex_approx {p} : forall lib ex nt1 nt2,
  isprogram nt1
  -> @isprogram p nt2
  -> alpha_eq nt1 nt2
  -> ex_approx lib ex nt1 nt2.
Proof.
  intros.
  apply alpha_implies_ex_approx2; auto.
Qed.

Theorem alpha_implies_ex_approx_open {p} :
  forall lib ex nt1 nt2,
  @nt_wf p nt1
  -> alpha_eq nt1 nt2
  -> ex_approx_open lib ex nt1 nt2.
Proof.
  introv H1wf  Hal. repeat(split;[sp|]).
  alpha_hyps Hal;sp.
  introv Hpr H1pr H2pr.
  apply alpha_implies_ex_approx; sp.
  apply lsubst_alpha_congr2;sp.
Qed.
Hint Resolve alpha_implies_ex_approx_open : slowbad.


Lemma ex_approx_open_alpha_rw_l {p} : forall lib ex a b a',
  @alpha_eq p a a'
  -> (ex_approx_open lib ex a b <=> ex_approx_open lib ex a' b).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold ex_approx_open.
  split; introv Hyp;
  applydup @ex_approx_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma ex_approx_open_alpha_rw_r {p} : forall lib ex a b a',
  @alpha_eq p a a'
  -> (ex_approx_open lib ex b a <=> ex_approx_open lib ex b a').
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  unfold ex_approx_open.
  split; introv Hyp; 
  applydup @ex_approx_open_relates_only_wf in Hyp; repnd;
  alpha_hyps Hal; alpha_hyps Hal0; 
  alpha_hyps Hal; alpha_hyps Hal0;
  try(rwg Hal); auto;
  try(rwg Hal0); auto.
Qed.

Lemma ex_approx_open_alpha_rw_lr {p} : forall lib ex a b a' b',
  alpha_eq a a'
  -> @alpha_eq p b b'
  -> (ex_approx_open lib ex a b <=> ex_approx_open lib ex a' b').
Proof.
  introv Hala Halb.
  eapply @ex_approx_open_alpha_rw_l with (b:=b) in Hala.
  eapply @ex_approx_open_alpha_rw_r with (b:=a') in Halb.
  dtiffs.
  split; eauto.
Qed.

Ltac prove_wf1 :=
  sp;
 (
  match goal with
  | [ |- nt_wf ?t] =>
    match goal with
    | [ H: ex_approx_open _ _ t ?t2 |- _] => apply ex_approx_open_relates_only_wf in H; repnd;sp
    | [ H: ex_approx_open _ _ ?t2 t |- _ ] => apply ex_approx_open_relates_only_wf in H; repnd;sp
    end
  end
  ).


(* end hide *)

Hint Resolve isprogram_fix  isprogram_apply : slow.



Lemma ex_approx_open_lsubst_congr {p} : forall lib ex ta tb sub,
  @wf_sub p sub
  -> ex_approx_open lib ex ta tb
  -> ex_approx_open lib ex (lsubst ta sub) (lsubst tb sub).
Proof.
  introv Hwf Hap.
  applydup @ex_approx_open_relates_only_wf in Hap.
  repeat(split; [apply lsubst_wf_iff;sp;fail|]).
  intros subo Hwfs H1ps H2pr.
  unfold ex_approx_open in Hap.
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

Lemma ex_approx_canonical_form3 {p} :
  forall lib ex op bterms1 bterms2,
    isprogram (oterm (@Can p op) bterms1)
    -> isprogram (oterm (Can op) bterms2)
    -> lblift (ex_approx_open lib ex) bterms1 bterms2
    -> ex_approx lib ex (oterm (Can op) bterms1) (oterm (Can op) bterms2).
Proof.
  introv H1p H2p Hap. constructor. unfold ex_close_comput.
  dands; eauto; introv comp.

  - apply computes_to_value_isvalue_eq in comp; eauto with slow;[].
    inverts comp.
    eexists; dands; eauto with slow.
    apply ex_clearbot_relbt2; auto.

  - apply can_doesnt_raise_an_exception in comp; sp.

(*
  - apply can_doesnt_mark in comp; sp.
*)

  - apply reduces_to_if_isvalue_like in comp; eauto 3 with slow; ginv.
Qed.

Lemma ex_approx_canonical_form_exc {o} :
  forall lib ex a1 a2 (e1 e2 : @NTerm o),
    ex_approx lib ex a1 a2
    -> ex_approx lib ex e1 e2
    -> ex_approx lib ex (mk_exception a1 e1) (mk_exception a2 e2).
Proof.
  introv ap1 ap2.
  applydup @ex_approx_relates_only_progs in ap1; repnd.
  applydup @ex_approx_relates_only_progs in ap2; repnd.
  constructor.
  unfold ex_close_comput.
  dands; eauto; try (rw @isprogram_exception_iff; tcsp); introv comp.

  - apply computes_to_value_exception in comp; sp.

  - right;
    apply computes_to_exception_exception in comp; repnd; subst.
    exists a2 e2; dands; auto.
    apply computes_to_exception_refl.

(*
  - apply exception_doesnt_mark in comp; sp.
*)

  - apply reduces_to_exception in comp; eauto 3 with slow; ginv.
Qed.


(* begin hide *)

Lemma ex_approx_decomp_approx {p} :
  forall lib ex a b c d,
    ex_approx lib ex (mk_approx a b) (@mk_approx p c d)
    <=> ex_approx lib ex a c # ex_approx lib ex b d.
Proof.
  split; unfold mk_approx; introv Hyp.
  - applydup @ex_approx_relates_only_progs in Hyp. repnd.
    apply ex_approx_canonical_form2 in Hyp.
    unfold lblift in Hyp. repnd. allsimpl.
    alpharelbtd. GC.
    eapply blift_ex_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_ex_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd. applydup @ex_approx_relates_only_progs in Hyp. repnd.
    applydup @ex_approx_relates_only_progs in Hyp0. repnd.
    apply ex_approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_ex_approx_open_nobnd2; sp.
Qed.

Lemma ex_approxbt_lsubst_prog {p} :
  forall lib ex lv1 lv2 t1 t2,
    isprogram_bt (bterm lv1 t1)
    -> isprogram_bt (bterm lv2 t2)
    -> ex_approx_open_bterm lib ex (bterm lv1 t1) (bterm lv2 t2)
    -> forall lnt,
       length lnt= length lv1
       -> (forall t, LIn t lnt -> @isprogram p t)
       -> ex_approx lib ex (lsubst t1 (combine lv1 lnt)) (lsubst t2 (combine lv2 lnt)).
Proof.
  introv H1p H2p Ha0 Hlen Hlp.
  applydup @blift_numbvars in Ha0.
  unfold num_bvars in Ha1; simpl in Ha1.
  unfold ex_approx_open_bterm in Ha0.
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
  apply ex_approx_open_lsubst with (lvi:=lv) (lvo:=lvn) in Ha0.
  apply alpha_eq_sym in Ha5.
  apply alpha_eq_sym in Ha4.
  unfold ex_approx_open in Ha0.
  rwhg Ha5 Ha0.
  rwhg Ha4 Ha0.

  assert (ex_approx_open lib ex
    (lsubst t1 (var_ren lv1 lvn)) (lsubst t2 (var_ren lv2 lvn)))
   as XX by auto. (** alpha replacement *)
  unfold ex_approx_open in XX.
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
Ltac prove_ex_approx_mk :=
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
    applydup @ex_approx_relates_only_progs in Hceq; repnd;
    applydup @preserve_program in Hcomp as Hcomp0; auto;
    eapply @ex_approx_canonical_form in Hcomp; eauto;
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
    rep_eexists; dands; eauto; apply @ex_approx_open_ex_approx;
    eauto 2 with slow.

(* end hide *)
Lemma ex_approx_mk_pair {p} :
  forall lib ex (t t' a b : NTerm),
    computes_to_value lib t (mk_pair a b)
    -> ex_approx lib ex t t'
    -> {a', b' : @NTerm p $
         computes_to_value lib t' (mk_pair a' b')
         # ex_approx lib ex a a'
         # ex_approx lib ex b b'}.
Proof.
  prove_ex_approx_mk.
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


Lemma ex_approx_exception {p} :
  forall lib ex en (a b : @NTerm p),
    ex_approx lib ex (mk_exception en a) b
    -> (ex_approx lib ex en ex)
       [+]
       {x : NTerm
        & {c : @NTerm p
        & computes_to_exception lib x b c
        # ex_approx lib ex en x
        # ex_approx lib ex a c}}.
Proof.
  introv ap.
  invertsn ap.
  unfold ex_close_comput in ap; repnd.
  generalize (ap3 en a); intro k; autodimp k hyp.
  { apply computes_to_exception_refl. }
  destruct k as [k|k]; exrepnd; GC; tcsp.
  { repndors; tcsp; allunfold @bot2; tcsp. }
  { right; exists a' e'; sp; inversion b0. }
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
