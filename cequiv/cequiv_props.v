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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export cequiv.
Require Export terms3.

Lemma canonical_dec_pair {p} :
  forall x : @CanonicalOp p, {x = NPair} + {x <> NPair}.
Proof.
  introv.
  destruct x;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
Qed.

Lemma nt_wf_NPair_iff {o} :
  forall (bs : list (@BTerm o)),
    nt_wf (oterm (Can NPair) bs)
    <=> {a : NTerm & {b : NTerm & bs = [nobnd a, nobnd b] # nt_wf a # nt_wf b }}.
Proof.
  introv; split; intro h; exrepnd; subst.
  - inversion h as [|? ? imp e]; clear h; subst; allsimpl.
    repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    pose proof (imp (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (imp (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; dands; eauto.
  - constructor; unfold num_bvars; simpl; auto.
    introv i; repndors; subst; tcsp; allrw @bt_wf_iff; auto.
Qed.

Lemma ispair_cases {p} :
  forall lib (t : @NTerm p),
    hasvalue lib t
    -> {a, b : NTerm $ computes_to_value lib t (mk_pair a b)}
       [+] (forall a b, reduces_to lib (mk_ispair t a b) b).
Proof.
  introv hv.
  destruct hv as [ t' c ].
  destruct c as [ red iv ].
  inversion iv as [? isp isc]; subst.
  apply iscan_implies in isc; repndors; exrepnd; subst.

  { destruct (canonical_dec_pair c); subst.

    - left.
      inversion isp as [cl wf]; allsimpl; clear isp.
      allrw @nt_wf_NPair_iff; exrepnd; subst.
      exists a b; constructor; auto.

    - right; introv.
      eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step.
      destruct c; try (complete (simpl; sp)).
  }
Qed.

Lemma ispair_cases_c {p} :
  forall lib (t : @CTerm p),
    hasvaluec lib t
    -> {a, b : CTerm $ computes_to_valc lib t (mkc_pair a b)}
       [+] (forall a b, reduces_toc lib (mkc_ispair t a b) b).
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv.
  unfold computes_to_valc, reduces_toc.
  allsimpl.
  apply ispair_cases in hv; repdors; exrepnd.

  left.
  applydup @preserve_program in hv0; try (complete (allrw @isprogram_eq; sp)).
  rw <- @isprogram_pair_iff in hv1; repnd; allrw @isprogram_eq.
  exists (mk_ct a hv2) (mk_ct b hv1); simpl; sp.

  right.
  introv; destruct_cterms; simpl.
  apply hv.
Qed.

Lemma canonical_dec_inl {p} :
  forall x : @CanonicalOp p, {x = NInj NInl} + {x <> NInj NInl}.
Proof.
  introv.
  destruct x;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
  destruct c;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
Qed.


Lemma isinl_cases {p} :
  forall lib (t : @NTerm p),
    hasvalue lib t
    -> {a : NTerm $ computes_to_value lib t (mk_inl a)}
       [+] (forall a b, reduces_to lib (mk_isinl t a b) b).
Proof.
  introv hv.
  destruct hv as [ t' c ].
  destruct c as [ red iv ].
  dup iv as iv'.
  rw @isvalue_iff in iv'; repnd.
  apply iscan_implies in iv'0; repndors; exrepnd; subst.

  - destruct (canonical_dec_inl c).

    + left.
      subst.
      destruct iv' as [ cl wf ].
      inverts wf as bw eq.
      simpl in eq.
      repeat (destruct bterms; allsimpl; sp).
      apply cons_inj in eq; destruct eq as [ l1 eq ].
      clear eq.
      allunfold @num_bvars.
      destruct b; allsimpl.
      exists n.
      allrw length0; subst.
      constructor; sp.

    + right; introv.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step; csunf; simpl; auto.
      repeat (destruct c; try (complete (simpl; sp))).
Qed.

Lemma isinl_cases_c {p} :
  forall lib (t : @CTerm p),
    hasvaluec lib t
    -> {a : CTerm $ computes_to_valc lib t (mkc_inl a)}
       [+] (forall a b, reduces_toc lib (mkc_isinl t a b) b).
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv.
  unfold computes_to_valc, reduces_toc.
  allsimpl.
  apply isinl_cases in hv; repdors; exrepnd.

  left.
  applydup @preserve_program in hv1; try (complete (allrw @isprogram_eq; sp)).
  rw <- @isprogram_inl_iff in hv0; repnd; allrw @isprogram_eq.
  exists (mk_ct a hv0). simpl; sp.
  right.
  introv; destruct_cterms; simpl.
  apply hv.
Qed.


Lemma canonical_dec_inr {p} :
  forall x : @CanonicalOp p, {x = NInj NInr} + {x <> NInj NInr}.
Proof.
  introv.
  destruct x;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
  destruct c;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
Qed.


Lemma isinr_cases {p} :
  forall lib (t : @NTerm p),
    hasvalue lib t
    -> {a : NTerm $ computes_to_value lib t (mk_inr a)}
       [+] (forall a b, reduces_to lib (mk_isinr t a b) b).
Proof.
  introv hv.
  destruct hv as [ t' c ].
  destruct c as [ red iv ].
  dup iv as iv'.
  rw @isvalue_iff in iv'; repnd.
  apply iscan_implies in iv'0; repndors; exrepnd; subst.

  - destruct (canonical_dec_inr c).

    + left.
      subst.
      destruct iv' as [ cl wf ].
      inverts wf as bw eq.
      simpl in eq.
      repeat (destruct bterms; allsimpl; sp).
      apply cons_inj in eq; destruct eq as [ l1 eq ].
      clear eq.
      allunfold @num_bvars.
      destruct b; allsimpl.
      exists n.
      allrw length0; subst.
      constructor; sp.

    + right; introv.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step; csunf; simpl; auto.
      repeat (destruct c; try (complete (simpl; sp))).
Qed.

Lemma isinr_cases_c {p} :
  forall lib (t : @CTerm p),
    hasvaluec lib t
    -> {a : CTerm $ computes_to_valc lib t (mkc_inr a)}
       [+] (forall a b, reduces_toc lib (mkc_isinr t a b) b).
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv.
  unfold computes_to_valc, reduces_toc.
  allsimpl.
  apply isinr_cases in hv; repdors; exrepnd.

  left.
  applydup @preserve_program in hv1; try (complete (allrw @isprogram_eq; sp)).
  rw <- @isprogram_inr_iff in hv0; repnd; allrw @isprogram_eq.
  exists (mk_ct a hv0). simpl; sp.
  right.
  introv; destruct_cterms; simpl.
  apply hv.
Qed.


Lemma canonical_dec_lambda {p} :
  forall x : @CanonicalOp p, {x = NLambda} + {x <> NLambda}.
Proof.
  introv.
  destruct x;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
Qed.


Lemma islambda_cases {p} :
  forall lib (t : @NTerm p),
    hasvalue lib t
    -> {v : NVar $ {a : NTerm $ computes_to_value lib t (mk_lam v a)}}
       [+] (forall a b, reduces_to lib (mk_islambda t a b) b).
Proof.
  introv hv.
  destruct hv as [ t' c ].
  destruct c as [ red iv ].
  dup iv as iv'.
  rw @isvalue_iff in iv'; repnd.
  apply iscan_implies in iv'0; repndors; exrepnd; subst.

  - destruct (canonical_dec_lambda c).

    + left.
      subst.
      destruct iv' as [ cl wf ].
      inverts wf as bw eq.
      simpl in eq.
      repeat (destruct bterms; allsimpl; sp).
      destruct b as [l b]; allsimpl.
      allunfold @num_bvars; allsimpl.
      repeat (destruct l; allsimpl; ginv).
      exists n b.
      constructor; sp.

    + right; introv.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step; csunf; simpl; auto.
      destruct c; try (complete (simpl; sp)).
Qed.

(* Need islambda_cases_c ?? But first need  (mkc_lambda v a)  and what is it?
   a  covered by [v] ?
*)




Lemma canonical_dec_axiom {p} :
  forall x : @CanonicalOp p, {x = NAxiom} + {x <> NAxiom}.
Proof.
  introv.
  destruct x;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
Qed.


Lemma isaxiom_cases {p} :
  forall lib (t : @NTerm p),
    hasvalue lib t
    -> computes_to_value lib t mk_axiom
       [+] (forall a b, reduces_to lib (mk_isaxiom t a b) b).
Proof.
  introv hv.
  destruct hv as [ t' c ].
  destruct c as [ red iv ].
  dup iv as iv'.
  rw @isvalue_iff in iv'; repnd.
  apply iscan_implies in iv'0; repndors; exrepnd; subst.

  - destruct (canonical_dec_axiom c).

    + left.
      subst.
      destruct iv' as [ cl wf ].
      inverts wf as bw eq.
      simpl in eq.
      repeat (destruct bterms; allsimpl; sp); GC; fold_terms.
      constructor; sp.

    + right; introv.
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step; csunf; simpl; auto.
      destruct c; try (complete (simpl; sp)).
Qed.

Lemma isaxiom_cases_c {p} :
  forall lib (t : @CTerm p),
    hasvaluec lib t
    -> computes_to_valc lib t mkc_axiom
       [+] (forall a b, reduces_toc lib (mkc_isaxiom t a b) b).
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv.
  unfold computes_to_valc, reduces_toc.
  allsimpl.
  apply isaxiom_cases in hv; repdors; exrepnd; auto.
  right.
  introv; destruct_cterms; simpl.
  apply hv.
Qed.


Lemma reduces_to_pi1_pair {p} :
  forall lib (a b : @NTerm p), reduces_to lib (mk_pi1 (mk_pair a b)) a.
Proof.
  introv.
  apply reduces_to_if_step.
  simpl.
  unfold apply_bterm; simpl.
  change_to_lsubst_aux4; simpl; auto.
Qed.
Hint Immediate reduces_to_pi1_pair.

Lemma reduces_to_pi2_pair {p} :
  forall lib (a b : @NTerm p), reduces_to lib (mk_pi2 (mk_pair a b)) b.
Proof.
  introv.
  apply reduces_to_if_step.
  simpl.
  unfold apply_bterm; simpl.
  change_to_lsubst_aux4; simpl; auto.
Qed.
Hint Immediate reduces_to_pi2_pair.

Lemma cequiv_pi1_pair {p} :
  forall lib (a b : @NTerm p),
    isprogram a
    -> isprogram b
    -> cequiv lib (mk_pi1 (mk_pair a b)) a.
Proof.
  introv ipa ipb.
  apply reduces_to_implies_cequiv; sp.
  rw @isprogram_pi1.
  apply isprogram_pair; sp.
Qed.

Lemma cequiv_pi2_pair {p} :
  forall lib (a b : @NTerm p),
    isprogram a
    -> isprogram b
    -> cequiv lib (mk_pi2 (mk_pair a b)) b.
Proof.
  introv ipa ipb.
  apply reduces_to_implies_cequiv.
  - rw @isprogram_pi2;
  apply isprogram_pair; sp.
  - auto.
Qed.

Lemma reduces_to_outl_inl {p} :
  forall lib (a : @NTerm p), reduces_to lib (mk_outl (mk_inl a)) a.
Proof.
  introv.
  apply reduces_to_if_step.
  simpl.
  unfold apply_bterm; simpl.
  change_to_lsubst_aux4; simpl; auto.
Qed.
Hint Immediate reduces_to_outl_inl.

Lemma reduces_to_outr_inr {p} :
  forall lib (a : @NTerm p), reduces_to lib (mk_outr (mk_inr a)) a.
Proof.
  introv.
  apply reduces_to_if_step.
  simpl.
  unfold apply_bterm; simpl.
  change_to_lsubst_aux4; simpl; auto.
Qed.
Hint Immediate reduces_to_outr_inr.

Lemma cequiv_outl_inl {p} :
  forall lib (a : @NTerm p),
    isprogram a
    -> cequiv lib (mk_outl (mk_inl a)) a.
Proof.
  introv ipa.
  apply reduces_to_implies_cequiv; sp.
  rw @isprogram_outl.
  apply isprogram_inl; sp.
Qed.

Lemma cequiv_outr_inr {p} :
  forall lib (a : @NTerm p),
    isprogram a
    -> cequiv lib (mk_outr (mk_inr a)) a.
Proof.
  introv ipa .
  apply reduces_to_implies_cequiv; sp.
  rw @isprogram_outr.
  apply isprogram_inr; sp.
Qed.


(* !! MOVE *)
Lemma resp_cequiv {p} : forall lib, respects2 (cequiv lib) (@cequiv p lib).
Proof.
   split; introv; intros; eauto with slow.
Qed.
Hint Resolve resp_cequiv : respects.

Lemma cequiv_pair {p} :
  forall lib (a b c d : @NTerm p),
    cequiv lib a c
    -> cequiv lib b d
    -> cequiv lib (mk_pair a b) (mk_pair c d).
Proof.
  introv c1 c2.
  applydup @cequiv_isprogram in c1.
  applydup @cequiv_isprogram in c2.
  repnd.
  unfold mk_pair, nobnd.
  repeat prove_cequiv; auto.
Qed.


Hint Resolve alpha_implies_cequiv_open : slow.

Lemma computes_to_pair_eta {p} :
  forall lib (t a b : @NTerm p),
    isprogram t
    -> computes_to_value lib t (mk_pair a b)
    -> cequiv lib t (mk_eta_pair t).
Proof.
  introv isp c.
  apply computes_to_value_implies_cequiv in c; auto.
  applydup @cequiv_isprogram in c; repnd.
  allrw <- @isprogram_pair_iff; repnd; GC.
  apply @cequiv_trans with (b := mk_pair a b); auto.
  unfold mk_eta_pair.
  apply cequiv_pair.
  - assert (cequiv lib (mk_pi1 t) (mk_pi1 (mk_pair a b))) as ceq1.
    unfold mk_pi1, mk_spread, nobnd.
    repeat prove_cequiv; auto;
    try (complete (constructor; sp));
    try (complete (rw <- isprogram_pair_iff; sp)).
    apply alphabt_blift; simpl; dands; (introns XX); allsimpl; exrepnd;
    eauto 2 with slow.

    apply @cequiv_trans with (b := mk_pi1 (mk_pair a b)); auto with slow.
    apply cequiv_sym.
    apply cequiv_pi1_pair; auto.

  - assert (cequiv lib (mk_pi2 t) (mk_pi2 (mk_pair a b))) as ceq1.
    unfold mk_pi2, mk_spread, nobnd.
    repeat prove_cequiv; auto;
    try (complete (constructor; sp));
    try (complete (rw <- isprogram_pair_iff; sp)).
    apply alphabt_blift; simpl; dands; (introns XX); allsimpl; exrepnd;
    eauto 2 with slow.
    apply @cequiv_trans with (b := mk_pi2 (mk_pair a b)); auto with slow.
    apply cequiv_sym.
    apply cequiv_pi2_pair; auto.
Qed.

Lemma computes_to_pair_eta_c {p} :
  forall lib (t a b : @CTerm p),
    computes_to_valc lib t (mkc_pair a b)
    -> cequivc lib t (mkc_eta_pair t).
Proof.
  introv c.
  destruct_cterms.
  unfold computes_to_valc in c.
  unfold cequivc.
  allsimpl.
  apply computes_to_pair_eta with (a := x0) (b := x); auto.
  rw @isprogram_eq; auto.
Qed.

Lemma cequiv_eta_pair {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_eta_pair a) (mk_eta_pair b).
Proof.
  introv c.
  applydup @cequiv_isprogram in c; repnd.
  unfold mk_eta_pair, mk_pair, mk_pi1, mk_pi2, mk_spread, nobnd.
  repeat prove_cequiv; auto;
  try (complete (constructor; sp));
    apply alphabt_blift; simpl; dands; (introns XX); allsimpl; exrepnd;
    eauto 2 with slow.
Qed.

Lemma cequivc_eta_pair {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> cequivc lib (mkc_eta_pair a) (mkc_eta_pair b).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_eta_pair; sp.
Qed.

Lemma cequivc_eta_pair_replace {p} :
  forall lib (t u : @CTerm p),
    cequivc lib t u
    -> cequivc lib t (mkc_eta_pair t)
    -> cequivc lib u (mkc_eta_pair u).
Proof.
  introv c1 c2.
  apply cequivc_trans with (b := t); auto.
  apply cequivc_sym; auto.
  apply cequivc_trans with (b := mkc_eta_pair t); auto.
  apply cequivc_eta_pair; sp.
Qed.

Lemma cequiv_inl {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_inl a) (mk_inl b).
Proof.
  introv c1.
  applydup @cequiv_isprogram in c1.
  repnd.
  unfold mk_inl, nobnd.
  repeat prove_cequiv; auto.
Qed.

Lemma cequiv_inr {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_inr a) (mk_inr b).
Proof.
  introv c1.
  applydup @cequiv_isprogram in c1.
  repnd.
  unfold mk_inr, nobnd.
  repeat prove_cequiv; auto.
Qed.

Lemma computes_to_inl_eta {p} :
  forall lib (t a : @NTerm p),
    isprogram t
    -> computes_to_value lib t (mk_inl a)
    -> cequiv lib t (mk_eta_inl t).
Proof.
  introv isp c.
  apply computes_to_value_implies_cequiv in c; auto.
  applydup @cequiv_isprogram in c; repnd.
  allrw <- @isprogram_inl_iff; repnd; GC.
  apply @cequiv_trans with (b := mk_inl a); auto.
  unfold mk_eta_inl.
  apply cequiv_inl.
  assert (isprogram (@mk_bot p)) as ispbot.
      eauto 3 with slow.
  assert (isprogram_bt (bterm [nvary] (@mk_bot p))).
     destruct ispbot. constructor. constructor. constructor. auto.
  assert (blift (cequiv_open lib) (bterm [nvary] mk_bot) (bterm [nvary] mk_bot)).
   exists [nvary] (@mk_bot p) (@mk_bot p); sp; apply cequiv_open_refl. destruct ispbot. auto.

  
  - assert (cequiv lib (mk_outl t) (mk_outl (mk_inl a))) as ceq1.
    { unfold mk_outl, mk_decide, nobnd.
    repeat prove_cequiv; auto;
    try (complete (constructor; sp));
    try (complete (rw <- isprogram_inl_iff; sp)).
    apply alphabt_blift; simpl; dands; (introns XX); allsimpl; exrepnd;
    eauto 3 with slow. }
    {apply @cequiv_trans with (b := mk_outl (mk_inl a)); auto with slow.
    apply cequiv_sym.
    apply cequiv_outl_inl; auto. }
Qed.

Lemma computes_to_inl_eta_c {p} :
  forall lib (t a : @CTerm p),
    computes_to_valc lib t (mkc_inl a)
    -> cequivc lib t (mkc_eta_inl t).
Proof.
  introv c.
  destruct_cterms.
  unfold computes_to_valc in c.
  unfold cequivc.
  allsimpl.
  apply computes_to_inl_eta with (a := x) ; auto.
  rw @isprogram_eq; auto.
Qed.

Hint Resolve cequiv_open_refl : slow.

Lemma cequiv_eta_inl {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_eta_inl a) (mk_eta_inl b).
Proof.
  introv c.
  applydup @cequiv_isprogram in c; repnd.
  
  assert (isprogram (@mk_bot p)) as ispbot.
  { eauto 3 with slow. }
  assert (isprogram_bt (bterm [nvary] (@mk_bot p))).
  { destruct ispbot. constructor. constructor. constructor. auto. }

  assert (isprogram (mk_decide a nvarx (vterm nvarx) nvary mk_bot)).
   { apply isprogram_decide; auto. destruct ispbot. auto. }
  assert (isprogram (mk_decide b nvarx (vterm nvarx) nvary mk_bot)).
   { apply isprogram_decide; auto. destruct ispbot. auto. }

  unfold mk_eta_inl, mk_decide, mk_outl, nobnd.
  repeat prove_cequiv; auto.
  unfold mk_decide.
  repeat prove_cequiv; auto.
  
  - exists [nvarx] (@vterm p nvarx ) (@vterm p nvarx).
    sp; eauto 3 with slow.

  - exists [nvary] (@mk_bot p) (@mk_bot p).
    sp; eauto 3 with slow.
Qed.

Lemma cequivc_eta_inl {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> cequivc lib (mkc_eta_inl a) (mkc_eta_inl b).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_eta_inl; sp.
Qed.

Lemma cequivc_eta_inl_replace {p} :
  forall lib (t u : @CTerm p),
    cequivc lib t u
    -> cequivc lib t (mkc_eta_inl t)
    -> cequivc lib u (mkc_eta_inl u).
Proof.
  introv c1 c2.
  apply cequivc_trans with (b := t); auto.
  apply cequivc_sym; auto.
  apply cequivc_trans with (b := mkc_eta_inl t); auto.
  apply cequivc_eta_inl; sp.
Qed.


Lemma computes_to_inr_eta {p} :
  forall lib (t a : @NTerm p),
    isprogram t
    -> computes_to_value lib t (mk_inr a)
    -> cequiv lib t (mk_eta_inr t).
Proof.
  introv isp c.
  apply computes_to_value_implies_cequiv in c; auto.
  applydup @cequiv_isprogram in c; repnd.
  allrw <- @isprogram_inr_iff; repnd; GC.
  apply @cequiv_trans with (b := mk_inr a); auto.
  unfold mk_eta_inr.
  apply cequiv_inr.
  assert (isprogram (@mk_bot p)) as ispbot.
      eauto 3 with slow.
  assert (isprogram_bt (bterm [nvarx] (@mk_bot p))).
     destruct ispbot. constructor. constructor. constructor. auto.
  assert (blift (cequiv_open lib) (bterm [nvarx] mk_bot) (bterm [nvarx] mk_bot)).
   exists [nvarx] (@mk_bot p) (@mk_bot p); sp; apply cequiv_open_refl. destruct ispbot. auto.

   - assert (cequiv lib (mk_outr t) (mk_outr (mk_inr a))) as ceq1.
    { unfold mk_outr, mk_decide, nobnd.
      repeat prove_cequiv; auto;
      try (complete (constructor; sp));
        try (complete (rw <- isprogram_inr_iff; sp));
        apply alphabt_blift; simpl; dands; (introns XX); allsimpl; exrepnd;
        eauto 3 with slow. }
    { apply @cequiv_trans with (b := mk_outr (mk_inr a)); auto with slow.
      apply cequiv_sym.
      apply cequiv_outr_inr; auto. }
Qed.

Lemma computes_to_inr_eta_c {p} :
  forall lib (t a : @CTerm p),
    computes_to_valc lib t (mkc_inr a)
    -> cequivc lib t (mkc_eta_inr t).
Proof.
  introv c.
  destruct_cterms.
  unfold computes_to_valc in c.
  unfold cequivc.
  allsimpl.
  apply computes_to_inr_eta with (a := x) ; auto.
  rw @isprogram_eq; auto.
Qed.

Hint Resolve isprog_bottom : slow.
Hint Resolve isprog_vars_if_isprog : slow.

Lemma cequiv_eta_inr {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_eta_inr a) (mk_eta_inr b).
Proof.
  introv c.
  applydup @cequiv_isprogram in c; repnd.
  
  assert (isprogram (@mk_bot p)) as ispbot.
  { eauto 3 with slow. }
  assert (isprogram_bt (bterm [nvary] (@mk_bot p))).
  { apply isprog_vars_isprogrambt; eauto 3 with slow. }

  assert (isprogram (mk_decide a nvarx mk_bot  nvary (vterm nvary) )).
  { apply isprogram_decide; auto. destruct ispbot. auto. }
  assert (isprogram (mk_decide b nvarx mk_bot nvary (vterm nvary)  )).
  { apply isprogram_decide; auto. destruct ispbot. auto. }

  unfold mk_eta_inr, mk_decide, mk_outl, nobnd.
  repeat prove_cequiv; auto.
  unfold mk_decide.
  repeat prove_cequiv; auto.

  - exists [nvarx] (@mk_bot p) (@mk_bot p). 
    sp; eauto 3 with slow.

  - exists [nvary] (@vterm p nvary ) (@vterm p nvary).
    sp; eauto 3 with slow.
Qed.

Lemma cequivc_eta_inr {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> cequivc lib (mkc_eta_inr a) (mkc_eta_inr b).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_eta_inr; sp.
Qed.

Lemma cequivc_eta_inr_replace {p} :
  forall lib (t u : @CTerm p),
    cequivc lib t u
    -> cequivc lib t (mkc_eta_inr t)
    -> cequivc lib u (mkc_eta_inr u).
Proof.
  introv c1 c2.
  apply cequivc_trans with (b := t); auto.
  apply cequivc_sym; auto.
  apply cequivc_trans with (b := mkc_eta_inr t); auto.
  apply cequivc_eta_inr; sp.
Qed.

Lemma cequiv_ispair {p} :
  forall lib (t1 a1 b1 t2 a2 b2 : @NTerm p),
    cequiv lib t1 t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_ispair t1 a1 b1) (mk_ispair t2 a2 b2).
Proof.
  introv c1 c2 c3.
  applydup @cequiv_isprogram in c1.
  applydup @cequiv_isprogram in c2.
  applydup @cequiv_isprogram in c3.
  repnd.
  unfold mk_ispair, mk_can_test, nobnd.
  repeat prove_cequiv; auto.
Qed.

Lemma cequivc_mkc_ispair_of_pair {p} :
  forall lib (t a b : @CTerm p),
    cequivc lib t (mkc_eta_pair t)
    -> cequivc lib (mkc_ispair t a b) a.
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allrw @isprog_eq.
  assert (cequiv lib (mk_ispair x1 x0 x) (mk_ispair (mk_eta_pair x1) x0 x))
         as c' by (apply cequiv_ispair; sp; try (complete (apply cequiv_refl; sp))).
  apply cequiv_trans with (b := mk_ispair (mk_eta_pair x1) x0 x); auto.
  apply reduces_to_implies_cequiv; sp.
  apply isprogram_ispair; sp.
  apply isprogram_eta_pair; sp.
  apply reduces_to_if_step.
  simpl; sp.
Qed.

Lemma cequivc_eq_weak {p} :
  forall lib (a b : @CTerm p), a = b -> cequivc lib a b.
Proof.
  intros; subst; sp.
Qed.

Lemma cequiv_beta2 {p} :
  forall lib v (b a1 a2 : @NTerm p),
    isprog a1
    -> isprog a2
    -> isprog_vars [v] b
    -> cequiv lib (mk_apply2 (mk_lam v b) a1 a2) (mk_apply (subst b v a1) a2).
Proof.
  introv ispa1 ispa2 ispb.
  unfold mk_apply2.
  apply sp_implies_cequiv_apply.
  rw @isprogram_eq; auto.
  apply cequiv_beta; auto.
  rw @isprogram_eq; auto.
Qed.

Lemma cequivc_beta2 {p} :
  forall lib v b (a1 a2 : @CTerm p),
    cequivc lib (mkc_apply2 (mkc_lam v b) a1 a2) (mkc_apply (substc a1 v b) a2).
Proof.
  introv.
  rw @mkc_apply2_eq.
  apply sp_implies_cequivc_apply.
  apply cequivc_beta.
Qed.

Lemma cequiv_beta_isp {p} :
  forall lib v b (a : @NTerm p),
    isprog_vars [v] b
    -> isprog a
    -> cequiv lib (mk_apply (mk_lam v b) a) (subst b v a).
Proof.
  introv ipb ipa.
  apply cequiv_beta; sp.
  apply isprogram_eq; sp.
Qed.

Lemma approx_decomp_equality {p} :
  forall lib (a b c d A B : @NTerm p),
    approx lib (mk_equality a b A) (mk_equality c d B)
    <=> approx lib a c # approx lib b d # approx lib A B.
Proof.
  split; unfold mk_equality; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply approx_canonical_form2 in Hyp.
    unfold lblift in Hyp. repnd. allsimpl.
    alpharelbtd; GC.
    allapply @isprogram_equality_implies; allunfold @nobnd; exrepnd; allsimpl; cpx.
    eapply blift_approx_open_nobnd in Hyp2bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd.
    applydup @approx_relates_only_progs in Hyp. repnd.
    applydup @approx_relates_only_progs in Hyp0. repnd.
    applydup @approx_relates_only_progs in Hyp1. repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      sp; subst; sp; apply implies_isprogram_bt0; eauto with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      sp; subst; sp; apply implies_isprogram_bt0; eauto with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_equality {p} :
  forall lib (a b c d A B : @NTerm p),
    cequiv lib (mk_equality a b A) (mk_equality c d B)
    <=> cequiv lib a c # cequiv lib b d # cequiv lib A B.
Proof.
  intros.
  unfold cequiv.
  rw (approx_decomp_equality lib a b c d A B).
  rw (approx_decomp_equality lib c d a b B A).
  split; sp.
Qed.

Lemma cequivc_decomp_equality {p} :
  forall lib (a b c d A B : @CTerm p),
    cequivc lib (mkc_equality a b A) (mkc_equality c d B)
    <=> cequivc lib a c # cequivc lib b d # cequivc lib A B.
Proof.
  introv; destruct_cterms.
  unfold cequivc, mkc_equality; simpl.
  apply cequiv_decomp_equality.
Qed.

Lemma cequiv_mk_inl_if {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_inl a) (mk_inl b).
Proof.
  allunfold @mk_fix. introv Hc.
  applydup @cequiv_isprogram in Hc. repnd.
  repeat(prove_cequiv); auto.
Qed.

Lemma cequivc_mkc_inl_if {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> cequivc lib (mkc_inl a) (mkc_inl b).
Proof.
  allunfold @mk_inl.
  unfold cequivc.
  introv Hc.
  dest_cterms Hc.
  allsimpl.
  allrw @isprog_eq.
  apply cequiv_mk_inl_if; auto.
Qed.

Lemma cequiv_mk_inr_if {p} :
  forall lib (a b : @NTerm p),
    cequiv lib a b
    -> cequiv lib (mk_inr a) (mk_inr b).
Proof.
  allunfold @mk_fix. introv Hc.
  applydup @cequiv_isprogram in Hc. repnd.
  repeat(prove_cequiv); auto.
Qed.

Lemma cequivc_mkc_inr_if {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> cequivc lib (mkc_inr a) (mkc_inr b).
Proof.
  allunfold @mk_inl.
  unfold cequivc.
  introv Hc.
  dest_cterms Hc.
  allsimpl.
  allrw @isprog_eq.
  apply cequiv_mk_inr_if; auto.
Qed.

Lemma cequivc_mkc_inl_implies {o} :
  forall lib (t a : @CTerm o),
    cequivc lib (mkc_inl a) t
    -> {b : CTerm $ computes_to_valc lib t (mkc_inl b) # cequivc lib a b}.
Proof.
  introv ceq.
  eapply cequivc_mkc_inl; eauto.
  apply computes_to_valc_refl; sp.
  apply iscvalue_mkc_inl.
Qed.

Lemma cequivc_mkc_inr_implies {o} :
  forall lib (t a : @CTerm o),
    cequivc lib (mkc_inr a) t
    -> {b : CTerm $ computes_to_valc lib t (mkc_inr b) # cequivc lib a b}.
Proof.
  introv ceq.
  eapply cequivc_mkc_inr; eauto.
  apply computes_to_valc_refl; sp.
  apply iscvalue_mkc_inr.
Qed.

Lemma cequivc_axiom_implies {o} :
  forall lib (t : @CTerm o),
    cequivc lib mkc_axiom t -> computes_to_valc lib t mkc_axiom.
Proof.
  introv ceq.
  eapply cequivc_axiom; eauto.
  apply computes_to_valc_refl; sp.
Qed.
