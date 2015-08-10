(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export stronger_continuity_defs2.
Require Export cvterm3.


Definition spexccv {o} vs (a : get_patom_set o) : CVTerm vs :=
  mk_cv vs (spexcc a).

Definition bound_nat_c {o} (a : get_patom_set o) x e z (f : @CTerm o) :=
  mkc_lam
    x
    (mkcv_cbv
       [x]
       (mkc_var x)
       x
       (mkcv_dup1
          x
          (mkcv_less
             [x]
             (mkc_var x)
             (mkcv_zero [x])
             (mkcv_vbot [x] z)
             (mkcv_try [x]
                       (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))
                       (mkcv_utoken [x] a)
                       e
                       (spexccv [e,x] a))))).

Lemma get_cterm_bound_nat_c {o} :
  forall (a : get_patom_set o) (x e z : NVar) (f : @CTerm o),
    get_cterm (bound_nat_c a x e z f)
    = bound_nat a x e z (get_cterm f).
Proof. sp. Qed.

Lemma cequivc_mkc_cbv {o} :
  forall lib (t : @CTerm o) x (u : CVTerm [x]),
    iscvalue t
    -> cequivc lib (mkc_cbv t x u) (substc t x u).
Proof.
  introv i.
  destruct_cterms.
  unfold iscvalue in i; allsimpl.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv;[rw @isprogram_eq;apply isprog_cbv;auto|].
  apply reduces_to_if_step.
  applydup @isvalue_implies_iscan in i.
  apply iscan_implies in i2; repndors; exrepnd; subst;
  csunf; simpl; auto.
Qed.

Lemma implies_equal_bound_nat_try_aux_c {o} :
  forall lib a x e z (f g : @CTerm o),
    e <> x
    -> equality lib f g (nat2natE a)
    -> equality lib (bound_nat_try_c a x e z f) (bound_nat_try_c a x e z g) nat2nat.
Proof.
  introv d equ.
  unfold nat2nat.
  unfold nat2natE in equ.
  allrw @equality_in_fun; repnd; dands; tcsp.
  clear equ1 equ0.

  introv en.
  unfold bound_nat_try_c.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].

  repeat (rw @mkcv_cbv_substc_same).
  repeat (rw @mkc_var_substc).
  allrw @mkcv_cont1_dup1.

  apply equality_in_tnat in en.
  unfold equality_of_nat in en; exrepnd; spcast.
  pose proof (equ (mkc_nat k) (mkc_nat k)) as eqn.
  autodimp eqn hyp.
  { apply equality_in_tnat; unfold equality_of_nat.
    exists k; dands; spcast; apply computes_to_valc_refl;
    eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply simpl_cequivc_mkc_cbv;
      apply cequivc_sym;
      apply computes_to_valc_implies_cequivc;
      exact en1|].
  eapply equality_respects_cequivc_right;
    [apply simpl_cequivc_mkc_cbv;
      apply cequivc_sym;
      apply computes_to_valc_implies_cequivc;
      exact en0|].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.

  repeat (rw @mkcv_less_substc).
  repeat (rw @mkcv_try_substc; auto).
  repeat (rw @mkcv_apply_substc).
  repeat (rw @csubst_mk_cv).
  repeat (rw @mkc_var_substc).
  repeat (rw @mkcv_utoken_substc).
  repeat (rw @mkcv_vbot_substc).
  repeat (rw @mkcv_zero_substc).
  unfold mkcv_zero.
  repeat (rw @substc2_mk_cv).
  fold (@mkcv_zero o [e]).

  allrw @mkc_zero_eq.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  boolvar; tcsp;[].

  apply @equality_in_natE in eqn.
  repndors.

  - unfold equality_of_nat in eqn; exrepnd; spcast.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;[exact eqn1|];
        apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;[exact eqn0|];
        apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc
      |].
    apply equality_in_tnat; unfold equality_of_nat.
    exists k0; dands; spcast; apply computes_to_valc_refl; eauto 2 with slow.

  - repnd; spcast.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact eqn0|apply cequivc_refl]
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact eqn|apply cequivc_refl]
      |].

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    allrw @substc_mkcv_zero.
    apply equality_in_tnat; unfold equality_of_nat.
    exists 0; dands; spcast; rw @mkc_zero_eq;
    apply computes_to_valc_refl; eauto 2 with slow.
Qed.

(* !!MOVE *)
Hint Resolve wf_apply : slow.

Lemma wf_bound_nat_try_aux {o} :
  forall a x e z (arg f : @NTerm o) t,
    wf_term arg
    -> wf_term f
    -> wf_term t
    -> wf_term (bound_nat_try_aux a arg x e z f t).
Proof.
  introv w1 w2 w3.
  unfold bound_nat_try_aux.
  apply wf_cbv; auto.
  apply wf_less; eauto 3 with slow.
  apply wf_try; eauto 3 with slow.
Qed.

Lemma wf_bound_nat_try {o} :
  forall a x e z (f : @NTerm o),
    wf_term f
    -> wf_term (bound_nat_try a x e z f).
Proof.
  introv w.
  apply wf_lam.
  apply wf_bound_nat_try_aux; eauto 3 with slow.
Qed.
Hint Resolve wf_bound_nat_try : slow.

Lemma wf_spexc {o} :
  forall (a : get_patom_set o), wf_term (spexc a).
Proof.
  introv.
  apply wf_exception; eauto 3 with slow.
Qed.
Hint Resolve wf_spexc : slow.

Lemma wf_bound_nat_aux {o} :
  forall a x e z (arg f : @NTerm o),
    wf_term arg
    -> wf_term f
    -> wf_term (bound_nat_aux a arg x e z f).
Proof.
  introv w1 w2.
  apply wf_cbv; auto.
  apply wf_less; eauto 3 with slow.
  apply wf_try; eauto 3 with slow.
Qed.

Lemma wf_bound_nat {o} :
  forall a x e z (f : @NTerm o),
    wf_term f
    -> wf_term (bound_nat a x e z f).
Proof.
  introv w.
  apply wf_lam.
  apply wf_bound_nat_aux; eauto 3 with slow.
Qed.
Hint Resolve wf_bound_nat : slow.

Lemma isprog_vars_bound_nat {o} :
  forall vs a x e z (f : @NTerm o),
    isprog_vars (x :: vs) f
    -> isprog_vars vs (bound_nat a x e z f).
Proof.
  introv isp.
  apply isprog_vars_lam.
  apply isprog_vars_cbv; eauto 3 with slow.
  apply isprog_vars_less; dands; eauto 3 with slow.
  apply isprog_vars_try_implies; eauto 3 with slow.
  apply isprog_vars_apply; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_bound_nat : slow.

Lemma isprog_vars_bound_nat_try {o} :
  forall vs a x e z (f : @NTerm o),
    isprog_vars (x :: vs) f
    -> isprog_vars vs (bound_nat_try a x e z f).
Proof.
  introv isp.
  apply isprog_vars_lam.
  apply isprog_vars_cbv; eauto 3 with slow.
  apply isprog_vars_less; dands; eauto 3 with slow.
  apply isprog_vars_try_implies; eauto 3 with slow.
  apply isprog_vars_apply; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_bound_nat_try : slow.

Lemma isprog_bound_nat {o} :
  forall a x e z (f : @NTerm o),
    isprog f
    -> isprog (bound_nat a x e z f).
Proof.
  introv isp.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_bound_nat; eauto 3 with slow.
Qed.
Hint Resolve isprog_bound_nat : slow.

Lemma isprog_bound_nat_try {o} :
  forall a x e z (f : @NTerm o),
    isprog f
    -> isprog (bound_nat_try a x e z f).
Proof.
  introv isp.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_bound_nat_try; eauto 3 with slow.
Qed.
Hint Resolve isprog_bound_nat_try : slow.

Lemma isprog_lfresh {o} :
  forall vs (t : @NTerm o),
    isprog t -> isprog (lfresh vs t).
Proof.
  induction vs; introv isp; simpl; auto.
  apply isprog_fresh_implies.
  apply IHvs in isp; eauto 3 with slow.
Qed.
Hint Resolve isprog_lfresh : slow.

Lemma isprog_spfexc {o} :
  forall vs1 vs2 (a : get_patom_set o),
    isprog (spfexc vs1 vs2 a).
Proof.
  introv.
  unfold spfexc.
  apply isprog_exception; eauto 3 with slow.
Qed.
Hint Resolve isprog_spfexc : slow.

Lemma cequiv_spfexc {o} :
  forall lib vs1 vs2 (a : get_patom_set o),
    cequiv lib (spfexc vs1 vs2 a) (spexc a).
Proof.
  introv.
  apply cequiv_spexc_if; eauto 3 with slow.
  exists (lfresh vs1 (mk_utoken a)) (@lfresh o vs2 mk_axiom); dands; auto;
  unfold computes_to_value; dands; eauto 3 with slow;
  try (apply reduces_to_lfresh_utoken);
  try (apply reduces_to_lfresh_axiom);
  try (apply reduces_to_symm).
Qed.

Lemma differ_try_compute_to_valc_nat {o} :
  forall lib a (F f g : @CTerm o) k x e z,
    !LIn a (getc_utokens F)
    -> equality lib f g (nat2natE a)
    -> computes_to_valc
         lib
         (mkc_apply F (bound_nat_try_c a x e z f))
         (mkc_nat k)
    -> {v1 : CTerm
        & {v2 : CTerm
        & reduces_toc lib (mkc_apply F (bound_nat_c a x e z f)) v1
        # reduces_toc lib (mkc_apply F (bound_nat_c a x e z g)) v2
        # ((v1 = mkc_nat k # v2 = mkc_nat k)
           [+] (cequivc lib v1 (spexcc a) # cequivc lib v2 (spexcc a)))}}.
Proof.
  introv nia equ comp.
  apply equality_in_nat2natE_implies in equ.
  destruct_cterms.
  unfold computes_to_valc in comp; unfold reduces_toc; allsimpl.
  unfold getc_utokens in nia; allsimpl.
  unfold cequivc; simpl; try (fold (spexc a)).

  fold (@mk_vbot o z) in comp.
  fold (bound_nat_try_aux a (mk_var x) x e z x1) in comp.
  fold (bound_nat_try a x e z x1) in comp.

  fold (@mk_vbot o z).
  fold (spexc a).
  fold (bound_nat_aux a (mk_var x) x e z x1).
  fold (bound_nat_aux a (mk_var x) x e z x0).
  fold (bound_nat a x e z x1).
  fold (bound_nat a x e z x0).

  unfold computes_to_value, reduces_to in comp; exrepnd.

  pose proof (differ_try_reduces_in_atmost_k_steps
                lib a x1 x0 mk_zero k0
                (mk_apply x2 (bound_nat_try a x e z x1))
                (mk_apply x2 (bound_nat a x e z x1))
                (mk_apply x2 (bound_nat a x e z x0))
                (mk_nat k)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  { apply wf_apply; eauto 3 with slow. }
  { apply wf_apply; eauto 3 with slow. }
  { apply wf_apply; eauto 3 with slow. }
  { apply differ_try_oterm; simpl; tcsp.
    introv xx; repndors; tcsp; ginv.
    - constructor; apply differ_try_refl; auto.
    - constructor.
      apply differ_try_oterm; simpl; tcsp.
      introv xx; repndors; tcsp; ginv.
      constructor.
      apply differ_try_base; auto. }

  exrepnd.
  apply differ_try_alpha_nat in h1; repndors; exrepnd; subst.

  - exists (@mkc_nat o k) (@mkc_nat o k); simpl; dands; auto.

  - applydup @reduces_to_preserves_isprog in h0;
    [|apply isprog_apply; complete (eauto 3 with slow)].
    applydup @reduces_to_preserves_isprog in h2;
    [|apply isprog_apply; complete (eauto 3 with slow)].

    exists (existT _ t2' h3) (existT _ t3' h4); simpl.
    unfold spfexc_pair in h1; exrepnd; subst.
    dands; auto.
    right; dands; tcsp; apply cequiv_spfexc.
Qed.

Lemma apply_nat2natE_aux {o} :
  forall lib (F : @CTerm o) f g a x e z,
    e <> x
    -> !LIn a (getc_utokens F)
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> equality lib f g (nat2natE a)
    -> equality
         lib
         (mkc_apply F (bound_nat_c a x e z f))
         (mkc_apply F (bound_nat_c a x e z g))
         (natE a).
Proof.
  introv d nia mem equ.
  rw @equality_in_fun in mem; repnd.
  clear mem0 mem1.

  applydup (implies_equal_bound_nat_try_aux_c lib a x e z) in equ as eqtry;
    try (complete (intro k; ginv)).
  applydup mem in eqtry as eqn.
  allrw @equality_in_tnat; allunfold @equality_of_nat; exrepnd; spcast.

  pose proof (differ_try_compute_to_valc_nat lib a F f g k x e z) as h.
  repeat (autodimp h hyp); exrepnd.

  apply equality_in_natE; repndors; repnd; subst.
  - left.
    unfold equality_of_nat; exists k; dands; spcast;
    apply computes_to_valc_iff_reduces_toc; dands; auto.
  - right; dands; spcast;
    eapply cequivc_trans;[|exact h3|idtac|exact h1];[|];
    apply reduces_toc_implies_cequivc; auto.
Qed.

Lemma isprog_vars_dup2 {o} :
  forall v vs (t : @NTerm o),
    isprog_vars (v :: vs) t
    -> isprog_vars (v :: v :: vs) t.
Proof.
  introv isp.
  eapply isprog_vars_subvars;[|exact isp].
  rw subvars_prop; simpl; sp.
Qed.

Definition mkcv_dup2 {o} v vs (t : @CVTerm o (v :: vs)) : CVTerm (v :: v :: vs) :=
  let (a,x) := t in
  exist (isprog_vars (v :: v :: vs)) a (isprog_vars_dup2 v vs a x).

Definition bound_nat_vf_c {o} (a : get_patom_set o) (x e z f : NVar) : CVTerm [f] :=
  mkcv_lam
    [f]
    x
    (mkcv_cbv
       [x,f]
       (mk_cv_app_r [f] [x] (mkc_var x))
       x
       (mkcv_dup2
          x
          [f]
          (mkcv_less
             [x,f]
             (mk_cv_app_r [f] [x] (mkc_var x))
             (mkcv_zero [x,f])
             (mkcv_vbot [x,f] z)
             (mkcv_try [x,f]
                       (mkcv_apply [x,f]
                                   (mk_cv_app_l [x] [f] (mkc_var f))
                                   (mk_cv_app_r [f] [x] (mkc_var x)))
                       (mkcv_utoken [x,f] a)
                       e
                       (spexccv [e,x,f] a))))).

Definition app_bound_nat {o} a (x e z f : NVar) (F : @CTerm o) : CTerm :=
  mkc_lam f (mkcv_apply [f] (mk_cv [f] F) (bound_nat_vf_c a x e z f)).

Lemma substc_bound_nat_vf_c {o} :
  forall a x e z f (t : @CTerm o),
    f <> x
    -> substc t f (bound_nat_vf_c a x e z f)
       = bound_nat_c a x e z t.
Proof.
  introv d1; destruct_cterms; simpl.
  apply cterm_eq; simpl.
  unfsubst; simpl.

  allrw @sub_filter_nil_r.
  allrw memvar_singleton.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  fold_terms.

  f_equal.
  repeat (boolvar; simpl); fold_terms; tcsp.
Qed.

Lemma equality_app_bound_nat_nat2nat2nat {o} :
  forall lib a x e z f (F : @CTerm o),
    f <> x
    -> e <> x
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> equality lib F (app_bound_nat a x e z f F) (mkc_fun nat2nat mkc_tnat).
Proof.
  introv d1 d2 mem.
  allrw @equality_in_fun; repnd; dands; tcsp; eauto 3 with slow.
  intros f1 f2 en.

  unfold app_bound_nat.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_bound_nat_vf_c; auto.
  apply mem.

  allrw @equality_in_fun; repnd; dands; tcsp.
  clear en0 en1.
  intros n1 n2 eqn.

  apply equality_in_tnat in eqn.
  unfold equality_of_nat in eqn; exrepnd; spcast.
  pose proof (en (mkc_nat k) (mkc_nat k)) as m.
  autodimp m hyp.
  { apply equality_in_tnat; unfold equality_of_nat; exists k;
    dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn1
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn0
    |].
  clear dependent n1.
  clear dependent n2.

  eapply equality_trans;[exact m|].
  apply equality_in_tnat in m.
  unfold equality_of_nat in m; exrepnd; spcast; GC.
  clear en m1.

  unfold bound_nat_c.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_cbv_substc_same.
  rw @mkcv_cont1_dup1.
  rw @mkc_var_substc.

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.
  rw @mkcv_less_substc.
  rw @substc_mkcv_zero.
  rw @mkcv_vbot_substc.
  rw @mkcv_try_substc; auto;[].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @mkc_var_substc.
  rw @mkcv_utoken_substc.
  unfold spexccv; rw @substc2_mk_cv; fold (spexccv [e] a).

  rw @mkc_zero_eq.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
  boolvar; tcsp;[].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply simpl_cequivc_mkc_try;
     [apply computes_to_valc_implies_cequivc;exact m0
     |apply cequivc_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;
      apply computes_to_valc_implies_cequivc;
      eapply computes_to_valc_mkc_try;
      [apply computes_to_valc_refl
      |apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
    |]; eauto 3 with slow; [].

  apply equality_in_tnat.
  unfold equality_of_nat.
  exists k0; dands; spcast; auto.
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma equality_app_bound_nat_nat2natE2natE {o} :
  forall lib a x e z f (F : @CTerm o),
    f <> x
    -> e <> x
    -> member lib F (mkc_fun (nat2natE a) (natE a))
    -> equality lib F (app_bound_nat a x e z f F) (mkc_fun (nat2natE a) (natE a)).
Proof.
  introv d1 d2 mem.
  allrw @equality_in_fun; repnd; dands; tcsp; eauto 3 with slow.
  intros f1 f2 en.

  unfold app_bound_nat.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_bound_nat_vf_c; auto.
  apply mem.

  allrw @equality_in_fun; repnd; dands; tcsp.
  clear en0 en1.
  intros n1 n2 eqn.

  apply equality_in_tnat in eqn.
  unfold equality_of_nat in eqn; exrepnd; spcast.
  pose proof (en (mkc_nat k) (mkc_nat k)) as m.
  autodimp m hyp.
  { apply equality_in_tnat; unfold equality_of_nat; exists k;
    dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn1
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn0
    |].
  clear dependent n1.
  clear dependent n2.

  eapply equality_trans;[exact m|].
  apply equality_in_natE in m; repndors.

  - unfold equality_of_nat in m; exrepnd; spcast; GC.
    clear en m1.

    unfold bound_nat_c.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_beta|].
    rw @mkcv_cbv_substc_same.
    rw @mkcv_cont1_dup1.
    rw @mkc_var_substc.

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.
    rw @mkcv_less_substc.
    rw @substc_mkcv_zero.
    rw @mkcv_vbot_substc.
    rw @mkcv_try_substc; auto;[].
    rw @mkcv_apply_substc.
    rw @csubst_mk_cv.
    rw @mkc_var_substc.
    rw @mkcv_utoken_substc.
    unfold spexccv; rw @substc2_mk_cv; fold (spexccv [e] a).

    rw @mkc_zero_eq.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
    boolvar; tcsp;[].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply simpl_cequivc_mkc_try;
       [apply computes_to_valc_implies_cequivc;exact m0
       |apply cequivc_refl]
      |].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;
        [apply computes_to_valc_refl
        |apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
      |]; eauto 3 with slow; [].

    apply equality_in_natE; left.
    unfold equality_of_nat.
    exists k0; dands; spcast; auto.
    apply computes_to_valc_refl; eauto 3 with slow.

  - repnd; spcast.
    clear en m0.

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym; exact m|].

    unfold bound_nat_c.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_beta|].
    rw @mkcv_cbv_substc_same.
    rw @mkcv_cont1_dup1.
    rw @mkc_var_substc.

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.
    rw @mkcv_less_substc.
    rw @substc_mkcv_zero.
    rw @mkcv_vbot_substc.
    rw @mkcv_try_substc; auto;[].
    rw @mkcv_apply_substc.
    rw @csubst_mk_cv.
    rw @mkc_var_substc.
    rw @mkcv_utoken_substc.
    unfold spexccv; rw @substc2_mk_cv; fold (spexccv [e] a).

    rw @mkc_zero_eq.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
    boolvar; tcsp;[].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply simpl_cequivc_mkc_try;
       [exact m
       |apply cequivc_refl]
      |].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    unfold spexccv.
    rw @csubst_mk_cv.

    apply equality_in_natE; right.
    dands; spcast; auto.
Qed.

Lemma cequiv_open_simpler_equiv {p} :
  forall lib a c,
    simpl_olift (@cequiv p lib) a c <=> cequiv_open lib a c.
Proof.
  introv.
  split.

  - intro Hos. repnud Hos.
    unfold cequiv_open, olift.
    dands;auto.
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.
    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    apply (cequiv_rw_l _ _ _ Xtrima).
    apply (cequiv_rw_r _ _ _ Xtrimc).
    apply Hos; auto.

  - intro Hos.
    repnud Hos.
    unfold olift in Hos; unfold simpl_olift; repnd; dands; auto.
    introv ps isp1 isp2.
    pose proof (Hos sub) as h.
    repeat (autodimp h hyp); eauto with slow.
Qed.

(* !!MOVE *)
Hint Resolve cl_sub_implies_disjoint_bv_sub : slow.

Lemma prog_sub_sub_keep {o} :
  forall (sub : @Sub o) vs,
    prog_sub sub
    -> prog_sub (sub_keep sub vs).
Proof.
  induction sub; introv ps; simpl; eauto 3 with slow.
  destruct a; boolvar; eauto 3 with slow; allrw @prog_sub_cons; tcsp.
Qed.
Hint Resolve prog_sub_sub_keep : slow.

Lemma dom_sub_sub_keep_subset {o} :
  forall (sub : @Sub o) vs,
    subset (dom_sub (sub_keep sub vs)) vs.
Proof.
  induction sub; introv; simpl; auto.
  destruct a; boolvar; simpl; tcsp.
  apply subset_cons_l; dands; tcsp.
Qed.

Definition sub_find_def {o} (sub : @Sub o) v t :=
  match sub_find sub v with
    | Some t => t
    | None => t
  end.

Fixpoint mk_sub_vars {o} (vs : list NVar) (sub : @Sub o) : Sub :=
  match vs with
    | [] => []
    | v :: vs => (v,sub_find_def sub v mk_axiom) :: (mk_sub_vars vs sub)
  end.

Lemma isprogram_sub_find_def {o} :
  forall (sub : @Sub o) v t,
    prog_sub sub
    -> isprogram t
    -> isprogram (sub_find_def sub v t).
Proof.
  introv ps isp.
  unfold sub_find_def.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.
  apply sub_find_some in Heqsf.
  rw <- @prog_sub_eq in ps.
  apply in_sub_eta in Heqsf; repnd.
  apply ps in Heqsf; auto.
Qed.

Lemma prog_sub_mk_sub_vars {o} :
  forall vs (sub : @Sub o),
    prog_sub sub
    -> prog_sub (mk_sub_vars vs sub).
Proof.
  induction vs; introv ps; simpl; eauto 3 with slow.
  apply prog_sub_cons; dands; tcsp.
  apply isprogram_sub_find_def; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_mk_sub_vars : slow.

Lemma dom_sub_mk_sub_vars {o} :
  forall vs (sub : @Sub o),
    dom_sub (mk_sub_vars vs sub) = vs.
Proof.
  induction vs; introv; simpl; auto.
  rw IHvs; auto.
Qed.

Lemma sub_find_mk_sub_vars {o} :
  forall v vs (sub : @Sub o),
    sub_find (mk_sub_vars vs sub) v
    = if memvar v vs
      then Some (sub_find_def sub v mk_axiom)
      else None.
Proof.
  induction vs; introv; simpl; auto.
  boolvar; repndors; subst; GC; tcsp; allrw @not_over_or; repnd; tcsp.
Qed.

Lemma sub_filter_mk_sub_vars {o} :
  forall vs (sub : @Sub o) l,
    sub_filter (mk_sub_vars vs sub) l
    = mk_sub_vars (remove_nvars l vs) (sub_filter sub l).
Proof.
  induction vs; introv; simpl.

  - allrw remove_nvars_nil_r; simpl; auto.

  - allrw remove_nvars_cons_r.
    boolvar; simpl; tcsp.
    f_equal; tcsp.
    f_equal.
    unfold sub_find_def.
    rw @sub_find_sub_filter_eq.
    boolvar; tcsp.
Qed.

Lemma lsubst_aux_eq_mk_sub_vars {o} :
  forall t vs (sub : @Sub o),
    (forall v : NVar, LIn v vs -> LIn v (free_vars t) -> LIn v (dom_sub sub))
    -> prog_sub sub
    -> subset (dom_sub sub) vs
    -> lsubst_aux t sub = lsubst_aux t (mk_sub_vars vs sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv imp ps ss; allsimpl; auto.

  - Case "vterm".
    allrw subset_cons_l; repnd.
    rw @sub_find_mk_sub_vars.
    unfold sub_find_def.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; boolvar; tcsp.

    + apply sub_find_some in Heqsf.
      apply in_sub_eta in Heqsf; repnd.
      apply ss in Heqsf0; sp.

    + apply sub_find_none_iff in Heqsf; tcsp.
      pose proof (imp v); sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    f_equal.
    rw @sub_filter_mk_sub_vars.
    eapply ind; eauto 3 with slow.

    + introv j k.
      allrw <- @dom_sub_sub_filter.
      allrw in_remove_nvars; repnd; dands; auto.
      pose proof (imp v) as h.
      repeat (autodimp h hyp).
      rw lin_flat_map.
      eexists; dands; eauto.
      simpl; rw in_remove_nvars; dands; auto.

    + rw <- @dom_sub_sub_filter.
      introv j; allrw in_remove_nvars; repnd; dands; auto.
Qed.

Lemma ex_sub_lsubst_eq {o} :
  forall (sub : @Sub o) vs t,
    isprog_vars (dom_sub sub) t
    -> prog_sub sub
    -> subset (dom_sub sub) vs
    -> {sub' : Sub
        & prog_sub sub'
        # dom_sub sub' = vs
        # sub' = mk_sub_vars vs sub
        # lsubst t sub = lsubst t sub'}.
Proof.
  introv isp ps ss.
  exists (mk_sub_vars vs sub).
  rw @dom_sub_mk_sub_vars.
  dands; eauto 3 with slow.
  repeat unflsubst.

  assert (forall v, LIn v vs -> LIn v (free_vars t) -> LIn v (dom_sub sub)) as imp.
  { introv i1 i2.
    allrw @isprog_vars_eq; repnd.
    allrw subvars_eq.
    apply isp0 in i2; auto. }

  pose proof (lsubst_aux_eq_mk_sub_vars t vs sub) as h.
  repeat (autodimp h hyp).
Qed.

Lemma cequiv_open_simpler_equiv2 {o} :
  forall lib vs (a b : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs b
    -> (cequiv_open lib a b
        <=> forall sub,
              prog_sub sub
              -> dom_sub sub = vs
              -> cequiv lib (lsubst a sub) (lsubst b sub)).
Proof.
  introv isp1 isp2.
  rw <- @cequiv_open_simpler_equiv.
  unfold simpl_olift.
  split; introv h.

  - repnd.
    introv ps e; subst.
    apply h; auto;
    apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow;
    allrw @isprog_vars_eq; allrw @subvars_eq; repnd; eauto 3 with slow.

  - dands; eauto 3 with slow.
    introv ps ispa ispb.

    pose proof (simple_lsubst_trim2 a sub vs) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { allrw @isprog_vars_eq; allrw @subvars_eq; sp. }

    pose proof (simple_lsubst_trim2 b sub vs) as l.
    repeat (autodimp l hyp); eauto 3 with slow.
    { allrw @isprog_vars_eq; allrw @subvars_eq; sp. }

    rw q; rw l.
    pose proof (dom_sub_sub_keep_subset sub vs) as ds.
    pose proof (prog_sub_sub_keep sub vs ps) as ps'.
    remember (sub_keep sub vs) as sub'; clear Heqsub'.

    rw q in ispa.
    rw l in ispb.
    applydup @lsubst_program_implies in ispa.
    applydup @lsubst_program_implies in ispb.

    assert (isprog_vars (dom_sub sub') a) as ispa'.
    { allrw @isprog_vars_eq; repnd; dands; allrw @subvars_eq; auto. }
    assert (isprog_vars (dom_sub sub') b) as ispb'.
    { allrw @isprog_vars_eq; repnd; dands; allrw @subvars_eq; auto. }

    pose proof (ex_sub_lsubst_eq sub' vs a) as k.
    repeat (autodimp k hyp).
    exrepnd; rw k0.

    pose proof (ex_sub_lsubst_eq sub' vs b) as j.
    repeat (autodimp j hyp).
    exrepnd; rw j0.

    subst sub'0 sub'1.
    apply h; eauto 3 with slow.
Qed.

Lemma approx_open_simpler_equiv2 {o} :
  forall lib vs (a b : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs b
    -> (approx_open lib a b
        <=> forall sub,
              prog_sub sub
              -> dom_sub sub = vs
              -> approx lib (lsubst a sub) (lsubst b sub)).
Proof.
  introv isp1 isp2.
  rw <- @approx_open_simpler_equiv.
  unfold simpl_olift.
  split; introv h.

  - repnd.
    introv ps e; subst.
    apply h; auto;
    apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow;
    allrw @isprog_vars_eq; allrw @subvars_eq; repnd; eauto 3 with slow.

  - dands; eauto 3 with slow.
    introv ps ispa ispb.

    pose proof (simple_lsubst_trim2 a sub vs) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { allrw @isprog_vars_eq; allrw @subvars_eq; sp. }

    pose proof (simple_lsubst_trim2 b sub vs) as l.
    repeat (autodimp l hyp); eauto 3 with slow.
    { allrw @isprog_vars_eq; allrw @subvars_eq; sp. }

    rw q; rw l.
    pose proof (dom_sub_sub_keep_subset sub vs) as ds.
    pose proof (prog_sub_sub_keep sub vs ps) as ps'.
    remember (sub_keep sub vs) as sub'; clear Heqsub'.

    rw q in ispa.
    rw l in ispb.
    applydup @lsubst_program_implies in ispa.
    applydup @lsubst_program_implies in ispb.

    assert (isprog_vars (dom_sub sub') a) as ispa'.
    { allrw @isprog_vars_eq; repnd; dands; allrw @subvars_eq; auto. }
    assert (isprog_vars (dom_sub sub') b) as ispb'.
    { allrw @isprog_vars_eq; repnd; dands; allrw @subvars_eq; auto. }

    pose proof (ex_sub_lsubst_eq sub' vs a) as k.
    repeat (autodimp k hyp).
    exrepnd; rw k0.

    pose proof (ex_sub_lsubst_eq sub' vs b) as j.
    repeat (autodimp j hyp).
    exrepnd; rw j0.

    subst sub'0 sub'1.
    apply h; eauto 3 with slow.
Qed.

Lemma cequivc_lam {o} :
  forall lib x (t1 t2 : @CVTerm o [x]),
    (forall u, cequivc lib (substc u x t1) (substc u x t2))
    -> cequivc lib (mkc_lam x t1) (mkc_lam x t2).
Proof.
  introv ceq.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_congruence; fold_terms;
  try (apply isprogram_lam); auto.
  unfold cequiv_bts, lblift; simpl; dands; auto.
  introv len.
  destruct n; tcsp; try omega; clear len.
  unfold selectbt; simpl.
  unfold blift.
  exists [x] x1 x0; dands; eauto 3 with slow.

  pose proof (cequiv_open_simpler_equiv2 lib [x] x1 x0) as h.
  repeat (autodimp h hyp).
  apply h; clear h.
  introv ps e.
  destruct sub as [|a]; allsimpl; ginv.
  destruct a as [v t]; allsimpl.
  destruct sub; allsimpl; ginv.
  allrw @prog_sub_cons; repnd.
  allrw @isprogram_eq.
  allrw @fold_subst.
  pose proof (ceq (existT _ t ps0)) as h.
  allsimpl; auto.
Qed.

Lemma cequivc_cbv {o} :
  forall lib u1 u2 x (t1 t2 : @CVTerm o [x]),
    cequivc lib u1 u2
    -> (forall u, cequivc lib (substc u x t1) (substc u x t2))
    -> cequivc lib (mkc_cbv u1 x t1) (mkc_cbv u2 x t2).
Proof.
  introv ceq1 ceq2.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_congruence; fold_terms;
  try (apply isprogram_cbv); eauto 3 with slow;
  try (complete (clear ceq2; allrw @isprog_vars_eq; sp)).
  unfold cequiv_bts, lblift; simpl; dands; auto.
  introv len.
  repeat (destruct n; tcsp; try omega); clear len; unfold selectbt; simpl.
  { unfold blift; exists ([] : list NVar) x1 x0; dands; auto.
    apply cequiv_implies_cequiv_open; auto. }
  unfold blift.
  exists [x] x3 x2; dands; eauto 3 with slow.

  pose proof (cequiv_open_simpler_equiv2 lib [x] x3 x2) as h.
  repeat (autodimp h hyp).
  apply h; clear h.
  introv ps e.
  destruct sub as [|a]; allsimpl; ginv.
  destruct a as [v t]; allsimpl.
  destruct sub; allsimpl; ginv.
  allrw @prog_sub_cons; repnd.
  allrw @isprogram_eq.
  allrw @fold_subst.
  pose proof (ceq2 (existT _ t ps0)) as h.
  allsimpl; auto.
Qed.

Definition sp_bound_nat_c {o} x z (f : @CTerm o) :=
  mkc_lam
    x
    (mkcv_less
       [x]
       (mkc_var x)
       (mkcv_zero [x])
       (mkcv_vbot [x] z)
       (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))).

Lemma approxc_implies_cequivc {o} :
  forall lib (a b : @CTerm o),
    approxc lib a b -> approxc lib b a -> cequivc lib a b.
Proof.
  introv apr1 apr2.
  destruct_cterms.
  allunfold @approxc; allunfold @cequivc; allsimpl.
  split; auto.
Qed.

Lemma computes_step_try_ncan {p} :
  forall lib n l a c e,
    compute_step lib (mk_try (oterm (@NCan p n) l) a c e)
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess t => csuccess (mk_try t a c e)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma computes_step_try_abs {p} :
  forall lib abs l a c e,
    compute_step lib (mk_try (oterm (@Abs p abs) l) a c e)
    = match compute_step_lib lib abs l with
        | csuccess t => csuccess (mk_try t a c e)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_try_implies {o} :
  forall lib k (t : @NTerm o) a c e v,
    computes_to_val_like_in_max_k_steps lib (mk_try t a c e) v k
    -> {x : NTerm
        & {m : nat
        & m < k
        # computes_to_val_like_in_max_k_steps lib t x m}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    destruct t as [vv|f|op bs]; ginv.

    { exists (sterm f) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow. }

    dopid op as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      exists (oterm (Can can) bs) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow.

    + Case "NCan".
      rw @computes_step_try_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) bs)) as xx; destruct xx; ginv.
      symmetry in Heqxx.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto; try omega.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      exists (oterm Exc bs) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow.

    + Case "Abs".
      rw @computes_step_try_abs in comp1.
      remember (compute_step_lib lib abs bs) as xx; destruct xx; ginv.
      symmetry in Heqxx.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto; try omega.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma hasvalue_like_try {o} :
  forall lib (t : @NTerm o) a v e,
    hasvalue_like lib (mk_try t a v e)
    -> hasvalue_like lib t.
Proof.
  introv hv.
  allrw @computes_to_val_like_iff_hasvalue_like; exrepnd.
  allunfold @computes_to_val_like; exrepnd.
  apply computes_to_val_like_in_max_k_steps_try_implies in hv1; exrepnd.
  exists x m; auto.
Qed.

Lemma hasvalue_likec_try {o} :
  forall lib (t : @CTerm o) a v e,
    hasvalue_likec lib (mkc_try t a v e)
    -> hasvalue_likec lib t.
Proof.
  introv hv.
  destruct_cterms.
  allunfold @hasvalue_likec; allsimpl.
  apply hasvalue_like_try in hv; auto.
Qed.

Lemma hasvalue_likec_implies_or {o} :
  forall lib (t : @CTerm o),
    hasvalue_likec lib t
    -> (hasvaluec lib t [+] raises_exceptionc lib t).
Proof.
  introv; destruct_cterms.
  unfold hasvalue_likec, hasvaluec, raises_exceptionc; simpl.
  introv hv; apply hasvalue_like_implies_or in hv; eauto 3 with slow.
Qed.

Lemma computes_step_cbv_ncan {p} :
  forall lib n l v u,
    compute_step lib (mk_cbv (oterm (@NCan p n) l) v u)
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess t => csuccess (mk_cbv t v u)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma computes_step_cbv_abs {p} :
  forall lib abs l v u,
    compute_step lib (mk_cbv (oterm (@Abs p abs) l) v u)
    = match compute_step_lib lib abs l with
        | csuccess t => csuccess (mk_cbv t v u)
        | cfailure m t => cfailure m t
      end.
Proof.
  introv; csunf; simpl; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_cbv_implies {o} :
  forall lib k (t : @NTerm o) v u z,
    computes_to_val_like_in_max_k_steps lib (mk_cbv t v u) z k
    -> {x : NTerm
        & {m : nat
        & m < k
        # computes_to_val_like_in_max_k_steps lib t x m}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    destruct t as [vv|f|op bs]; ginv.

    { exists (sterm f) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow. }

    dopid op as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      exists (oterm (Can can) bs) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow.

    + Case "NCan".
      rw @computes_step_cbv_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) bs)) as xx; destruct xx; ginv.
      symmetry in Heqxx.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto; try omega.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.

    + Case "Exc".
      exists (oterm Exc bs) 0; dands; try omega.
      rw @computes_to_val_like_in_max_k_steps_0; dands; eauto 3 with slow.

    + Case "Abs".
      rw @computes_step_cbv_abs in comp1.
      remember (compute_step_lib lib abs bs) as xx; destruct xx; ginv.
      symmetry in Heqxx.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      exists x (S m); dands; auto; try omega.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists n; auto.
Qed.

Lemma hasvalue_like_cbv {o} :
  forall lib (t : @NTerm o) v u,
    hasvalue_like lib (mk_cbv t v u)
    -> hasvalue_like lib t.
Proof.
  introv hv.
  allrw @computes_to_val_like_iff_hasvalue_like; exrepnd.
  allunfold @computes_to_val_like; exrepnd.
  apply computes_to_val_like_in_max_k_steps_cbv_implies in hv1; exrepnd.
  exists x m; auto.
Qed.

Lemma hasvalue_likec_cbv {o} :
  forall lib (t : @CTerm o) v u,
    hasvalue_likec lib (mkc_cbv t v u)
    -> hasvalue_likec lib t.
Proof.
  introv hv.
  destruct_cterms.
  allunfold @hasvalue_likec; allsimpl.
  apply hasvalue_like_cbv in hv; auto.
Qed.

Lemma computes_to_val_like_less {o} :
  forall lib (t1 t2 t3 t4 : @NTerm o) v,
    wf_term t1
    -> wf_term t2
    -> wf_term t3
    -> wf_term t4
    -> computes_to_val_like lib (mk_less t1 t2 t3 t4) v
    -> {i1 : Z
        & {i2 : Z
        & computes_to_can lib t1 (mk_integer i1)
        # computes_to_can lib t2 (mk_integer i2)
        # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_integer i1) (mk_integer i2) t3 t4)
        # computes_to_val_like lib (if Z_lt_le_dec i1 i2 then t3 else t4) v}}
       [+] {a : NTerm
            & {e : NTerm
            & computes_to_exception lib a t1 e
            # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_exception a e) t2 t3 t4)
            # v = mk_exception a e}}
       [+] {i : Z
            & {a : NTerm
            & {e : NTerm
            & computes_to_can lib t1 (mk_integer i)
            # computes_to_exception lib a t2 e
            # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_integer i) (mk_exception a e) t3 t4)
            # v = mk_exception a e}}}.
Proof.
  introv w1 w2 w3 w4 comp.
  unfold computes_to_val_like in comp; exrepnd.
  apply computes_to_val_like_in_max_k_steps_comp_implies in comp0; auto.
  repndors; exrepnd; repndors; exrepnd; subst; allsimpl; ginv.

  - left; exists i1 i2; dands; eauto 3 with slow.
    + unfold computes_to_can; dands; eauto 3 with slow.
    + unfold computes_to_can; dands; eauto 3 with slow.
    + boolvar.
      * unfold computes_to_val_like; eauto 3 with slow.
      * unfold computes_to_val_like; eauto 3 with slow.

  - right; left.
    exists en e; dands; eauto 3 with slow.
    unfold computes_to_exception_in_max_k_steps in comp3.
    unfold computes_to_exception; eauto 3 with slow.

  - right; right.
    exists i en e; dands; eauto 3 with slow.
    + unfold computes_to_can; dands; eauto 3 with slow.
    + unfold computes_to_exception_in_max_k_steps in comp5.
      unfold computes_to_exception; eauto 3 with slow.
Qed.

Lemma hasvalue_like_less {o} :
  forall lib (t1 t2 t3 t4 : @NTerm o),
    wf_term t1
    -> wf_term t2
    -> wf_term t3
    -> wf_term t4
    -> hasvalue_like lib (mk_less t1 t2 t3 t4)
    -> {i1 : Z
        & {i2 : Z
        & computes_to_can lib t1 (mk_integer i1)
        # computes_to_can lib t2 (mk_integer i2)
        # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_integer i1) (mk_integer i2) t3 t4)
        # hasvalue_like lib (if Z_lt_le_dec i1 i2 then t3 else t4)}}
       [+] {a : NTerm
            & {e : NTerm
            & computes_to_exception lib a t1 e
            # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_exception a e) t2 t3 t4)}}
       [+] {i : Z
            & {a : NTerm
            & {e : NTerm
            & computes_to_can lib t1 (mk_integer i)
            # computes_to_exception lib a t2 e
            # reduces_to lib (mk_less t1 t2 t3 t4) (mk_less (mk_integer i) (mk_exception a e) t3 t4)}}}.
Proof.
  introv w1 w2 w3 s4 comp.
  apply computes_to_val_like_iff_hasvalue_like in comp; exrepnd.
  apply computes_to_val_like_less in comp0; auto.
  repndors; exrepnd; subst.
  - left; exists i1 i2; dands; auto.
    apply computes_to_val_like_iff_hasvalue_like.
    exists v; auto.
  - right; left; exists a e; dands; auto.
  - right; right; exists i a e; dands; auto.
Qed.

Lemma hasvalue_likec_less {o} :
  forall lib (t1 t2 t3 t4 : @CTerm o),
    hasvalue_likec lib (mkc_less t1 t2 t3 t4)
    -> {i1 : Z
        & {i2 : Z
        & reduces_toc lib t1 (mkc_integer i1)
        # reduces_toc lib t2 (mkc_integer i2)
        # reduces_toc lib (mkc_less t1 t2 t3 t4) (mkc_less (mkc_integer i1) (mkc_integer i2) t3 t4)
        # hasvalue_likec lib (if Z_lt_le_dec i1 i2 then t3 else t4)}}
       [+] {a : CTerm
            & {e : CTerm
            & computes_to_excc lib a t1 e
            # reduces_toc lib (mkc_less t1 t2 t3 t4) (mkc_less (mkc_exception a e) t2 t3 t4)}}
       [+] {i : Z
            & {a : CTerm
            & {e : CTerm
            & reduces_toc lib t1 (mkc_integer i)
            # computes_to_excc lib a t2 e
            # reduces_toc lib (mkc_less t1 t2 t3 t4) (mkc_less (mkc_integer i) (mkc_exception a e) t3 t4)}}}.
Proof.
  introv comp; destruct_cterms; allunfold @hasvalue_likec; allsimpl.
  allunfold @reduces_toc; allsimpl.
  allunfold @computes_to_excc; allsimpl.
  apply hasvalue_like_less in comp; eauto 3 with slow.
  allunfold @computes_to_can.
  repndors; exrepnd.
  - left; exists i3 i4; dands; eauto 3 with slow.
    boolvar; allsimpl; auto.
  - right; left.
    applydup @preserve_program_exc2 in comp0; allrw @isprogram_eq; repnd; auto.
    exists (existT _ a comp3) (existT _ e comp2); allsimpl; dands; auto.
  - right; right.
    applydup @preserve_program_exc2 in comp2; allrw @isprogram_eq; repnd; auto.
    exists i3 (existT _ a comp5) (existT _ e comp4); allsimpl; dands; auto.
Qed.

Lemma reduces_toc_trans {o} :
  forall lib (a b c : @CTerm o),
    reduces_toc lib a b
    -> reduces_toc lib b c
    -> reduces_toc lib a c.
Proof.
  introv r1 r2; destruct_cterms; allunfold @reduces_toc; allsimpl.
  eapply reduces_to_trans; eauto.
Qed.

Lemma cequivc_mkc_less_exc {o} :
  forall lib (a e t1 t2 t3 : @CTerm o),
    cequivc
      lib
      (mkc_less (mkc_exception a e) t1 t2 t3)
      (mkc_exception a e).
Proof.
  introv; destruct_cterms; unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; allrw @isprogram_eq;
  [apply isprog_less; dands; auto; apply isprog_exception; complete auto|].
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma raises_exceptionc_as_computes_to_excc {o} :
  forall lib (t : @CTerm o),
    raises_exceptionc lib t
    <=> {a : CTerm & {e : CTerm & computes_to_excc lib a t e}}.
Proof.
  introv; destruct_cterms; unfold raises_exceptionc, computes_to_excc; simpl.
  unfold raises_exception.
  split; intro h; exrepnd.
  - applydup @preserve_program_exc2 in h1; allrw @isprogram_eq; auto; repnd.
    exists (existT _ a h2) (existT _ e h0); simpl; auto.
  - destruct_cterms; allsimpl.
    eexists; eexists; eauto.
Qed.

Lemma cequivc_mkc_cbv_exc {o} :
  forall lib (a e : @CTerm o) (x : NVar) (u : CVTerm [x]),
    cequivc lib (mkc_cbv (mkc_exception a e) x u) (mkc_exception a e).
Proof.
  introv; apply reduces_toc_implies_cequivc.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma cequivc_bound_nat_c_sp_bound_nat_c {o} :
  forall lib a (f : @CTerm o) x e z,
    e <> x
    -> member lib f (nat2natE a)
    -> cequivc
         lib
         (bound_nat_c a x e z f)
         (sp_bound_nat_c x z f).
Proof.
  introv d1 mem.
  unfold bound_nat_c, sp_bound_nat_c.

  apply cequivc_lam; introv.
  allrw @mkcv_cbv_substc_same.
  allrw @mkcv_cont1_dup1.
  allrw @mkcv_less_substc.
  allrw @substc_mkcv_zero.
  allrw @mkcv_apply_substc.
  allrw @csubst_mk_cv.
  allrw @mkc_var_substc.
  allrw @mkcv_vbot_substc.

  apply approxc_implies_cequivc; apply approxc_assume_hasvalue; intro hv.

  - apply @hasvalue_likec_cbv in hv.
    apply @hasvalue_likec_implies_or in hv.
    repndors.

    + apply hasvaluec_computes_to_valc_implies in hv; exrepnd.
      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply computes_to_valc_implies_cequivc;
          exact hv0|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl];
           apply computes_to_valc_implies_cequivc;
           exact hv0
        ].
      rw @computes_to_valc_iff_reduces_toc in hv0; repnd.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv;complete auto|].

      allrw @mkcv_less_substc.
      rw @mkcv_try_substc; try (complete (intro xx; ginv)).
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      allrw @mkcv_utoken_substc.
      unfold spexccv; rw @substc2_mk_cv; fold (spexccv [nvare] a).

      apply approxc_assume_hasvalue; intro hv.

      apply hasvalue_likec_less in hv; repndors; exrepnd.

      * eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv2
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply cequivc_mkc_less;
             [apply reduces_toc_implies_cequivc;exact hv2
             |apply cequivc_refl
             |apply cequivc_refl
             |apply cequivc_refl]
          ].
        rw @mkc_zero_eq.
        rw @mkc_nat_eq.
        eapply cequivc_approxc_trans;
          [apply cequivc_mkc_less_int|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;apply cequivc_mkc_less_int].

        clear hv3.

        boolvar; eauto 3 with slow; try (apply approxc_refl).

        pose proof (Wf_Z.Z_of_nat_complete_inf i1) as q.
        autodimp q hyp;[]; exrepnd; subst.
        rw <- @mkc_nat_eq in hv2.

        eapply cequivc_approxc_trans;
          [apply simpl_cequivc_mkc_try;
            [apply implies_cequivc_apply;
              [apply cequivc_refl
              |apply reduces_toc_implies_cequivc;exact hv2]
            |apply cequivc_refl]
          |].

        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply implies_cequivc_apply;
             [apply cequivc_refl
             |apply reduces_toc_implies_cequivc;
               eapply reduces_toc_trans;
               [exact hv1|exact hv2]
             ]
          ].

        apply equality_in_fun in mem; repnd.
        clear mem0 mem1.
        pose proof (mem (mkc_nat n) (mkc_nat n)) as h.
        autodimp h hyp; eauto 3 with slow.

        apply equality_in_natE_implies in h; repndors.

        { unfold equality_of_nat_tt in h; exrepnd; GC.
          eapply cequivc_approxc_trans;
            [apply computes_to_valc_implies_cequivc;
              eapply computes_to_valc_mkc_try;
              [exact h1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
            |].
          apply computes_to_valc_implies_approxc in h1; sp. }

        { repnd; GC.
          eapply approxc_cequivc_trans;
            [|apply cequivc_sym;exact h0].

          eapply cequivc_approxc_trans;
            [apply simpl_cequivc_mkc_try;
              [exact h0
              |apply cequivc_refl]
            |].
          unfold spexcc.
          eapply cequivc_approxc_trans;
            [apply reduces_toc_implies_cequivc;
              apply reduces_toc_mkc_try_exc
            |].
          unfold spexccv; rw @csubst_mk_cv.
          apply approxc_refl. }

      * assert (computes_to_excc lib a0 b e0) as comp.
        { allrw @computes_to_excc_iff_reduces_toc.
          eapply reduces_toc_trans;[exact hv2|].
          apply reduces_toc_refl. }
        clear hv1 hv2.

        allrw @computes_to_excc_iff_reduces_toc.

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact comp
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply cequivc_mkc_less;
             [apply reduces_toc_implies_cequivc;exact comp
             |apply cequivc_refl
             |apply cequivc_refl
             |apply cequivc_refl]
          ].

        eapply cequivc_approxc_trans;
          [apply cequivc_mkc_less_exc|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc].
        apply approxc_refl.

      * apply (computes_to_valc_and_excc_false _ _ _ mkc_zero) in hv4; tcsp.
        apply computes_to_valc_refl; eauto 3 with slow.

    + allrw @raises_exceptionc_as_computes_to_excc; exrepnd.
      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply reduces_toc_implies_cequivc;
          exact hv1|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl];
           apply reduces_toc_implies_cequivc;
           exact hv1
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_exc].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv_exc|].
      apply approxc_refl.

  - apply hasvalue_likec_less in hv.
    repndors; exrepnd.

    + eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv0
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].
      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_int|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_cbv]; eauto 3 with slow;[].

      allrw @mkcv_less_substc.
      rw @mkcv_try_substc; try (complete (intro xx; ginv)).
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      allrw @mkcv_utoken_substc.
      unfold spexccv; rw @substc2_mk_cv; fold (spexccv [nvare] a).
      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_int].

      clear hv1.

      boolvar; eauto 3 with slow; try (apply approxc_refl).

      pose proof (Wf_Z.Z_of_nat_complete_inf i1) as q.
      autodimp q hyp;[]; exrepnd; subst.
      allrw <- @mkc_nat_eq.

      eapply cequivc_approxc_trans;
        [apply implies_cequivc_apply;
          [apply cequivc_refl
          |apply reduces_toc_implies_cequivc;exact hv0]
        |].

      apply equality_in_fun in mem; repnd.
      clear mem0 mem1.
      pose proof (mem (mkc_nat n) (mkc_nat n)) as h.
      autodimp h hyp; eauto 3 with slow.

      apply equality_in_natE_implies in h; repndors.

      { unfold equality_of_nat_tt in h; exrepnd; GC.
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;
             eapply computes_to_valc_mkc_try;
             [exact h1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
          ].
        apply computes_to_valc_implies_approxc in h1; sp. }

      { repnd; GC.
        eapply cequivc_approxc_trans;[exact h0|].

        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply simpl_cequivc_mkc_try;
             [exact h0
             |apply cequivc_refl]
          ].
        unfold spexcc.
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply reduces_toc_implies_cequivc;
             apply reduces_toc_mkc_try_exc
          ].
        unfold spexccv; rw @csubst_mk_cv.
        apply approxc_refl. }

    + clear hv1.

      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc|].

      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_cbv_exc
        ].
      apply approxc_refl.

    + apply (computes_to_valc_and_excc_false _ _ _ mkc_zero) in hv2; tcsp.
      apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma apply_nat2natE_aux2 {o} :
  forall lib (F : @CTerm o) f g a x z,
    !LIn a (getc_utokens F)
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> equality lib f g (nat2natE a)
    -> equality
         lib
         (mkc_apply F (sp_bound_nat_c x z f))
         (mkc_apply F (sp_bound_nat_c x z g))
         (natE a).
Proof.
  introv nia mem equ.
  pose proof (ex_fresh_var [x]) as fv.
  exrepnd; allsimpl; allrw not_over_or; repnd; GC.
  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply (cequivc_bound_nat_c_sp_bound_nat_c _ a _ x v z);tcsp;
       apply equality_refl in equ;auto
      ]
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply (cequivc_bound_nat_c_sp_bound_nat_c _ a _ x v z);tcsp;
       apply equality_sym in equ; apply equality_refl in equ;auto
      ]
    |].
  apply apply_nat2natE_aux; auto.
Qed.

Definition sp_bound_nat_vf_c {o} (x z f : NVar) : @CVTerm o [f] :=
  mkcv_lam
    [f]
    x
    (mkcv_less
       [x,f]
       (mk_cv_app_r [f] [x] (mkc_var x))
       (mkcv_zero [x,f])
       (mkcv_vbot [x,f] z)
       (mkcv_apply [x,f]
                   (mk_cv_app_l [x] [f] (mkc_var f))
                   (mk_cv_app_r [f] [x] (mkc_var x)))).

Definition sp_app_bound_nat {o} (x z f : NVar) (F : @CTerm o) : CTerm :=
  mkc_lam f (mkcv_apply [f] (mk_cv [f] F) (sp_bound_nat_vf_c x z f)).

Lemma substc_sp_bound_nat_vf_c {o} :
  forall x z f (t : @CTerm o),
    f <> x
    -> substc t f (sp_bound_nat_vf_c x z f)
       = sp_bound_nat_c x z t.
Proof.
  introv d1; destruct_cterms; simpl.
  apply cterm_eq; simpl.
  unfsubst; simpl.

  allrw @sub_filter_nil_r.
  allrw memvar_singleton.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  fold_terms.

  f_equal.
  repeat (boolvar; simpl); fold_terms; tcsp.
Qed.

Lemma equality_sp_app_bound_nat_nat2nat2nat {o} :
  forall lib x z f (F : @CTerm o),
    f <> x
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> equality lib F (sp_app_bound_nat x z f F) (mkc_fun nat2nat mkc_tnat).
Proof.
  introv d1 mem.
  allrw @equality_in_fun; repnd; dands; tcsp; eauto 3 with slow.
  intros f1 f2 en.

  unfold app_bound_nat.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_sp_bound_nat_vf_c; auto.
  apply mem.

  allrw @equality_in_fun; repnd; dands; tcsp.
  clear en0 en1.
  intros n1 n2 eqn.

  apply equality_in_tnat in eqn.
  unfold equality_of_nat in eqn; exrepnd; spcast.
  pose proof (en (mkc_nat k) (mkc_nat k)) as m.
  autodimp m hyp.
  { apply equality_in_tnat; unfold equality_of_nat; exists k;
    dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn1
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn0
    |].
  clear dependent n1.
  clear dependent n2.

  eapply equality_trans;[exact m|].
  apply equality_in_tnat in m.
  unfold equality_of_nat in m; exrepnd; spcast; GC.
  clear en m1.

  unfold sp_bound_nat_c.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_less_substc.
  rw @substc_mkcv_zero.
  rw @mkcv_vbot_substc.
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @mkc_var_substc.

  rw @mkc_zero_eq.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
  boolvar; tcsp;[].

  apply equality_in_tnat.
  unfold equality_of_nat.
  exists k0; dands; spcast; auto.
Qed.

Lemma equality_sp_app_bound_nat_nat2natE2natE {o} :
  forall lib a x z f (F : @CTerm o),
    f <> x
    -> member lib F (mkc_fun (nat2natE a) (natE a))
    -> equality lib F (sp_app_bound_nat x z f F) (mkc_fun (nat2natE a) (natE a)).
Proof.
  introv d1 mem.
  allrw @equality_in_fun; repnd; dands; tcsp; eauto 3 with slow.
  intros f1 f2 en.

  unfold app_bound_nat.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_sp_bound_nat_vf_c; auto.
  apply mem.

  allrw @equality_in_fun; repnd; dands; tcsp.
  clear en0 en1.
  intros n1 n2 eqn.

  apply equality_in_tnat in eqn.
  unfold equality_of_nat in eqn; exrepnd; spcast.
  pose proof (en (mkc_nat k) (mkc_nat k)) as m.
  autodimp m hyp.
  { apply equality_in_tnat; unfold equality_of_nat; exists k;
    dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn1
    |].
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;[apply cequivc_refl|];
     apply cequivc_sym;
     apply computes_to_valc_implies_cequivc;
     exact eqn0
    |].
  clear dependent n1.
  clear dependent n2.

  eapply equality_trans;[exact m|].
  apply equality_in_natE in m; repndors.

  - unfold equality_of_nat in m; exrepnd; spcast; GC.
    clear en m1.

    unfold sp_bound_nat_c.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_beta|].
    rw @mkcv_less_substc.
    rw @substc_mkcv_zero.
    rw @mkcv_vbot_substc.
    rw @mkcv_apply_substc.
    rw @csubst_mk_cv.
    rw @mkc_var_substc.

    rw @mkc_zero_eq.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
    boolvar; tcsp;[].

    apply equality_in_natE; left.
    unfold equality_of_nat.
    exists k0; dands; spcast; auto.

  - repnd; spcast.
    clear en m0.

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym; exact m|].

    unfold sp_bound_nat_c.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_beta|].
    rw @mkcv_less_substc.
    rw @substc_mkcv_zero.
    rw @mkcv_vbot_substc.
    rw @mkcv_apply_substc.
    rw @csubst_mk_cv.
    rw @mkc_var_substc.

    rw @mkc_zero_eq.
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_less_nat|]; eauto 3 with slow.
    boolvar; tcsp;[].

    apply equality_in_natE; right.
    dands; spcast; auto.
Qed.

Lemma getc_utokens_sp_app_bound_nat {o} :
  forall x z f (F : @CTerm o),
    getc_utokens (sp_app_bound_nat x z f F) = getc_utokens F.
Proof.
  introv; destruct_cterms; unfold getc_utokens; simpl.
  allrw app_nil_r; auto.
Qed.

Lemma cequivc_mkc_less_exc2 {o} :
  forall lib i (a e t1 t2 : @CTerm o),
    cequivc
      lib
      (mkc_less (mkc_integer i) (mkc_exception a e) t1 t2)
      (mkc_exception a e).
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl.
  dcwf h; allsimpl; auto.
Qed.

Lemma cequivc_mkc_less_twice {o} :
  forall lib (a b c d : @CTerm o),
    cequivc
      lib
      (mkc_less a b c (mkc_less a b c d))
      (mkc_less a b c d).
Proof.
  introv.

  apply approxc_implies_cequivc; apply approxc_assume_hasvalue; intro hv.

  - apply hasvalue_likec_less in hv; repndors; exrepnd.

    + eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv0
        |apply reduces_toc_implies_cequivc;exact hv2
        |apply cequivc_refl
        |apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply reduces_toc_implies_cequivc;exact hv2
          |apply cequivc_refl
          |apply cequivc_refl]
        ]
      |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv0
           |apply reduces_toc_implies_cequivc;exact hv2
           |apply cequivc_refl
           |apply cequivc_refl]
        ].

      eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_mkc_less_int
        ]
      |].

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_int|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;apply cequivc_mkc_less_int].

      clear hv1.

      boolvar; eauto 3 with slow; try (apply approxc_refl).

    + allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv0
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl]
        ].

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc].
        apply approxc_refl.

    + allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv1
        |apply reduces_toc_implies_cequivc;exact hv2
        |apply cequivc_refl
        |apply cequivc_refl
        ]
      |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv1
           |apply reduces_toc_implies_cequivc;exact hv2
           |apply cequivc_refl
           |apply cequivc_refl]
        ].

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc2|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc2].
        apply approxc_refl.

  - apply hasvalue_likec_less in hv; repndors; exrepnd.

    + eapply approxc_cequivc_trans;
      [|apply cequivc_sym;
         apply cequivc_mkc_less;
         [apply reduces_toc_implies_cequivc;exact hv0
         |apply reduces_toc_implies_cequivc;exact hv2
         |apply cequivc_refl
         |apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv0
           |apply reduces_toc_implies_cequivc;exact hv2
           |apply cequivc_refl
           |apply cequivc_refl]
         ]
      ].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply reduces_toc_implies_cequivc;exact hv2
          |apply cequivc_refl
          |apply cequivc_refl]
        |].

      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_mkc_less_int
           ]
        ].

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_int|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;apply cequivc_mkc_less_int].

      clear hv1.

      boolvar; eauto 3 with slow; try (apply approxc_refl).

    + allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv0
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl]
        ].

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc].
        apply approxc_refl.

    + allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv1
        |apply reduces_toc_implies_cequivc;exact hv2
        |apply cequivc_refl
        |apply cequivc_refl
        ]
      |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_less;
           [apply reduces_toc_implies_cequivc;exact hv1
           |apply reduces_toc_implies_cequivc;exact hv2
           |apply cequivc_refl
           |apply cequivc_refl]
        ].

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc2|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc2].
        apply approxc_refl.
Qed.

Lemma cequivc_sp_bound_nat_c_twice {o} :
  forall lib x z (f : @CTerm o),
    cequivc
      lib
      (sp_bound_nat_c x z (sp_bound_nat_c x z f))
      (sp_bound_nat_c x z f).
Proof.
  introv.
  unfold sp_bound_nat_c.

  apply cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_vbot_substc.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_beta]
    |].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_vbot_substc.

  apply cequivc_mkc_less_twice.
Qed.

Lemma cequivc_apply_sp_app_bound_nat_sp_bound_nat {o} :
  forall lib x z vf (f F : @CTerm o),
    vf <> x
    -> cequivc
         lib
         (mkc_apply (sp_app_bound_nat x z vf F) (sp_bound_nat_c x z f))
         (mkc_apply F (sp_bound_nat_c x z f)).
Proof.
  introv d1.
  unfold sp_app_bound_nat.
  eapply cequivc_trans;[apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_sp_bound_nat_vf_c; auto.

  apply implies_cequivc_apply; eauto 3 with slow.

  apply cequivc_sp_bound_nat_c_twice.
Qed.

Lemma type_nat2natE {o} :
  forall lib (a : get_patom_set o),
    type lib (nat2natE a).
Proof.
  introv.
  apply tequality_mkc_fun; allrw @fold_type; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2natE : slow.

Lemma sp_app_bound_nat_nat2natE {o} :
  forall lib a x z vf (F : @CTerm o),
    vf <> z
    -> vf <> x
    -> !LIn a (getc_utokens F)
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> member
         lib
         (sp_app_bound_nat x z vf F)
         (mkc_fun (nat2natE a) (natE a)).
Proof.
  introv d1 d2 nia mem.

  apply equality_in_fun; dands; eauto 3 with slow.
  intros f g m.

  pose proof (equality_sp_app_bound_nat_nat2nat2nat lib x z vf F) as h.
  repeat (autodimp h hyp); try (complete (intro xx; ginv)).
  applydup @equality_sym in h as m1.
  apply equality_refl in m1.

  pose proof (apply_nat2natE_aux2
                lib
                (sp_app_bound_nat x z vf F)
                f g a x z) as q.
  allrw @getc_utokens_sp_app_bound_nat.
  repeat (autodimp q hyp).

  eapply equality_respects_cequivc_left in q;
    [|apply (cequivc_apply_sp_app_bound_nat_sp_bound_nat _ _ _ vf);
       intro xx; ginv];[].

  eapply equality_respects_cequivc_right in q;
    [|apply (cequivc_apply_sp_app_bound_nat_sp_bound_nat _ _ _ vf);
       intro xx; ginv];[].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  allrw @mkcv_apply_substc.
  allrw @csubst_mk_cv.
  repeat (rw @substc_sp_bound_nat_vf_c; try (complete (intro xx; ginv))).
  auto.
Qed.

Lemma equality_sp_app_bound_nat_nat2natE2natE2 {o} :
  forall lib a x z f (F : @CTerm o),
    f <> x
    -> member lib (sp_app_bound_nat x z f F) (mkc_fun (nat2natE a) (natE a))
    -> equality lib F (sp_app_bound_nat x z f F) (mkc_fun (nat2natE a) (natE a)).
Proof.
  introv d1 mem.

  allrw @equality_in_fun; repnd; dands; tcsp; eauto 3 with slow.
  intros f1 f2 en.

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @substc_sp_bound_nat_vf_c; auto.

  applydup mem in en as ea.

  eapply equality_respects_cequivc_right in ea;[|apply cequivc_beta].
  eapply equality_respects_cequivc_left in ea;[|apply cequivc_beta].
  repeat (rw @mkcv_apply_substc in ea).
  repeat (rw @csubst_mk_cv in ea).
  repeat (rw @substc_sp_bound_nat_vf_c in ea; auto).

  eapply equality_trans;[|exact ea].
  apply equality_refl in ea.
  apply equality_refl in en.
  clear f2.

Abort.

Lemma apply_nat2natE {o} :
  forall lib (F : @CTerm o) a,
    !LIn a (getc_utokens F)
    -> member lib F (mkc_fun nat2nat mkc_tnat)
    -> member lib F (mkc_fun (nat2natE a) (natE a)).
Proof.
  introv nia mem.

  pose proof (sp_app_bound_nat_nat2natE lib a nvarx nvarz nvarf F) as h.
  repeat (autodimp h hyp); try (complete (intro xx; ginv)).

Abort.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)