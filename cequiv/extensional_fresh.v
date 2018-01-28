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


Require Import approx_star0.
Require Import approx_star_abs.
Require Import approx_star_fresh.


Lemma extensional_fresh {p} : @extensional_op p (NCan NFresh).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; allsimpl; repnd; subst; GC;
  [apply isprogram_fresh_implies in Hprt; exrepnd; complete ginv|].
  fold_terms.

  assert (m <= S k) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) as lek by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  apply isprogram_fresh in Hprt.
  applydup @reduces_atmost_preserves_program in Hcv4; auto;
  [|apply isprogram_subst_if_bt; eauto 3 with slow].

  duplicate Has.
  unfold lblift_sub in Has; repnd.
  simpl in Has, Has1; cpx; GC.
  repeat(approxrelbtd); show_hyps.
  fold_terms.

  applydup @alpha_eq_preserves_isvalue_like in Hcv8; auto.
  unfold mk_fresh in XX1.
  rw @compute_step_fresh_if_isvalue_like2 in XX1; auto; ginv.

  assert (isvalue_like (subst u v (mk_utoken (get_fresh_atom lib t)))) as isv.
  { apply isvalue_like_subst; auto. }
  assert (isvalue_like x) as isvx.
  { apply alpha_eq_sym in Hcv5; apply alpha_eq_preserves_isvalue_like in Hcv5; auto. }

  remember (get_fresh_atom lib t) as ua.
  apply isprogram_fresh in Hprt'.
  pose proof (fresh_atom p (get_utokens_lib lib (mk_pair t tr))) as fa.
  destruct fa as [ua' fa]; allsimpl; allrw app_nil_r.
  allrw in_app_iff; allrw not_over_or; repnd.
  pose proof (get_fresh_atom_prop_and_lib lib t) as gfu; rw <- Hequa in gfu.

  apply no_change_after_val_like with (k2 := k) in Hcv4; auto.
  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k t x [(v,mk_utoken ua)] [(v,mk_utoken ua')]) as comp.
  repeat (autodimp comp hyp); eauto 3 with slow.

  { constructor; auto; introv i; rw in_app_iff; tcsp. }

  { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; auto. }
  { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; auto.
    rw in_app_iff; tcsp. }

  exrepnd; allrw @fold_subst.
  unfold get_utokens_sub in comp2; simpl in comp2; allrw disjoint_singleton_l.

  assert (isprogram (subst w0 v (mk_utoken ua))) as ispsw0.
  { apply alphaeq_preserves_program in comp0; apply comp0; auto. }
  assert (isprogram s) as isps.
  { apply alpha_eq_sym in comp1; apply alphaeq_preserves_program in comp1; apply comp1.
    apply isprogram_subst_if_bt; eauto 2 with slow.
    apply isprogram_subst_implies in ispsw0; auto. }

  assert (!LIn ua (get_utokens_lib lib u)) as niu.
  { intro i; apply Hcv6 in i; sp. }

  assert (alpha_eq u w0) as aeq0.
  { assert (alpha_eq (subst u v (mk_utoken ua)) (subst w0 v (mk_utoken ua))) as h by eauto with slow.
    pose proof (change_bvars_alpha_wspec [v] u) as k1.
    pose proof (change_bvars_alpha_wspec [v] w0) as k2.
    exrepnd.
    allrw disjoint_singleton_l.
    pose proof (lsubst_alpha_congr2 ntcv0 u [(v,mk_utoken ua)]) as p1.
    pose proof (lsubst_alpha_congr2 ntcv w0 [(v,mk_utoken ua)]) as p2.
    autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
    allrw @fold_subst.
    assert (alpha_eq (subst ntcv0 v (mk_utoken ua)) (subst ntcv v (mk_utoken ua))) as h' by eauto with slow.
    apply alpha_eq_subst_utoken_not_in_implies in h'; eauto with slow.
    { intro j.
      apply (get_utokens_subset_get_utokens_lib lib) in j.
      destruct niu; apply (alphaeq_preserves_get_utokens_lib lib) in k3.
      rw k3 ; auto. }
    { intro j.
      apply (get_utokens_subset_get_utokens_lib lib) in j.
      destruct comp2; apply (alphaeq_preserves_get_utokens_lib lib) in k0.
      rw k0; auto. }
  }

  assert (isvalue_like w0) as isvw0.
  { apply alpha_eq_preserves_isvalue_like in aeq0; auto. }
  assert (isvalue_like s) as isvs.
  { apply alpha_eq_sym in comp1; apply alpha_eq_preserves_isvalue_like in comp1; auto.
    apply isvalue_like_subst; auto. }

  make_red_val_like comp5 h.
  pose proof (Hi (subst t v (mk_utoken ua')) s (subst tr vr (mk_utoken ua'))) as h'.
  repeat (autodimp h' hyp).
  { apply isprogram_subst_if_bt; eauto with slow. }
  { apply isprogram_subst_if_bt; eauto with slow. }
  { unfold approx_star_bterm, blift_sub in Has0bt; exrepnd; repndors; exrepnd; tcsp; GC.
    applydup @alpha_eq_bterm_implies_eq_length in Has0bt2.
    allsimpl; destruct lv as [|v']; allsimpl; tcsp.
    destruct lv; allsimpl; tcsp; GC; try omega.
    pose proof (lsubst_alpha_congr4 [v] [v'] t nt1 [(v,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq1.
    repeat (autodimp aeq1 hyp); simpl; eauto 2 with slow.
    pose proof (lsubst_alpha_congr4 [vr] [v'] tr nt2 [(vr,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq2.
    repeat (autodimp aeq2 hyp); simpl; eauto 2 with slow.
    allrw @fold_subst.
    eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact aeq1].
    eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact aeq2].
    pose proof (approx_star_change_nrut_sub
                  lib nt1 nt2 sub
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)
                  [(v',mk_utoken ua')]
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)) as q.
    allsimpl; repeat (autodimp q hyp); eauto 5 with slow;[].
    apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp.
    apply alpha_eq_bterm_preserves_utokens in Has0bt2.
    apply alpha_eq_bterm_preserves_utokens in Has0bt0.
    allsimpl.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt2.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt0.
    rw <- Has0bt2; rw <- Has0bt0.
    repeat (rw in_app_iff); repeat (rw in_app_iff); sp.
  }

  pose proof (approx_star_alpha_fun_l lib s (subst tr vr (mk_utoken ua')) (subst u v (mk_utoken ua'))) as ap1.
  repeat (autodimp ap1 hyp).
  { eapply alpha_eq_trans;[exact comp1|].
    unfold subst; apply lsubst_alpha_congr2; eauto with slow. }

  apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; subst; eauto 2 with slow.

  assert (alpha_eq (pushdown_fresh v w) (pushdown_fresh v u)) as aeq.
  { apply implies_alpha_eq_pushdown_fresh.
    apply alpha_eq_bterm_congr; eauto with slow. }
  eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact aeq].

  assert (isprog_vars [v] u) as ispu.
  { apply alphaeq_preserves_program in Hcv5.
    apply Hcv5 in Hcv3.
    apply isprogram_subst_implies in Hcv3.
    apply isprog_vars_iff_isprogram_bt; auto. }

  pose proof (howe_lemma2_implies_same_value_like
                lib
                (subst u v (mk_utoken ua'))
                (subst tr vr (mk_utoken ua'))) as ap2.
  repeat (autodimp ap2 hyp); eauto 2 with slow.
  { apply isprogram_subst_if_bt; eauto 2 with slow. }
  { apply isprogram_subst_if_bt; eauto 2 with slow. }
  exrepnd.
  unfold reduces_to in ap0; exrepnd.
  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k0 tr v0 [(vr,mk_utoken ua')] [(vr,mk_utoken ua')]) as comp'.
  allrw @fold_subst.
  simpl in *; GC.
  repeat (autodimp comp' hyp); eauto 2 with slow;
    try (complete (unfold get_utokens_sub; simpl; apply disjoint_singleton_l; rw in_app_iff; tcsp));
    try (complete (constructor; auto; introv i; rw in_app_iff; tcsp));[].

  exrepnd.
  clear dependent s0.
  allunfold @get_utokens_sub; allsimpl; allrw disjoint_singleton_l.
  allrw @fold_subst.
  eapply same_value_like_alpha_eq_r in ap2;[|exact comp'0].
  eapply approx_starbts_get_bterms_alpha_eq in ap3;[|exact comp'0].

  assert (isprog_vars [vr] w1) as ispw1.
  { apply reduces_atmost_preserves_program in ap4.
    - apply alphaeq_preserves_program in comp'0; apply comp'0 in ap4.
      apply isprogram_subst_implies in ap4.
      apply isprog_vars_iff_isprogram_bt; auto.
    - apply isprogram_subst_if_bt; eauto with slow. }

  assert (!LIn ua' (get_utokens_lib lib u)) as niua'u.
  { intro i; apply Hcv6 in i; sp; rw in_app_iff in i; tcsp. }

  assert (get_op (subst u v (mk_utoken ua')) = get_op u) as gopu.
  { unfsubst; unfold isvalue_like in Hcv0; repndors.
    - apply iscan_implies in Hcv0; repndors; exrepnd; subst; simpl; auto.
    - apply isexc_implies2 in Hcv0; exrepnd; subst; simpl; auto. }

  rw gopu in ap3.

  pose proof (approx_star_pushdown_fresh_if_subst lib u w1 v vr ua') as apspf.
  repeat (autodimp apspf hyp).

  eapply approx_star_open_trans;[exact apspf|].

  apply approx_implies_approx_open.

  remember (get_fresh_atom lib tr) as a.

  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k0 tr v0 [(vr,mk_utoken ua')] [(vr,mk_utoken a)]) as r.
  allsimpl; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
  allsimpl; allrw disjoint_singleton_l.
  repeat (autodimp r hyp); eauto 3 with slow;
    try (complete (constructor; auto; introv i; rw in_app_iff; tcsp));
    try (complete (rw in_app_iff; tcsp));[| |].

  { apply nr_ut_sub_cons; eauto with slow; intro xx; subst; apply get_fresh_atom_prop_and_lib. }
  { subst; apply get_fresh_atom_prop_and_lib. }
  exrepnd.

  allrw disjoint_singleton_l.

  allrw @fold_subst.
  pose proof (alpha_eq_lsubst_nrut_sub_implies
                w1 w2 [(vr,mk_utoken ua')]
                (get_utokens_lib lib w1 ++ get_utokens_lib lib w2)) as aeqws.

  repeat (autodimp aeqws hyp); eauto 4 with slow.

  { apply nrut_sub_cons; simpl; eexists; dands; eauto with slow;
      tcsp; rw in_app_iff; sp; allrw in_app_iff; tcsp. }

  applydup @approx_starbt_relates_only_wf in Has0bt as wf; repnd.
  allrw @bt_wf_iff.
  allrw @nt_wf_eq.

  pose proof (reduces_to_fresh lib tr s0 vr) as rf; simpl in rf.
  rw <- Heqa in rf.
  repeat (autodimp rf hyp).
  { exists k0; auto. }
  exrepnd.

  assert (alpha_eq s0 (subst w1 vr (mk_utoken a))) as aeq1.
  { eapply alpha_eq_trans;[exact r1|].
    apply lsubst_alpha_congr2; eauto with slow. }

  assert (alpha_eq z (subst_utokens (subst w1 vr (mk_utoken a)) [(a,mk_var vr)])) as aeq2.
  { eapply alpha_eq_trans;[exact rf0|].
    apply alpha_eq_subst_utokens; eauto with slow. }

  assert (!LIn a (get_utokens_lib lib w1)) as niaw1.
  { intro xx.
    apply (alphaeq_preserves_get_utokens_lib lib) in aeqws;
      rw aeqws in xx; apply r4 in xx.
    subst; apply get_fresh_atom_prop_and_lib in xx; tcsp. }

  rw in_app_iff in niaw1; apply not_over_or in niaw1; repnd.

  pose proof (simple_alphaeq_subst_utokens_subst w1 vr a niaw0) as aeq3.

  assert (alpha_eq z w1) as aeq4 by eauto 3 with slow.

  apply (approx_trans _ _ (mk_fresh vr z));
    [|apply reduces_to_implies_approx_eauto; auto;
      apply isprogram_fresh; complete auto].

  eapply approx_alpha_rw_r_aux;
    [apply alpha_eq_sym; apply implies_alpha_eq_mk_fresh; exact aeq4|].

  assert (isvalue_like w1) as isvlw1.
  { repeat (rw @cl_subst_subst_aux in ap2; eauto 2 with slow).
    unfold subst_aux in ap2.
    inversion ap2 as [? ? ? e1 e2|].

    - destruct u as [z11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.

      + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
        try (complete (inversion gopu)).

      + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
        try (complete (inversion gopu)); ginv.
        destruct w1 as [z22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
        inversion e2; subst; allsimpl; fold_terms; GC.
        allrw subset_cons_l; repnd; tcsp.
        allrw not_over_or; tcsp.

    - destruct u as [z11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
      destruct w1 as [z22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
  }

  pose proof (compute_step_fresh_if_isvalue_like lib vr w1 isvlw1) as comp.
  apply reduces_to_implies_approx_eauto;
    [apply isprogram_fresh; complete auto|].
  apply reduces_to_if_step; auto.
Qed.
