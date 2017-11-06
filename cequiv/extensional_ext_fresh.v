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


Require Import approx_ext_star0.
Require Import approx_ext_star_abs.
Require Import approx_ext_star_fresh.


Ltac rev_assert n t :=
  let xxx := fresh "h" in
  match goal with
  | [ |- ?c ] => assert (t -> c) as xxx;[intro n|apply xxx;clear xxx]
  end.

Lemma extensional_ext_fresh {p} : @extensional_op_ext p (NCan NFresh).
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

  apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; try subst a; eauto 2 with slow.

  assert (alpha_eq (pushdown_fresh v w) (pushdown_fresh v u)) as aeq.
  { apply implies_alpha_eq_pushdown_fresh.
    apply alpha_eq_bterm_congr; eauto 3 with slow. }
  eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact aeq].

  (* XXXXXXXXXXXX *)

  assert (forall l,
             {ua' : get_patom_set p
              & {v0 : NTerm
              & {k0 : nat
              & {w1 : NTerm
              & isprog_vars [vr] tr
              # isprog_vars [vr] w1
              # !LIn ua' l
              # !LIn ua' (get_utokens tr)
              # !LIn ua' (get_utokens_library lib)
              # !LIn ua' (get_utokens_lib lib w1)
              # !LIn ua' (get_utokens_lib lib u)
              # subset (get_utokens_lib lib w1) (get_utokens_lib lib tr)
              # reduces_in_atmost_k_steps lib (subst tr vr (mk_utoken ua')) v0 k0
              # alpha_eq v0 (subst w1 vr (mk_utoken ua'))
              # same_value_like lib (subst u v (mk_utoken ua')) (subst w1 vr (mk_utoken ua'))
              # approx_ext_starbts lib (get_op u) (get_bterms (subst u v (mk_utoken ua'))) (get_bterms (subst w1 vr (mk_utoken ua')))
              # get_op (subst u v (mk_utoken ua')) = get_op u
              # approx_ext_open lib (pushdown_fresh vr w1) (mk_fresh vr tr)}}}}) as ah.

  {
    introv.
    unfold approx_ext_star_bterm, blift_sub in Has0bt; exrepnd; repndors; exrepnd; tcsp; GC.
    (* == we commit here to a list of forbidden names == *)
    pose proof (Has0bt1 (l ++ get_utokens t ++ get_utokens tr)) as Has0bt1.
    exrepnd; GC.
    applydup @alpha_eq_bterm_implies_eq_length in Has0bt2.
    allsimpl; destruct lv as [|v']; allsimpl; tcsp.
    destruct lv; allsimpl; tcsp; GC; try omega.
    destruct sub as [|vt]; simpl in *; ginv.
    destruct vt as [vt ta]; simpl in *.
    destruct sub; simpl in *; try (inversion Has0bt3); subst vt; GC.
    apply nrut_sub_cons in Has0bt5; exrepnd; simpl in *; GC.

    clear Has0bt1.

    subst ta.
    rename a into ua'.

    pose proof (lsubst_alpha_congr4 [v] [v'] t nt1 [(v,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq1.
    repeat (autodimp aeq1 hyp); simpl; eauto 2 with slow.
    pose proof (lsubst_alpha_congr4 [vr] [v'] tr nt2 [(vr,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq2.
    repeat (autodimp aeq2 hyp); simpl; eauto 2 with slow.
    allrw @fold_subst.

    eapply approx_ext_star_alpha_fun_l in Has0bt4;[|apply alpha_eq_sym;eauto].
    eapply approx_ext_star_alpha_fun_r in Has0bt4;[|apply alpha_eq_sym;eauto].

    (*XXXXX*)

    (*  pose proof (fresh_atom p (get_utokens_lib lib (mk_pair t tr))) as fa.
  destruct fa as [ua' fa]; allsimpl; allrw app_nil_r.*)
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
    { assert (alpha_eq (subst u v (mk_utoken ua)) (subst w0 v (mk_utoken ua))) as h by eauto 3 with slow.
      pose proof (change_bvars_alpha_wspec [v] u) as k1.
      pose proof (change_bvars_alpha_wspec [v] w0) as k2.
      exrepnd.
      allrw disjoint_singleton_l.
      pose proof (lsubst_alpha_congr2 ntcv0 u [(v,mk_utoken ua)]) as p1.
      pose proof (lsubst_alpha_congr2 ntcv w0 [(v,mk_utoken ua)]) as p2.
      autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
      allrw @fold_subst.
      assert (alpha_eq (subst ntcv0 v (mk_utoken ua)) (subst ntcv v (mk_utoken ua))) as h' by eauto 4 with slow.
      apply alpha_eq_subst_utoken_not_in_implies in h'; eauto 4 with slow;[|].
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
    { apply isprogram_subst_if_bt; eauto 3 with slow. }
    { apply isprogram_subst_if_bt; eauto 3 with slow. }
    (*  { unfold approx_ext_star_bterm, blift_sub in Has0bt; exrepnd; repndors; exrepnd; tcsp; GC.
    applydup @alpha_eq_bterm_implies_eq_length in Has0bt2.
    allsimpl; destruct lv as [|v']; allsimpl; tcsp.
    destruct lv; allsimpl; tcsp; GC; try omega.
    pose proof (lsubst_alpha_congr4 [v] [v'] t nt1 [(v,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq1.
    repeat (autodimp aeq1 hyp); simpl; eauto 2 with slow.
    pose proof (lsubst_alpha_congr4 [vr] [v'] tr nt2 [(vr,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq2.
    repeat (autodimp aeq2 hyp); simpl; eauto 2 with slow.
    allrw @fold_subst.
    eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact aeq1].
    eapply approx_ext_star_alpha_fun_r;[|apply alpha_eq_sym; exact aeq2].

    pose proof (approx_ext_star_change_nrut_sub
                  lib nt1 nt2 sub
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)
                  [(v',mk_utoken ua')]
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)) as q.
    allsimpl; repeat (autodimp q hyp); eauto 5 with slow;[].

    apply nrut_sub_cons; eexists; dands; simpl; eauto 3 with slow; tcsp;[].
    apply alpha_eq_bterm_preserves_utokens in Has0bt2.
    apply alpha_eq_bterm_preserves_utokens in Has0bt0.
    allsimpl.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt2.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt0.
    rw <- Has0bt2; rw <- Has0bt0.
    repeat (rw in_app_iff); repeat (rw in_app_iff); sp.
  }*)

    pose proof (approx_ext_star_alpha_fun_l lib s (subst tr vr (mk_utoken ua')) (subst u v (mk_utoken ua'))) as ap1.
    repeat (autodimp ap1 hyp).
    { eapply alpha_eq_trans;[exact comp1|].
      unfold subst; apply lsubst_alpha_congr2; eauto 3 with slow. }

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
    eapply approx_ext_starbts_get_bterms_alpha_eq in ap3;[|exact comp'0].

    assert (isprog_vars [vr] w1) as ispw1.
    { apply reduces_atmost_preserves_program in ap4.
      - apply alphaeq_preserves_program in comp'0; apply comp'0 in ap4.
        apply isprogram_subst_implies in ap4.
        apply isprog_vars_iff_isprogram_bt; auto.
      - apply isprogram_subst_if_bt; eauto 3 with slow. }

    assert (!LIn ua' (get_utokens_lib lib u)) as niua'u.
    { intro i; apply Hcv6 in i; sp; rw in_app_iff in i; tcsp. }

    assert (get_op (subst u v (mk_utoken ua')) = get_op u) as gopu.
    { unfsubst; unfold isvalue_like in Hcv0; repndors.
      - apply iscan_implies in Hcv0; repndors; exrepnd; subst; simpl; auto.
      - apply isexc_implies2 in Hcv0; exrepnd; subst; simpl; auto. }

    rw gopu in ap3.

    eexists; eexists; eexists; eexists; dands; eauto;[].

    (* approx_ext_open *)

    apply approx_ext_implies_approx_ext_open.

    remember (get_fresh_atom lib tr) as a.

    pose proof (reduces_in_atmost_k_steps_change_utok_sub
                  lib k0 tr v0 [(vr,mk_utoken ua')] [(vr,mk_utoken a)]) as r.
    allsimpl; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
    allsimpl; allrw disjoint_singleton_l.
    repeat (autodimp r hyp); eauto 3 with slow;
      try (complete (constructor; auto; introv i; rw in_app_iff; tcsp));
      try (complete (rw in_app_iff; tcsp));[| |].

    { apply nr_ut_sub_cons; eauto 3 with slow; intro xx; subst; apply get_fresh_atom_prop_and_lib. }
    { subst; apply get_fresh_atom_prop_and_lib. }

    destruct r as [wr [sr r]]; repnd.

    allrw disjoint_singleton_l.

    allrw @fold_subst.
    pose proof (alpha_eq_lsubst_nrut_sub_implies
                  w1 wr [(vr,mk_utoken ua')]
                  (get_utokens_lib lib w1 ++ get_utokens_lib lib wr)) as aeqws.

    repeat (autodimp aeqws hyp); eauto 4 with slow.

    { apply nrut_sub_cons; simpl; eexists; dands; eauto 3 with slow;
        tcsp; rw in_app_iff; sp; allrw in_app_iff; tcsp. }

    pose proof (reduces_to_fresh lib tr sr vr) as rf; simpl in rf.
    rw <- Heqa in rf.
    repeat (autodimp rf hyp); eauto 3 with slow.
    exrepnd.

    assert (alpha_eq sr (subst w1 vr (mk_utoken a))) as aleq1.
    { eapply alpha_eq_trans;[exact r|].
      apply lsubst_alpha_congr2; eauto 3 with slow. }

    assert (alpha_eq z (subst_utokens (subst w1 vr (mk_utoken a)) [(a,mk_var vr)])) as aleq2.
    { eapply alpha_eq_trans;[exact rf0|].
      apply alpha_eq_subst_utokens; eauto 3 with slow. }

    assert (!LIn a (get_utokens_lib lib w1)) as niaw1.
    { intro xx.
      apply (alphaeq_preserves_get_utokens_lib lib) in aeqws;
        rw aeqws in xx; apply r3 in xx.
      subst; apply get_fresh_atom_prop_and_lib in xx; tcsp. }

    rw in_app_iff in niaw1; apply not_over_or in niaw1; repnd.

    pose proof (simple_alphaeq_subst_utokens_subst w1 vr a niaw0) as aeq3.

    assert (alpha_eq z w1) as aeq4 by eauto 3 with slow.

    apply (approx_ext_trans _ _ (mk_fresh vr z));
      [|apply reduces_to_implies_approx_ext_eauto; auto;
        apply isprogram_fresh; complete auto].

    eapply approx_ext_alpha_rw_r_aux;
      [apply alpha_eq_sym; apply implies_alpha_eq_mk_fresh; exact aeq4|].

    assert (isvalue_like w1) as isvlw1.
    { repeat (rw @cl_subst_subst_aux in ap2; eauto 2 with slow).
      unfold subst_aux in ap2.
      inversion ap2 as [? ? ? e1 e2| ? ? e1 e2|].

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.

        + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
            try (complete (inversion gopu)).

        + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
            try (complete (inversion gopu)); ginv.
          destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
          inversion e2; subst; allsimpl; fold_terms; GC.
          allrw subset_cons_l; repnd; tcsp.
          allrw not_over_or; tcsp.

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
        destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
        destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
    }

    pose proof (compute_step_fresh_if_isvalue_like lib vr w1 isvlw1) as comp.
    apply reduces_to_implies_approx_ext_eauto;
      [apply isprogram_fresh; complete auto|].
    apply reduces_to_if_step; auto.
  }

  Lemma same_value_like_implies_isvalue_like_left {o} :
    forall lib (v1 v2 : @NTerm o),
      same_value_like lib v1 v2 -> isvalue_like v1.
  Proof.
    introv same.
    inversion same; eauto 3 with slow.
  Qed.
  Hint Resolve same_value_like_implies_isvalue_like_left : slow.

  Lemma same_value_like_implies_isvalue_like_right {o} :
    forall lib (v1 v2 : @NTerm o),
      same_value_like lib v1 v2 -> isvalue_like v2.
  Proof.
    introv same.
    inversion same; eauto 3 with slow.
  Qed.
  Hint Resolve same_value_like_implies_isvalue_like_right : slow.

  Lemma isvalue_like_subst_change_utokens {o} :
    forall (t : @NTerm o) v a b,
      isvalue_like (subst t v (mk_utoken a))
      -> isvalue_like (subst t v (mk_utoken b)).
  Proof.
    introv isv.
    unfsubst; unfsubst in isv.
    destruct t as [w|f|op bs]; simpl in *; auto.
    boolvar; auto.
  Qed.

  Lemma length_mk_fresh_bterms {o} :
    forall v (bs : list (@BTerm o)),
      length (mk_fresh_bterms v bs) = length bs.
  Proof.
    introv.
    unfold mk_fresh_bterms; autorewrite with list; auto.
  Qed.
  Hint Rewrite @length_mk_fresh_bterms : slow.

  Definition blift_sub2 {o}
             lib
             (op : @Opid o)
             (R : NTrel)
             (b1 b2: @BTerm o) : [univ] :=
    forall l,
      {lv : list NVar
                 $ {nt1,nt2 : NTerm
                                $ (
                                  (op <> NCan NFresh # R nt1 nt2)
                                    [+]
                                    {sub : Sub
                                           & op = NCan NFresh
                                                       # R (lsubst nt1 sub) (lsubst nt2 sub)
                                                       # nrut_sub (l ++ get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2) sub
                                                       # lv = dom_sub sub}
                                )
                                # alpha_eq_bterm b1 (bterm lv nt1)
                                # alpha_eq_bterm b2 (bterm lv nt2) }}.

  Lemma blift_sub2_implies_blift_sub {o} :
    forall lib op (b1 b2 : @BTerm o) bs1 bs2,
      wf_term (oterm op bs1)
      -> wf_term (oterm op bs2)
      -> LIn (b1, b2) (combine bs1 bs2)
      -> blift_sub2 lib op (approx_ext_star lib) b1 b2
      -> blift_sub lib op (approx_ext_star lib) b1 b2.
  Proof.
    introv wf1 wf2 ic h.
    unfold blift_sub.
    unfold blift_sub2 in h.

    destruct (dec_op_eq_fresh op) as [d|d]; subst.

    - pose proof (h []) as q; exrepnd.
      exists lv nt1 nt2; dands; auto.
      right.
      introv.
      pose proof (h l) as w; exrepnd; repndors; exrepnd; tcsp.
      clear h.
      subst.

      apply wf_oterm_iff in wf1.
      apply wf_oterm_iff in wf2.
      repnd; simpl in *.
      repeat (destruct bs1; simpl in *; ginv).
      repeat (destruct bs2; simpl in *; ginv).
      destruct b as [l1 t1]; destruct b0 as [l2 t2]; unfold num_bvars in *; simpl in *.
      destruct l1 as [|v1]; simpl in *; ginv; destruct l1; simpl in *; ginv.
      destruct l2 as [|v2]; simpl in *; ginv; destruct l2; simpl in *; ginv.
      repndors; tcsp; ginv.

      applydup @alphaeqbt_numbvars in q0.
      applydup @alphaeqbt_numbvars in w0.
      unfold num_bvars in *; simpl in *.
      destruct sub0 as [|p1]; simpl in *; ginv; destruct sub0; simpl in *; ginv.
      destruct sub as [|p2]; simpl in *; ginv; destruct sub; simpl in *; ginv.
      destruct p1 as [z1 u1].
      destruct p2 as [z2 u2].
      simpl in *.

      exists [(z1,u2)]; dands; auto.

      + eapply approx_ext_star_alpha_fun_l;
          [eapply approx_ext_star_alpha_fun_r|];
          [exact w4| | ].

        * assert (alpha_eq_bterm (bterm [z2] nt3) (bterm [z1] nt2)) as aeq.
          { eapply alpha_eq_bterm_trans;[|exact q0].
            apply alpha_eq_bterm_sym;auto. }
          apply (apply_bterm_alpha_congr2 _ _ [u2]) in aeq;
            unfold num_bvars in *; simpl in *; auto.

        * assert (alpha_eq_bterm (bterm [z2] nt0) (bterm [z1] nt1)) as aeq.
          { eapply alpha_eq_bterm_trans;[|exact q2].
            apply alpha_eq_bterm_sym;auto. }
          apply (apply_bterm_alpha_congr2 _ _ [u2]) in aeq;
            unfold num_bvars in *; simpl in *; auto.

      + unfold nrut_sub, get_utokens_sub in *; simpl in *; repnd; dands; auto.

        * apply ut_sub_cons in w1; repnd.
          apply ut_sub_cons; dands; auto.

        * apply alpha_eq_bterm_preserves_utokens in q0.
          apply alpha_eq_bterm_preserves_utokens in w0.
          apply alpha_eq_bterm_preserves_utokens in q2.
          apply alpha_eq_bterm_preserves_utokens in w2.
          simpl in *.
          unfold get_utokens_lib in *.
          rewrite <- q2; rewrite w2.
          rewrite <- q0; rewrite w0; auto.

    - pose proof (h []) as q; exrepnd.
      exists lv nt1 nt2; dands; auto.
      repndors; tcsp.
  Qed.

  assert {w1 : NTerm
          & forall l,
            {ua' : get_patom_set p
              & {k0 : nat
              & {v0 : NTerm
              & isprog_vars [vr] tr
              # isprog_vars [vr] w1
              # !LIn ua' l
              # !LIn ua' (get_utokens tr)
              # !LIn ua' (get_utokens_library lib)
              # !LIn ua' (get_utokens_lib lib w1)
              # !LIn ua' (get_utokens_lib lib u)
              # subset (get_utokens_lib lib w1) (get_utokens_lib lib tr)
              # reduces_in_atmost_k_steps lib (subst tr vr (mk_utoken ua')) v0 k0
              # alpha_eq v0 (subst w1 vr (mk_utoken ua'))
              # same_value_like lib (subst u v (mk_utoken ua')) (subst w1 vr (mk_utoken ua'))
              # approx_ext_starbts lib (get_op u) (get_bterms (subst u v (mk_utoken ua'))) (get_bterms (subst w1 vr (mk_utoken ua')))
              # get_op (subst u v (mk_utoken ua')) = get_op u
              # approx_ext_open lib (pushdown_fresh vr w1) (mk_fresh vr tr)}}}} as ah'.
  {
    pose proof (ah []) as ahnil; exrepnd.
    exists w1.
    introv.
    pose proof (ah l) as ahl; exrepnd.
    clear ah.

    assert (alpha_eq w1 w0) as aeqw.
    {
      pose proof (reduces_in_atmost_k_steps_change_utok_sub
                    lib k0 tr v0
                    [(vr,mk_utoken ua')]
                    [(vr,mk_utoken ua'0)]) as q.
      repeat (autodimp q hyp); eauto 3 with slow.
      { apply nr_ut_sub_cons; eauto 3 with slow; intro xx; subst.
        unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp. }
      { apply nr_ut_sub_cons; eauto 3 with slow; intro xx; subst.
        unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp. }
      { unfold get_utokens_sub; simpl; apply disjoint_singleton_l.
        unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp. }
      { unfold get_utokens_sub; simpl; apply disjoint_singleton_l.
        unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp. }
      exrepnd.

      assert (alpha_eq (lsubst w2 [(vr, mk_utoken ua')]) (subst w1 vr (mk_utoken ua'))) as aeqw.
      { eapply alpha_eq_trans;[apply alpha_eq_sym;eauto|];auto. }

      apply (alpha_eq_lsubst_nrut_sub_implies _ _ _ (get_utokens_lib lib tr)) in aeqw; eauto 3 with slow;
        [|apply nrut_sub_cons; exists ua'; simpl; dands; tcsp; eauto 2 with slow;
          unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp
         |eapply subset_trans;[|exact q4]; eauto 3 with slow
         |eapply subset_trans;[|exact ahnil8]; eauto 3 with slow];[].

      assert (isvalue_like v0) as isv1.
      {
        eapply alpha_eq_preserves_isvalue_like_left;[|exact ahnil10].
        allrw @fold_subst; eauto 3 with slow.
      }

      assert (isvalue_like v1) as isv2.
      {
        eapply alpha_eq_preserves_isvalue_like_left;[|exact ahl10].
        allrw @fold_subst; eauto 3 with slow.
      }

      assert (isvalue_like s) as isv3.
      {
        eapply alpha_eq_preserves_isvalue_like_left;[|exact q1].
        eapply isvalue_like_subst_change_utokens.
        eapply alpha_eq_preserves_isvalue_like_left;[|apply alpha_eq_sym;exact q0]; auto.
      }

      assert (isprogram v1) as isp1.
      {
        split.
        - apply closed_null_free_vars.
          introv i.
          eapply reduces_to_free_vars in i;[| |exists k1; eauto]; eauto 3 with slow;[].
          apply isprog_vars_eq in ahl0; repnd.
          unfold subst in i.
          rewrite @free_vars_cl_lsubst in i; eauto 3 with slow;[].
          simpl in i.
          allrw in_remove_nvars; simpl in *; repnd.
          apply subvars_eq in ahl14; apply ahl14 in i0; simpl in *; tcsp.
        - eapply reduces_in_atmost_k_Steps_preserves_wf;[eauto|].
          eauto 3 with slow.
      }

      assert (isprogram s) as isp2.
      {
        split.
        - apply closed_null_free_vars.
          introv i.
          eapply reduces_to_free_vars in i;[| |exists k0; eauto]; eauto 3 with slow;[|].
          { apply isprog_vars_eq in ahl0; repnd.
            unfold subst in i.
            rewrite @free_vars_cl_lsubst in i; eauto 3 with slow;[].
            simpl in i.
            allrw in_remove_nvars; simpl in *; repnd.
            apply subvars_eq in ahl14; apply ahl14 in i0; simpl in *; tcsp. }
          { apply lsubst_wf_if_eauto; eauto 3 with slow. }
        - eapply reduces_in_atmost_k_Steps_preserves_wf;[eauto|].
          apply lsubst_wf_if_eauto; eauto 3 with slow.
      }

      assert (s = v1) as eqv.
      {
        destruct (le_dec k1 k0).

        {
          apply (no_change_after_val_like3 _ _ _ _ k0) in ahl9; auto;[].
          unfold subst in ahl9.
          unfold reduces_in_atmost_k_steps in *.
          rewrite ahl9 in q5; ginv.
        }

        {
          apply (no_change_after_val_like3 _ _ _ _ k1) in q5; auto; try omega;[].
          unfold subst in ahl9.
          unfold reduces_in_atmost_k_steps in *.
          rewrite ahl9 in q5; ginv.
        }
      }

      subst s.

      assert (alpha_eq (lsubst w2 [(vr, mk_utoken ua'0)]) (subst w0 vr (mk_utoken ua'0))) as aeqw'.
      { eapply alpha_eq_trans;[apply alpha_eq_sym;eauto|];auto. }

      apply (alpha_eq_lsubst_nrut_sub_implies _ _ _ (get_utokens_lib lib tr)) in aeqw'; eauto 3 with slow;
        [apply nrut_sub_cons; exists ua'0; simpl; dands; tcsp; eauto 2 with slow;
         unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp
        |eapply subset_trans;[|exact q4]; eauto 3 with slow
        |eapply subset_trans;[|exact ahl8]; eauto 3 with slow].
    }


    exists ua'0 k1 v1; dands; auto.

    { erewrite alphaeq_preserves_get_utokens_lib;[|exact aeqw];auto. }

    { eapply alpha_eq_trans;[exact ahl10|].
      apply lsubst_alpha_congr2; auto; eauto 3 with slow. }

    { eapply same_value_like_alpha_eq_r;[exact ahl11|].
      apply lsubst_alpha_congr2; auto; eauto 3 with slow. }

    { eapply approx_ext_starbts_get_bterms_alpha_eq;[exact ahl12|].
      apply lsubst_alpha_congr2; auto; eauto 3 with slow. }
  }
  clear ah; rename ah' into ah.
  exrepnd.

  assert (approx_ext_open lib (pushdown_fresh vr w1) (mk_fresh vr tr)
          # isprog_vars [v] u
          # isprog_vars [vr] tr
          # isprog_vars [vr] w1
          # forall l,
             {a : get_patom_set p
              & !LIn a l
              # !LIn a (get_utokens_lib lib u)
              (*# !LIn a (get_utokens_lib lib tr)*)
              # !LIn a (get_utokens_lib lib w1)
              # same_value_like lib (subst u v (mk_utoken a)) (subst w1 vr (mk_utoken a))
              # approx_ext_starbts lib (get_op u) (get_bterms (subst u v (mk_utoken a))) (get_bterms (subst w1 vr (mk_utoken a))) } ) as ah.
  {
    pose proof (ah0 []) as ahnil; exrepnd; dands; auto.
    { eapply alphaeq_preserves_isprog_vars;[apply alpha_eq_sym;eauto|].
      apply isprogram_pushdown_fresh; auto. }
    introv.
    pose proof (ah0 l) as ah; exrepnd.
    exists ua'0; dands; auto; eauto 3 with slow.
    (*{ unfold get_utokens_lib; rw in_app_iff; rw not_over_or; tcsp. }*)
  }
  clear ah0.
  repnd.

  eapply approx_ext_star_open_trans;[|exact ah0].

  Lemma wf_term_oterm_mk_fresh_bterms {o} :
    forall op v (bs : list (@BTerm o)),
      wf_term (oterm op bs) -> wf_term (oterm op (mk_fresh_bterms v bs)).
  Proof.
    introv wf.
    allrw @wf_oterm_iff; repnd.
    rewrite <- wf0.
    unfold mk_fresh_bterms.
    rewrite map_map; unfold compose.
    dands.

    - apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

    - introv i.
      apply in_map_iff in i; exrepnd; subst.
      apply bt_wf_eq.
      apply bt_wf_mk_fresh_bterm_if.
      apply bt_wf_eq; tcsp.
  Qed.
  Hint Resolve wf_term_oterm_mk_fresh_bterms : slow.

Lemma approx_ext_star_pushdown_fresh_if_subst {o} :
  forall lib (t1 t2 : @NTerm o) v1 v2,
    isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall l,
           {a : get_patom_set o
            & !LIn a l
            # !LIn a (get_utokens_lib lib t1)
            # !LIn a (get_utokens_lib lib t2)
            # same_value_like lib (subst t1 v1 (mk_utoken a)) (subst t2 v2 (mk_utoken a))
            # approx_ext_starbts lib (get_op t1) (get_bterms (subst t1 v1 (mk_utoken a))) (get_bterms (subst t2 v2 (mk_utoken a)))})
    -> approx_ext_star lib (pushdown_fresh v1 t1) (pushdown_fresh v2 t2).
Proof.
  introv isp1 isp2 imp.

  pose proof (ex_fresh_var (all_vars t1
                                     ++ all_vars t2))
    as fv; exrepnd.
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (alpha_bterm_change
                (bterm [v1] t1) [v1] t1 [v]) as aeqbt1.
  allrw disjoint_singleton_r.
  allrw in_app_iff; allrw not_over_or.
  allsimpl.
  repeat (autodimp aeqbt1 hyp).

  pose proof (alpha_bterm_change
                (bterm [v2] t2) [v2] t2 [v]) as aeqbt2.
  allrw disjoint_singleton_r.
  allrw in_app_iff; allrw not_over_or.
  allsimpl.
  repeat (autodimp aeqbt2 hyp).

  remember (lsubst t1 (var_ren [v1] [v])) as nt1.
  remember (lsubst t2 (var_ren [v2] [v])) as nt2.

  unfold get_utokens_lib in *.

  applydup @alpha_eq_bterm_preserves_utokens in aeqbt1 as ut1; allsimpl.
  rw ut1 in imp.
  applydup @alpha_eq_bterm_preserves_utokens in aeqbt2 as ut2; allsimpl.
  rw ut2 in imp.

  eapply alpha_eq_bterm_preserves_isprog_vars in isp1;[|exact aeqbt1].
  eapply alpha_eq_bterm_preserves_isprog_vars in isp2;[|exact aeqbt2].

  assert (forall l,
           {a : get_patom_set o
            & !LIn a l
            # !LIn a (get_utokens_lib lib nt1)
            # !LIn a (get_utokens_lib lib nt2)
            # same_value_like lib (subst nt1 v (mk_utoken a)) (subst nt2 v (mk_utoken a))
            # approx_ext_starbts lib (get_op nt1) (get_bterms (subst nt1 v (mk_utoken a))) (get_bterms (subst nt2 v (mk_utoken a)))}) as imp'.
  {
    introv.
    pose proof (imp l) as q; exrepnd.

    pose proof (lsubst_alpha_congr4 [v1] [v] t1 nt1 [(v1,mk_utoken a)] [(v,mk_utoken a)]) as c1.
    allsimpl.
    repeat (autodimp c1 hyp); eauto 3 with slow.

    pose proof (lsubst_alpha_congr4 [v2] [v] t2 nt2 [(v2,mk_utoken a)] [(v,mk_utoken a)]) as c2.
    allsimpl.
    repeat (autodimp c2 hyp); eauto 3 with slow.

    allrw @fold_subst.

    eapply same_value_like_alpha_eq_r in q4;[|exact c2].
    eapply same_value_like_alpha_eq_l in q4;[|exact c1].

    assert (get_op t1 = get_op nt1) as go.
    { subst; rw @lsubst_lsubst_aux; allrw <- @sub_free_vars_is_flat_map_free_vars_range;
        allsimpl; allrw disjoint_singleton_r; auto.
      destruct t1; simpl; boolvar; simpl; tcsp. }
    rw go in q0.

    eapply approx_ext_starbts_get_bterms_alpha_eq in q0;[|exact c2].
    eapply approx_ext_starbts_get_bterms_alpha_eq_l in q0;[|exact c1].

    exists a; dands; auto.
  }
  clear imp; rename imp' into imp.

  applydup @implies_alpha_eq_pushdown_fresh in aeqbt1 as apf1.
  applydup @implies_alpha_eq_pushdown_fresh in aeqbt2 as apf2.

  eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact apf1].
  eapply approx_ext_star_alpha_fun_r;[|apply alpha_eq_sym; exact apf2].

  clear dependent t1.
  clear dependent t2.
  rename nt1 into t1.
  rename nt2 into t2.

  destruct t1 as [x|f|op bs]; allsimpl; tcsp; GC.

  - pose proof (imp []) as imp.
    destruct imp as [a [nal [na1 [na2 [svl ap]]]]].
    repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

    boolvar.

    + apply approx_ext_open_implies_approx_ext_star.
      apply approx_ext_implies_approx_ext_open.
      apply (approx_ext_trans _ _ (mk_fresh x (mk_var x))).

      * apply reduces_to_implies_approx_ext2.
        { apply isprogram_fresh.
          apply isprog_vars_var. }
        apply reduces_to_if_step.
        csunf; simpl; boolvar; auto.

      * apply fresh_id_approx_ext_any.
        apply isprogram_pushdown_fresh; auto.

    + inversion svl.

  - pose proof (imp []) as imp.
    destruct imp as [a [nal [na1 [na2 [svl ap]]]]].
    repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

    autorewrite with slow in *.
    destruct t2 as [v2|f2|op bs]; allsimpl; boolvar; allsimpl;
    try (complete (inversion svl)); eauto 4 with slow.
    inversion svl; subst; clear svl.
    allrw @isprog_vars_eq; repnd.
    econstructor;[| |eauto|]; eauto 3 with slow.

  - allsimpl.
    destruct t2 as [x|f|op' bs']; allsimpl; GC.

    + pose proof (imp []) as imp.
      destruct imp as [a [nal [na1 [na2 [svl ap]]]]].
      repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

      boolvar; try (complete (inversion svl)).
      inversion svl; subst; allsimpl.
      allrw not_over_or; sp.

    + pose proof (imp []) as imp.
      destruct imp as [a [nal [na1 [na2 [svl ap]]]]].
      repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

      try (complete (inversion svl)).

    + pose proof (imp []) as q.
      destruct q as [a0 [nal [na1 [na2 [svl ap]]]]].
      clear nal na1 na2.
      repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

      applydup @same_value_like_implies_same_op in svl; subst.
      clear svl.

      assert (length bs = length bs') as e.
      {  unfold approx_ext_starbts, lblift_sub in ap; repnd; allrw map_length.
         unfold mk_fresh_bterms; allrw map_length; auto. }
      clear ap.

      (* xxxxxxxxxxxxxx *)

      apply (apso _ _ _ _ (mk_fresh_bterms v bs')); auto;
        try (apply approx_ext_open_refl);
        [unfold mk_fresh_bterms; allrw map_length; auto
        |idtac
        |apply isprog_vars_eq in isp2; repnd;
         allrw @nt_wf_oterm_iff; repnd;
         rw <- isp3;
         unfold mk_fresh_bterms; allrw map_map; unfold compose; dands;
         [ apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto|];
         introv i; allrw in_map_iff; exrepnd; subst;
         apply isp2 in i1; apply bt_wf_mk_fresh_bterm_if; complete auto].

      apply lblift_sub_eq; autorewrite with slow; dands; auto.
      introv i.

      apply (blift_sub2_implies_blift_sub _ _ _ _ (mk_fresh_bterms v bs) (mk_fresh_bterms v bs')); eauto 3 with slow;[].
      unfold mk_fresh_bterms in i.
      rewrite <- map_combine in i.
      apply in_map_iff in i; exrepnd; ginv.
      rename a1 into b1.
      rename a into b2.

(*      unfold lblift_sub, mk_fresh_bterms; dands; allrw map_length; auto.
      introv i.
      repeat (rw @selectbt_map; auto; try omega).

      unfold approx_ext_starbts, lblift_sub in ap; repnd; allrw map_length; GC.
      pose proof (ap n i) as k; clear ap.
      repeat (rw @selectbt_map in k; auto; try omega).
      allunfold @selectbt.*)

(*      pose proof (in_nth_combine _ _ bs bs' n default_bt default_bt) as h.
      repeat (autodimp h hyp).
      remember (nth n bs default_bt)  as b1; clear Heqb1.
      remember (nth n bs' default_bt) as b2; clear Heqb2.
      allrw in_app_iff; allrw not_over_or; repnd.
      applydup in_combine in h; repnd.
      assert (!LIn a (get_utokens_b b1)) as niab1.
      { introv q; destruct ni3; rw lin_flat_map; eexists; dands; eauto. }
      assert (!LIn a (get_utokens_b b2)) as niab2.
      { introv q; destruct ni0; rw lin_flat_map; eexists; dands; eauto. }*)

(* new stuff *)




      introv.
      pose proof (imp l) as imp.
      destruct imp as [a [nal [na1 [na2 [svl ap]]]]].
      repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.

      apply lblift_sub_eq in ap; autorewrite with slow in *.
      repnd; GC.
      rewrite <- map_combine in ap.
      pose proof (ap (lsubst_bterm_aux b1 [(v, mk_utoken a)])
                     (lsubst_bterm_aux b2 [(v, mk_utoken a)])) as ap.
      autodimp ap hyp.
      { apply in_map_iff; eexists; dands; eauto. }
      unfold get_utokens_lib in *; simpl in *.
      allrw in_app_iff; allrw not_over_or; repnd.
      applydup in_combine in i1; repnd.
      assert (!LIn a (get_utokens_b b1)) as niab1.
      { introv q; destruct na4; rw lin_flat_map; eexists; dands; eauto. }
      assert (!LIn a (get_utokens_b b2)) as niab2.
      { introv q; destruct na0; rw lin_flat_map; eexists; dands; eauto. }

      apply (blift_sub_diff (v :: maybe_new_var_b v b1
                               :: maybe_new_var_b v b2
                               :: all_vars_bterm b1
                               ++ all_vars_bterm b2)) in ap.
      exrepnd.
      allrw disjoint_cons_r; allrw disjoint_cons_l; allrw disjoint_app_r; allrw disjoint_app_l; repnd.

      assert (wf_term nt1) as wfnt1.
      { repndors; exrepnd.
        - allapply @approx_ext_star_relates_only_wf; repnd; eauto 2 with slow.
        - pose proof (ap2 l) as k1; exrepnd.
          allapply @approx_ext_star_relates_only_wf; repnd.
          allapply @lsubst_nt_wf; eauto with slow. }

      assert (wf_term nt2) as wfnt2.
      { repndors; exrepnd.
        - allapply @approx_ext_star_relates_only_wf; repnd; eauto 2 with slow.
        - pose proof (ap2 l) as k1; exrepnd.
          allapply @approx_ext_star_relates_only_wf; repnd.
          allapply @lsubst_nt_wf; eauto with slow. }

      pose proof (alpha_eq_subst_bterm_aux_pull_out_token b1 v a lv nt1) as exs1.
      repeat (autodimp exs1 hyp); exrepnd.
      subst nt1.
      rename u into nt1.

      pose proof (alpha_eq_subst_bterm_aux_pull_out_token b2 v a lv nt2) as exs2.
      repeat (autodimp exs2 hyp); exrepnd.
      subst nt2.
      rename u into nt2.

      assert (disjoint lv (bound_vars nt1)) as disjlvnt1.
      { introv j1 j2.
        apply ap8 in j1; destruct j1.
        unfsubst.
        rw (bound_vars_lsubst_aux_nrut_sub nt1 [(v,mk_utoken a)] []); auto.
        apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp. }

      assert (disjoint lv (bound_vars nt2)) as disjlvnt2.
      { introv j1 j2.
        apply ap9 in j1; destruct j1.
        unfsubst.
        rw (bound_vars_lsubst_aux_nrut_sub nt2 [(v,mk_utoken a)] []); auto.
        apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp. }

      unfold blift_sub.

      pose proof (alpha_eq_bterm_mk_fresh_bterm_berm b1 v a lv nt1) as e1.
      repeat (autodimp e1 hyp); eauto 3 with slow.

      pose proof (alpha_eq_bterm_mk_fresh_bterm_berm b2 v a lv nt2) as e2.
      repeat (autodimp e2 hyp); eauto 3 with slow.

      exists lv (mk_fresh v nt1) (mk_fresh v nt2); dands; auto.

      (* here comes trouble! *)

      repndors;[left|right].

      * repnd; dands; auto.
        apply (apso _ _ _ _ [bterm [v] nt2]); allsimpl; auto; fold_terms;
          [|apply approx_ext_open_refl; allrw <- @nt_wf_eq;
            allapply @lsubst_nt_wf; apply nt_wf_fresh; auto].
        unfold lblift_sub; simpl; dands; auto; introv q; destruct n; cpx.
        unfold selectbt; simpl.
        unfold blift_sub.

        exists [v] nt1 nt2; dands; auto.
        right.
        exists [(v,mk_utoken a)]; simpl; dands; auto.
        apply nrut_sub_cons; simpl; eexists; dands; eauto 3 with slow; tcsp.
        repeat (rw in_app_iff); sp.

        admit.

      * exrepnd.

        pose proof (exists_nrut_sub
                      (dom_sub sub)
                      (a :: get_utokens_lib lib (subst nt1 v (mk_utoken a))
                         ++ get_utokens_lib lib (subst nt2 v (mk_utoken a))))
          as ens; exrepnd.

        pose proof (approx_ext_star_change_nrut_sub
                      lib
                      (subst nt1 v (mk_utoken a))
                      (subst nt2 v (mk_utoken a))
                      sub
                      (get_utokens_lib lib (subst nt1 v (mk_utoken a)) ++ get_utokens_lib lib (subst nt2 v (mk_utoken a)))
                      sub0
                      (a :: get_utokens_lib lib (subst nt1 v (mk_utoken a)) ++ get_utokens_lib lib (subst nt2 v (mk_utoken a))))
          as aps; repeat (autodimp aps hyp); eauto 5 with slow;[].

        exists sub0; dands; auto; simpl; allrw app_nil_r;
        try (complete (subst; auto));
        [|eapply nrut_sub_subset;[|exact ens1]; apply subset_cons1;
          apply subset_app_lr; introv z;
          apply get_utokens_lib_subst; boolvar; simpl;
          autorewrite with slow in *;
          repeat (rw app_nil_r); repeat (rw in_app_iff); tcsp;
          try (complete (unfold get_utokens_lib in *; allrw in_app_iff; tcsp))];[].

        repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow); simpl; fold_terms.
        apply (apso _ _ _ _ [bterm [v] (lsubst_aux nt2 (sub_filter sub0 [v]))]); allsimpl; auto; fold_terms;
        [|apply approx_ext_open_refl; allrw <- @nt_wf_eq;
          allapply @lsubst_nt_wf; apply nt_wf_fresh; auto;
          apply implies_wf_lsubst_aux; eauto 3 with slow];[].
        unfold lblift_sub; simpl; dands; auto; introv q; destruct n0; cpx.
        unfold selectbt; simpl.
        unfold blift_sub.

        allunfold @subst.
        rw (cl_lsubst_swap_sub_filter nt1) in aps; eauto 3 with slow.
        rw (cl_lsubst_swap_sub_filter nt2) in aps; eauto 3 with slow.
        allsimpl.

        assert (!LIn a (get_utokens_sub sub0)) as niasub.
        { intro z; unfold nrut_sub in ens1; repnd; allrw disjoint_cons_l; sp. }

        exists [v] (lsubst_aux nt1 (sub_filter sub0 [v])) (lsubst_aux nt2 (sub_filter sub0 [v])); dands; auto.
        right.
        exists [(v,mk_utoken a)]; simpl; dands; auto.
        { repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow). }
        apply nrut_sub_cons; simpl; eexists; dands; eauto 2 with slow; tcsp.

        rw in_app_iff; rw not_over_or; dands; intro z;
          apply get_utokens_lib_lsubst_aux_subset in z; rw in_app_iff in z; repndors; tcsp;
            try (apply get_utokens_sub_filter_subset in z; tcsp);
            try (complete (apply in_app_iff in z; repndors; tcsp)).
Qed.




XXXXXXXXX

  unfold approx_ext_star_bterm, blift_sub in Has0bt; exrepnd; repndors; exrepnd; tcsp; GC.
  (* == we commit here to a list of forbidden names == *)
  pose proof (Has0bt1 (get_utokens t ++ get_utokens tr)) as Has0bt1.
  exrepnd; GC.
  applydup @alpha_eq_bterm_implies_eq_length in Has0bt2.
  allsimpl; destruct lv as [|v']; allsimpl; tcsp.
  destruct lv; allsimpl; tcsp; GC; try omega.
  destruct sub as [|vt]; simpl in *; ginv.
  destruct vt as [vt ta]; simpl in *.
  destruct sub; simpl in *; try (inversion Has0bt3); subst vt; GC.
  apply nrut_sub_cons in Has0bt5; exrepnd; simpl in *; GC.

  clear Has0bt1.

  subst ta.
  rename a into ua'.

  pose proof (lsubst_alpha_congr4 [v] [v'] t nt1 [(v,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq1.
  repeat (autodimp aeq1 hyp); simpl; eauto 2 with slow.
  pose proof (lsubst_alpha_congr4 [vr] [v'] tr nt2 [(vr,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq2.
  repeat (autodimp aeq2 hyp); simpl; eauto 2 with slow.
  allrw @fold_subst.

  eapply approx_ext_star_alpha_fun_l in Has0bt4;[|apply alpha_eq_sym;eauto].
  eapply approx_ext_star_alpha_fun_r in Has0bt4;[|apply alpha_eq_sym;eauto].

(*XXXXX*)

(*  pose proof (fresh_atom p (get_utokens_lib lib (mk_pair t tr))) as fa.
  destruct fa as [ua' fa]; allsimpl; allrw app_nil_r.*)
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
  { assert (alpha_eq (subst u v (mk_utoken ua)) (subst w0 v (mk_utoken ua))) as h by eauto 3 with slow.
    pose proof (change_bvars_alpha_wspec [v] u) as k1.
    pose proof (change_bvars_alpha_wspec [v] w0) as k2.
    exrepnd.
    allrw disjoint_singleton_l.
    pose proof (lsubst_alpha_congr2 ntcv0 u [(v,mk_utoken ua)]) as p1.
    pose proof (lsubst_alpha_congr2 ntcv w0 [(v,mk_utoken ua)]) as p2.
    autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
    allrw @fold_subst.
    assert (alpha_eq (subst ntcv0 v (mk_utoken ua)) (subst ntcv v (mk_utoken ua))) as h' by eauto 4 with slow.
    apply alpha_eq_subst_utoken_not_in_implies in h'; eauto 4 with slow;[|].
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
  { apply isprogram_subst_if_bt; eauto 3 with slow. }
  { apply isprogram_subst_if_bt; eauto 3 with slow. }
(*  { unfold approx_ext_star_bterm, blift_sub in Has0bt; exrepnd; repndors; exrepnd; tcsp; GC.
    applydup @alpha_eq_bterm_implies_eq_length in Has0bt2.
    allsimpl; destruct lv as [|v']; allsimpl; tcsp.
    destruct lv; allsimpl; tcsp; GC; try omega.
    pose proof (lsubst_alpha_congr4 [v] [v'] t nt1 [(v,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq1.
    repeat (autodimp aeq1 hyp); simpl; eauto 2 with slow.
    pose proof (lsubst_alpha_congr4 [vr] [v'] tr nt2 [(vr,mk_utoken ua')] [(v',mk_utoken ua')]) as aeq2.
    repeat (autodimp aeq2 hyp); simpl; eauto 2 with slow.
    allrw @fold_subst.
    eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact aeq1].
    eapply approx_ext_star_alpha_fun_r;[|apply alpha_eq_sym; exact aeq2].

    pose proof (approx_ext_star_change_nrut_sub
                  lib nt1 nt2 sub
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)
                  [(v',mk_utoken ua')]
                  (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2)) as q.
    allsimpl; repeat (autodimp q hyp); eauto 5 with slow;[].

    apply nrut_sub_cons; eexists; dands; simpl; eauto 3 with slow; tcsp;[].
    apply alpha_eq_bterm_preserves_utokens in Has0bt2.
    apply alpha_eq_bterm_preserves_utokens in Has0bt0.
    allsimpl.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt2.
    apply (eq_get_utokens_implies_eq_get_utokens_lib lib) in Has0bt0.
    rw <- Has0bt2; rw <- Has0bt0.
    repeat (rw in_app_iff); repeat (rw in_app_iff); sp.
  }*)

  pose proof (approx_ext_star_alpha_fun_l lib s (subst tr vr (mk_utoken ua')) (subst u v (mk_utoken ua'))) as ap1.
  repeat (autodimp ap1 hyp).
  { eapply alpha_eq_trans;[exact comp1|].
    unfold subst; apply lsubst_alpha_congr2; eauto 3 with slow. }

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
  eapply approx_ext_starbts_get_bterms_alpha_eq in ap3;[|exact comp'0].

  assert (isprog_vars [vr] w1) as ispw1.
  { apply reduces_atmost_preserves_program in ap4.
    - apply alphaeq_preserves_program in comp'0; apply comp'0 in ap4.
      apply isprogram_subst_implies in ap4.
      apply isprog_vars_iff_isprogram_bt; auto.
    - apply isprogram_subst_if_bt; eauto 3 with slow. }

  assert (!LIn ua' (get_utokens_lib lib u)) as niua'u.
  { intro i; apply Hcv6 in i; sp; rw in_app_iff in i; tcsp. }

  assert (get_op (subst u v (mk_utoken ua')) = get_op u) as gopu.
  { unfsubst; unfold isvalue_like in Hcv0; repndors.
    - apply iscan_implies in Hcv0; repndors; exrepnd; subst; simpl; auto.
    - apply isexc_implies2 in Hcv0; exrepnd; subst; simpl; auto. }

  rw gopu in ap3.

XXXX
  clear ap1 comp'3 comp'4 Heqskm Has0bt2 Has0bt0 Has0 Hcv9 Hcv2 Hcv aeq1 aeq2 Has0bt4 Hcv7 Hcv4 Hcv5 Hcv6 comp0 comp3 comp4 comp5 Hi Hcv1 Hcv8 Hcv0 Hprt isvx aeq aeq0 Has0bt8 ispu.
  clear dependent skm.
  clear dependent ua.
  clear dependent s.
  clear dependent k.
  clear dependent x.
  clear dependent nt1.
  clear dependent nt2.
  clear dependent t.
  clear dependent w.
  clear dependent m.
  clear dependent v'.
  clear dependent w0.

  (* keep ap4 ap2 ap3 Hprt' comp'0 comp'2 Has0bt1 Has0bt3 ispw1 niua'u gopu *)

  rev_assert apspf (approx_ext_star lib (pushdown_fresh v u) (pushdown_fresh vr w1)).

  {
    eapply approx_ext_star_open_trans;[exact apspf|].

    apply approx_ext_implies_approx_ext_open.

    remember (get_fresh_atom lib tr) as a.

    pose proof (reduces_in_atmost_k_steps_change_utok_sub
                  lib k0 tr v0 [(vr,mk_utoken ua')] [(vr,mk_utoken a)]) as r.
    allsimpl; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
    allsimpl; allrw disjoint_singleton_l.
    repeat (autodimp r hyp); eauto 3 with slow;
      try (complete (constructor; auto; introv i; rw in_app_iff; tcsp));
      try (complete (rw in_app_iff; tcsp));[| |].

    { apply nr_ut_sub_cons; eauto 3 with slow; intro xx; subst; apply get_fresh_atom_prop_and_lib. }
    { subst; apply get_fresh_atom_prop_and_lib. }

    destruct r as [wr [sr r]]; repnd.

    allrw disjoint_singleton_l.

    allrw @fold_subst.
    pose proof (alpha_eq_lsubst_nrut_sub_implies
                  w1 wr [(vr,mk_utoken ua')]
                  (get_utokens_lib lib w1 ++ get_utokens_lib lib wr)) as aeqws.

    repeat (autodimp aeqws hyp); eauto 4 with slow.

    { apply nrut_sub_cons; simpl; eexists; dands; eauto 3 with slow;
        tcsp; rw in_app_iff; sp; allrw in_app_iff; tcsp. }

    pose proof (reduces_to_fresh lib tr sr vr) as rf; simpl in rf.
    rw <- Heqa in rf.
    repeat (autodimp rf hyp); eauto 3 with slow.
    exrepnd.

    assert (alpha_eq sr (subst w1 vr (mk_utoken a))) as aleq1.
    { eapply alpha_eq_trans;[exact r|].
      apply lsubst_alpha_congr2; eauto 3 with slow. }

    assert (alpha_eq z (subst_utokens (subst w1 vr (mk_utoken a)) [(a,mk_var vr)])) as aleq2.
    { eapply alpha_eq_trans;[exact rf0|].
      apply alpha_eq_subst_utokens; eauto 3 with slow. }

    assert (!LIn a (get_utokens_lib lib w1)) as niaw1.
    { intro xx.
      apply (alphaeq_preserves_get_utokens_lib lib) in aeqws;
        rw aeqws in xx; apply r3 in xx.
      subst; apply get_fresh_atom_prop_and_lib in xx; tcsp. }

    rw in_app_iff in niaw1; apply not_over_or in niaw1; repnd.

    pose proof (simple_alphaeq_subst_utokens_subst w1 vr a niaw0) as aeq3.

    assert (alpha_eq z w1) as aeq4 by eauto 3 with slow.

    apply (approx_ext_trans _ _ (mk_fresh vr z));
      [|apply reduces_to_implies_approx_ext_eauto; auto;
        apply isprogram_fresh; complete auto].

    eapply approx_ext_alpha_rw_r_aux;
      [apply alpha_eq_sym; apply implies_alpha_eq_mk_fresh; exact aeq4|].

    assert (isvalue_like w1) as isvlw1.
    { repeat (rw @cl_subst_subst_aux in ap2; eauto 2 with slow).
      unfold subst_aux in ap2.
      inversion ap2 as [? ? ? e1 e2| ? ? e1 e2|].

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.

        + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
            try (complete (inversion gopu)).

        + repeat (rw @cl_subst_subst_aux in gopu; eauto 2 with slow); allunfold @subst_aux; allsimpl; boolvar; allsimpl;
            try (complete (inversion gopu)); ginv.
          destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
          inversion e2; subst; allsimpl; fold_terms; GC.
          allrw subset_cons_l; repnd; tcsp.
          allrw not_over_or; tcsp.

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
        destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.

      - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
        destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
    }

    pose proof (compute_step_fresh_if_isvalue_like lib vr w1 isvlw1) as comp.
    apply reduces_to_implies_approx_ext_eauto;
      [apply isprogram_fresh; complete auto|].
    apply reduces_to_if_step; auto.
  }


Qed.
