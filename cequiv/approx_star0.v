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


Require Export approx_star_props2.
Require Export computation6.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(* begin hide *)

Lemma range_utok_ren_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> length sub1 = length sub2
    -> range_utok_ren (nrut_subs_to_utok_ren sub1 sub2)
       = get_utokens_sub sub2.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 len; simphyps; tcsp.
  destruct a as [v1 t1]; destruct p as [v2 t2].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx.
  allrw @get_utokens_sub_cons; allsimpl.
  erewrite IHsub1; eauto.
Qed.

Lemma dom_utok_ren_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> length sub1 = length sub2
    -> dom_utok_ren (nrut_subs_to_utok_ren sub1 sub2)
       = get_utokens_sub sub1.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 len; simphyps; tcsp.
  destruct a as [v1 t1]; destruct p as [v2 t2].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx.
  allrw @get_utokens_sub_cons; allsimpl.
  erewrite IHsub1; eauto.
Qed.

Lemma approx_star_change_nrut_sub {o} :
  forall lib (t1 t2 : @NTerm o) sub l sub' l',
    nrut_sub l sub
    -> nrut_sub l' sub'
    -> dom_sub sub = dom_sub sub'
    -> subset (get_utokens_library lib) l
    -> subset (get_utokens_library lib) l'
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> subset (get_utokens t1) l'
    -> subset (get_utokens t2) l'
    -> approx_star lib (lsubst t1 sub) (lsubst t2 sub)
    -> approx_star lib (lsubst t1 sub') (lsubst t2 sub').
Proof.
  introv nrut1 nrut2 eqdoms ssl1 ssl2 ss1 ss2 ss3 ss4 apr.

  pose proof (length_dom sub) as len.
  rw eqdoms in len; rw @length_dom in len.

  pose proof (change_nr_ut_sub_in_lsubst_aux_approx_star
                lib (lsubst t1 sub) (lsubst t2 sub)
                (nrut_subs_to_utok_ren sub sub')) as h.
  erewrite @range_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  erewrite @dom_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  repeat (autodimp h hyp); eauto 3 with slow.

  - unfold nrut_sub in nrut1; repnd.
    eapply subset_disjoint;[|eauto]; auto.

  - unfold nrut_sub in nrut2; repnd.
    eapply subset_disjoint;[|eauto]; auto.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lib_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss3 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

    + unfold nrut_sub in nrut2; repnd.
      apply ssl2 in j0.
      apply nrut2 in j0; tcsp.

    + apply in_get_utokens_sub in j0; exrepnd.
      apply in_sub_keep_first in j1; repnd.
      apply sub_find_some in j2.
      destruct j.
      apply in_sub_eta in j2; repnd.
      unfold get_utokens_sub; rw lin_flat_map.
      eexists; dands; eauto.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lib_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss4 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

    + unfold nrut_sub in nrut1; repnd.
      apply ssl2 in j0.
      apply nrut2 in j0; tcsp.

    + apply in_get_utokens_sub in j0; exrepnd.
      apply in_sub_keep_first in j1; repnd.
      apply sub_find_some in j2.
      destruct j.
      apply in_sub_eta in j2; repnd.
      unfold get_utokens_sub; rw lin_flat_map.
      eexists; dands; eauto.

  - assert (disjoint (get_utokens_sub sub) (get_utokens t1)) as disj1.
    { introv i j.
      apply ss1 in j; unfold nrut_sub in nrut1; repnd.
      apply nrut1 in j; sp. }

    assert (disjoint (get_utokens_sub sub) (get_utokens t2)) as disj2.
    { introv i j.
      apply ss2 in j; unfold nrut_sub in nrut1; repnd.
      apply nrut1 in j; sp. }

    repeat (rw @lsubst_ren_utokens in h).
    repeat (rw @ren_utokens_trivial in h;[|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; eauto]).
    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in h; eauto.
Qed.

Lemma alpha_eq_bterm_preserves_osize2 {p} :
  forall bt1 bt2,
    @alpha_eq_bterm p bt1 bt2
    -> osize (get_nt bt1) = osize (get_nt bt2).
Proof.
  introv Hal.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  simpl; eapply alpha_eq_bterm_preserves_osize; eauto.
Qed.

Lemma lsubst_approx_star_congr_aux {p} :
  forall lib b b' lvi lnta lnta',
  approx_star lib b b'
  -> length lvi = length lnta
  -> length lvi = length lnta'
  -> disjoint (bound_vars b ++ bound_vars b') (flat_map (@free_vars p) (lnta ++ lnta'))
  -> bin_rel_nterm (approx_star lib) lnta lnta'
  -> approx_star lib (lsubst_aux b (combine lvi lnta)) (lsubst_aux b' (combine lvi lnta')).
Proof.
  nterm_ind1s b as [x|o lbt Hind] Case; introv Hap H1len H2len Hdis Hbin;
  rw flat_map_app in Hdis; duplicate Hbin as Hbb;
  apply @approx_rel_wf_sub with (lvi:=lvi) in Hbb; repnd.

  - Case "vterm".
    invertsn Hap. allsimpl.
    dsub_find xa;
      apply approx_open_lsubst_congr with (sub:= combine lvi lnta') in Hap;spcf;
      lsubst_lsubst_aux_eq_hyp X99 Hap; simpl; simpl_vlist; clear X99;
      lsubst_lsubst_aux_eq_hyp X99 Hap; simpl; simpl_vlist; clear X99;
      allsimpl; revert Hap.

    + dsub_find xa'; [|provefalse; eauto with slow].
      introv Hap. symmetry in Heqxa. symmetry in Heqxa'.
      eapply sub_find_some2_first
        in Heqxa; eauto. exrepnd. repnud Hbin. repnud Hbin.
      dimp (Hbin n);[spc;fail|].
      rewrite nth_indep with (d':= default_nterm) in Heqxa0; spc.
      rewrite nth_indep with (d':= default_nterm) in Heqxa4; spc.
      rw Heqxa0 in hyp.
      rw Heqxa4 in hyp.
      eapply approx_star_open_trans; eauto.

    + dsub_find xa'; [provefalse; eauto with slow | ].
      introv. apply approx_open_implies_approx_star.

  - Case "oterm".
    allsimpl.
    pose proof (approx_ot_change
                  lib
                  (flat_map free_vars lnta ++ flat_map free_vars lnta')
                  _ _ _ Hap) as Hao.
    exrepnd.
    rename lbtcv into lbt'. (* t' in paper *)
    apply approx_open_lsubst_congr with (sub:= combine lvi lnta') in Hao0;spcf.
    lsubst_lsubst_aux_eq_hyp X99 Hao0; simpl; simpl_vlist; clear X99;[].
    lsubst_lsubst_aux_eq_hyp X99 Hao0; simpl; simpl_vlist; clear X99;[].
    apply approx_star_open_trans with (b:=lsubst_aux (oterm o lbt') (combine lvi lnta'));spc;[].
    allsimpl.
    apply approx_open_relates_only_wf in Hao0. repnd.
    apply approx_star_congruence2;spc;[].
    clear Hao0 Hao4.
    unfold approx_starbts, lblift_sub; allunfold @blift_sub;repeat(simpl_list).
    dands; spcf.
    exrepnd. GC.
    introv Hlt. rw @selectbt_map;spc;[].  rw @selectbt_map;spc;[].
    duplicate Hlt as Hlt99. apply Hao2 in Hlt.

    destruct (dec_op_eq_fresh o) as [e|e].

    + pose proof (approx_star_btermd_fr
                    _ _ _ _
                    (flat_map free_vars lnta ++ flat_map free_vars lnta')
                    e
                    Hlt) as Hfb.

      exrepnd.
      exists lvn
             (lsubst_aux nt1' (sub_filter (combine lvi lnta) lvn))
             (lsubst_aux nt2' (sub_filter (combine lvi lnta') lvn)).
      dimp (selectbt_in n lbt');spcf.
      dimp (selectbt_in n lbt);spcf.
      applydup @alpha_eq_bterm_preserves_osize2 in Hfb4.
      (* needed to apply induction hyp later *)
      apply (lsubst_alphabt_congr _ _ (combine lvi lnta'))
        in Hfb5; [|allsimpl; spcls; disjoint_reasoningv;
                   apply disjoint_sym; eapply disjoint_flat_map_r in Hao1; eauto; fail].
      apply (lsubst_alphabt_congr _ _ (combine lvi lnta))
        in Hfb4; [|allsimpl; spcls; disjoint_reasoningv;
                   apply disjoint_sym in Hdis2;
                   eapply disjoint_flat_map_r in Hdis2; eauto with slow; fail].

      dands; auto;[].
      right.

      pose proof (exists_nrut_sub
                    lvn
                    (get_utokens_lib lib nt1'
                                 ++ get_utokens_lib lib nt2'
                                 ++ flat_map (get_utokens_lib lib) lnta
                                 ++ flat_map (get_utokens_lib lib) lnta'))
        as exnrut; exrepnd.

      pose proof (approx_star_change_nrut_sub
                    lib nt1' nt2' sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                    sub0
                    (get_utokens_lib lib nt1'
                                 ++ get_utokens_lib lib nt2'
                                 ++ flat_map (get_utokens_lib lib) lnta
                                 ++ flat_map (get_utokens_lib lib) lnta'))
           as ch.
      repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

      destruct (selectbt lbt n) as [l1 t1].
      destruct (selectbt lbt' n) as [l2 t2].
      allsimpl.

      pose proof (Hind t1 (lsubst nt1' sub0) l1) as h; repeat (autodimp h hh).
      { allrw; auto; rw @simple_osize_lsubst; eauto 3 with slow. }
      pose proof (h (lsubst nt2' sub0) lvi lnta lnta') as q; clear h.
      repeat (autodimp q hh).

      { repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow).
        repeat (erewrite bound_vars_lsubst_aux_nrut_sub; eauto).
        rw flat_map_app; allrw disjoint_app_l; sp. }

      repeat (rw @cl_lsubst_lsubst_aux in q; eauto 2 with slow).

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt1' sub0 (combine lvi lnta)) as e1.
      rw @sub_free_vars_combine in e1; auto.
      rw <- exnrut0 in e1.
      erewrite sub_bound_vars_nrut_sub in e1; eauto.
      erewrite sub_free_vars_nrut_sub in e1; eauto.
      allrw disjoint_app_r; allrw disjoint_app_l; repnd.
      repeat (autodimp e1 hh).

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt2' sub0 (combine lvi lnta')) as e2.
      rw @sub_free_vars_combine in e2; auto.
      rw <- exnrut0 in e2.
      erewrite sub_bound_vars_nrut_sub in e2; eauto.
      erewrite sub_free_vars_nrut_sub in e2; eauto.
      allrw disjoint_app_r; allrw disjoint_app_l; repnd.
      repeat (autodimp e2 hh).

      rw @cl_lsubst_aux_sub_trivial in e1; eauto 2 with slow.
      rw @cl_lsubst_aux_sub_trivial in e2; eauto 2 with slow.
      rw <- e1 in q; rw <- e2 in q.

      exists sub0; dands; auto.

      { repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow). }

      { eapply nrut_sub_subset;[|exact exnrut1].
        rw subset_app; dands; introv i; repeat (rw in_app_iff);
          apply get_utokens_lib_lsubst_aux in i; rw in_app_iff in i; repndors; tcsp;
            try (complete (apply in_app_iff in i; tcsp));
            apply in_get_utokens_sub in i; exrepnd; apply in_sub_keep_first in i0; repnd;
              apply sub_find_some in i2; apply in_sub_filter in i2; repnd; apply in_combine in i3; repnd.
        - right; right; left; rw lin_flat_map; eexists; dands; eauto 2 with slow.
        - right; right; right; rw lin_flat_map; eexists; dands; eauto 2 with slow.
      }

    + pose proof (approx_star_btermd
                    _ _ _ _
                    (flat_map free_vars lnta ++ flat_map free_vars lnta')
                    e
                    Hlt) as Hfb.
      exrepnd.
      exists lvn (lsubst_aux nt1' (sub_filter (combine lvi lnta) lvn))
             (lsubst_aux nt2' (sub_filter (combine lvi lnta') lvn)).
      dimp (selectbt_in n lbt');spcf.
      dimp (selectbt_in n lbt);spcf.
      applydup @alpha_eq_bterm_preserves_osize2 in Hfb2.
      (* needed to apply induction hyp later *)
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta'))
        in Hfb3; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym; eapply disjoint_flat_map_r in Hao1; eauto; fail].
      apply lsubst_alphabt_congr with (sub := (combine lvi lnta))
        in Hfb2; [|  allsimpl; spcls; disjoint_reasoningv;
                     apply disjoint_sym in Hdis2;
                     eapply disjoint_flat_map_r in Hdis2; eauto with slow; fail].

      dands; auto;[].
      left; dands; auto.
      dimp (sub_filter_pair_dom lvn (approx_star lib) lvi lnta lnta' ); spcf.
      exrepnd.
      rename lnta'0 into lntf.
      rename lntb' into lntf'.
      rename lvi' into lvif.
      rw hyp1.
      rw hyp3.
      destruct (selectbt lbt n) as [lv nt].
      simpl in Hfb5.
      eapply Hind with (nt:=nt); eauto; spc;[allrw; eauto 3 with slow|];[].
      rw flat_map_app. disjoint_reasoningv; disjoint_sub_filter.
Qed.

Lemma get_utokens_sub_combine {o} :
  forall vs (ts : list (@NTerm o)),
    length vs = length ts
    -> get_utokens_sub (combine vs ts) = flat_map get_utokens ts.
Proof.
  induction vs; destruct ts; introv len; allsimpl; tcsp; cpx.
  allrw @get_utokens_sub_cons.
  rw IHvs; auto.
Qed.

Lemma change_dom_nrut_sub {o} :
  forall (sub : @Sub o) l vs,
    nrut_sub l sub
    -> length vs = length sub
    -> {sub' : Sub
        & nrut_sub l sub'
        # range sub = range sub'
        # dom_sub sub' = vs }.
Proof.
  introv nrut len.
  exists (combine vs (range sub)).
  rw @range_combine; allrw @length_range; auto.
  rw @dom_sub_combine; allrw @length_range; auto.
  dands; auto.
  allunfold @nrut_sub; repnd.
  rw @get_utokens_sub_combine; allrw @length_range; auto.
  dands; auto.
  introv i.
  allapply in_combine; repnd.
  apply in_range in i; exrepnd.
  pose proof (nrut0 v0 t) as h; autodimp h hyp.
Qed.

Lemma cl_lsubst_approx_star_congr {o} :
  forall lib (a b : @NTerm o) sub,
    prog_sub sub
    -> approx_star lib a b
    -> approx_star lib (lsubst a sub) (lsubst_aux b sub).
Proof.
  introv pr apr.
  pose proof (lsubst_approx_star_congr_aux lib a b (dom_sub sub) (range sub) (range sub)) as h.
  allrw @length_dom; allrw @length_range.
  repeat (autodimp h hyp).
  - rw flat_map_app.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range.
    rw @sub_free_vars_if_cl_sub; simpl; eauto with slow.
  - unfold bin_rel_nterm, binrel_list; dands; auto.
    introv i.
    apply approx_star_refl.
    remember (nth n (range sub) default_nterm) as t.
    assert (LIn t (range sub)) as k.
    { subst; apply nth_in; auto. }
    apply in_range in k; exrepnd.
    pose proof (pr v t) as h; autodimp h hyp.
    destruct h as [c w]; auto.
  - allrw <- @sub_eta; auto.
    rw @cl_lsubst_lsubst_aux; eauto 2 with slow.
Qed.

(* we need it at least for subs with range as axiom for howe_lemma2 *)
Lemma approx_star_bterm_lsubst_congr {p} :
  forall lib (bt1 bt2 : BTerm) sub op,
    @prog_sub p sub
    -> approx_star_bterm lib op bt1 bt2
    -> approx_star_bterm
         lib op
         (lsubst_bterm_aux bt1 sub)
         (lsubst_bterm_aux bt2 sub).
Proof.
  introv Hpr Hs.

  destruct (dec_op_eq_fresh op) as [d|d].

  {
    pose proof (approx_star_btermd_fr
                  _ _ _ _
                  (flat_map free_vars (range sub)) d Hs) as Hfb.
    exrepnd.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range.

    unfold approx_star_bterm, blift_sub.
    exists lvn (lsubst nt1' (sub_filter sub lvn)) (lsubst nt2' (sub_filter sub lvn)).
    dands; auto;
    [|apply (lsubst_alphabt_congr _ _ sub) in Hfb4;
       allsimpl; auto;
       try (rw <- @cl_lsubst_lsubst_aux in Hfb4; eauto 3 with slow);
       allrw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_if_cl_sub; eauto with slow
     |apply (lsubst_alphabt_congr _ _ sub) in Hfb5;
       allsimpl; auto;
       try (rw <- @cl_lsubst_lsubst_aux in Hfb5; eauto 3 with slow);
       allrw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_if_cl_sub; eauto with slow].

    right.

    pose proof (exists_nrut_sub
                  lvn
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_sub sub))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub0 (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                  sub1
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_sub sub))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

    destruct bt1 as [l1 t1].
    destruct bt2 as [l2 t2].
    allsimpl.

    pose proof (cl_lsubst_approx_star_congr
                  lib (lsubst nt1' sub1) (lsubst nt2' sub1) sub) as q.
    repeat (autodimp q hyp).

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt1' sub1 sub) as e1.
    repeat (rw @sub_free_vars_if_cl_sub in e1; eauto with slow).
    repeat (autodimp e1 hh).

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj nt2' sub1 sub) as e2.
    repeat (rw @sub_free_vars_if_cl_sub in e2; eauto with slow).
    repeat (autodimp e2 hh).

    rw @cl_lsubst_aux_sub_trivial in e1; eauto 2 with slow.
    rw @cl_lsubst_aux_sub_trivial in e2; eauto 2 with slow.
    repeat (rw <- @cl_lsubst_lsubst_aux in e1; eauto with slow).
    repeat (rw <- @cl_lsubst_lsubst_aux in e2; eauto with slow).
    repeat (rw <- @cl_lsubst_lsubst_aux in q; eauto with slow).
    rw <- e1 in q; rw <- e2 in q; clear e1 e2.
    rw <- exnrut0 in q.

    exists sub1; dands; auto.

    { eapply nrut_sub_subset;[|exact exnrut1].
      rw subset_app; dands; introv i; repeat (rw in_app_iff);
        apply get_utokens_lib_lsubst in i; rw in_app_iff in i; repndors; tcsp;
          try (complete (apply in_app_iff in i; tcsp));
          apply in_get_utokens_sub in i; exrepnd; apply in_sub_keep_first in i0; repnd;
            apply sub_find_some in i2; apply in_sub_filter in i2; repnd;
              apply in_sub_eta in i3; repnd;
                right; right; rw lin_flat_map; eexists; dands; eauto.
    }
  }

  pose proof (approx_star_btermd
                _ _ _ _
                (flat_map free_vars (range sub)) d Hs) as Hfb.
  exrepnd.
  apply @lsubst_alphabt_congr with (sub := sub) in Hfb2;
    [| change_to_lsubst_aux4; eauto; fail].
  apply @lsubst_alphabt_congr with (sub := sub) in Hfb3;
    [| change_to_lsubst_aux4; eauto; fail].
  allsimpl.
  exists lvn (lsubst_aux nt1' (sub_filter sub lvn))
    (lsubst_aux nt2' (sub_filter sub lvn)).
  dands; sp;[].
  pose proof (sub_eta (sub_filter sub lvn)) as Xsfeta.
  pose proof (sub_eta_length (sub_filter sub lvn)) as X1len.
  remember (dom_sub (sub_filter sub lvn)) as lsvi.
  remember (range (sub_filter sub lvn)) as lsnt.
  rw Xsfeta.
  left; dands; auto.
  apply lsubst_approx_star_congr_aux;spc.
  - rw flat_map_app.
    (* the disjoint_sub_filter tactic needs the substitutions in eta form*)
    pose proof (sub_eta sub ) as Xseta.
    pose proof (sub_eta_length sub) as Xslen.
    remember (dom_sub sub) as lvi.
      remember (range sub) as lnt.
    rw Xseta in Xsfeta.
     disjoint_reasoningv; try disjoint_sub_filter.
  - unfold bin_rel_nterm, binrel_list; dands; [sp | introv Hlt].
    apply approx_star_refl. pose proof (nth_in _  _ _ default_nterm Hlt) as XX.
    rw Heqlsnt in XX.
    apply in_range in XX. exrepnd.
    apply in_sub_filter in XX0. exrepnd.
    apply Hpr in XX1.
    rw Heqlsnt. inverts XX1. sp.
Qed.

(* end hide *)

(** %\noindent \\*% The following is a generalization of Howe's lemma 1 %\cite{Howe:1989}%.
    He proved proved (needed) it for substitutions of length one.
    We need it atleast for substitutions of length upto two because
    the computation for [NSpread] performs a simultaneous subsitution
    for two variables. We prove a more general version instead. 
    Apart from some uninteresting details about substitution, our
    mechanized proof
    is essentially the same as Howe's.


*)
Lemma lsubst_approx_star_congr {p} :
  forall lib (t1 t2 : @NTerm p) (lvi : list NVar) (lnt1 lnt2 : list NTerm),
  bin_rel_nterm (approx_star lib) lnt1 lnt2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 (combine lvi lnt1)) (lsubst t2 (combine lvi lnt2)).
Proof.
  introv Hsr H1l H2l Has.
  pose proof (change_bvars_alpha_wspec 
    ((flat_map free_vars lnt1)++(flat_map free_vars lnt2)) t1) as H1f.
  exrepnd. rename ntcv into ct1.
  pose proof (change_bvars_alpha_wspec 
    ((flat_map free_vars lnt1)++(flat_map free_vars lnt2)) t2) as H2f.
  exrepnd. rename ntcv into ct2.
  assert (approx_star lib ct1 ct2) by eauto with slow. clear Has.
  apply lsubst_alpha_congr2 with (sub:=(combine lvi lnt1)) in H1f0.
  apply lsubst_alpha_congr2 with (sub:=(combine lvi lnt2)) in H2f0.
  assert (approx_star lib (lsubst ct1 (combine lvi lnt1)) (lsubst ct2 (combine lvi lnt2))) 
      ;[|eauto with slow; fail].
  clear dependent t1. clear dependent t2.
  change_to_lsubst_aux4; repeat(simpl_sub); disjoint_reasoningv.
  apply lsubst_approx_star_congr_aux; spc;[].
  spcls. rw flat_map_app. disjoint_reasoningv.
Qed.

(* begin hide *)

Lemma lsubst_approx_star_congr2 {p} : forall lib t1 t2 sub1 sub2,
  sub_range_rel (@approx_star p lib) sub1 sub2
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv Hsr Has.
  apply sub_range_rel_as_list in Hsr. exrepnd.
  subst sub1. subst sub2.
  apply lsubst_approx_star_congr; spc.
Qed.

(* weaker version than previous*)
Lemma lsubst_approx_star_congr3 {p} : forall lib t1 t2 sub,
  @wf_sub p sub
  -> approx_star lib t1 t2
  -> approx_star lib (lsubst t1 sub) (lsubst t2 sub).
Proof.
 introv Hw Has.
 apply lsubst_approx_star_congr2; sp;[].
 induction sub;allsimpl;spc.
 - repnud Hw. repnud Hw.  apply approx_star_refl. eapply Hw; left; eauto.
 - apply IHsub. introv Hin. repnud Hw. repnud Hw. eapply Hw; right; eauto.
Qed.

Lemma approx_starbt_change {p} :
  forall lib op bt1 bt2 (lvn : list NVar),
    op <> NCan NFresh
    -> approx_star_bterm lib op bt1 bt2
    -> no_repeats lvn
    -> length lvn = num_bvars bt1
    -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
    -> {nt1',nt2' : @NTerm p
        $ approx_star lib nt1' nt2'
        # alpha_eq_bterm bt1 (bterm lvn nt1')
        # alpha_eq_bterm bt2 (bterm lvn nt2')
       (* # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lvn *)
       }.
Proof.
  introv d Hab Hnr Hlen Hdis.
  invertsna Hab Hab.
  exrepnd; repndors; exrepnd; tcsp; GC.
  applydup @alphaeqbt_numbvars in Hab2.
  allunfold @num_bvars. allsimpl.

  dimp (alpha_bterm_pair_change3 _ _ _ _ _ lvn Hab2 Hab1); spcf;[].
  exrepnd.
  assert (approx_star lib nt1n nt2n) as XX by eauto with slow.
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  split; spc;[].
  apply approx_star_lsubst_vars;spc.
Qed.

Lemma lsubst_aux_nest_same_str2 {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst_aux (lsubst_aux t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst_aux t (filt_combine lvi lnt lf).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv Hl1 Hl2 Hnr Hdisb Hdisf; tcsp.

  { Case "vterm".

  simpl. destructr (sub_find (@filt_var_ren p lvi lvio lf) v) as [s1st|n1n].
  - apply symmetry in HeqHdeq. rename HeqHdeq into s1s.
    apply sub_find_sub_filter_some in s1s. repnd.
    apply sub_find_first in s1s0. exrepnd.
    unfold var_ren in s1s1.
    rewrite dom_sub_combine in s1s1;
     [| rewrite map_length; congruence] .
    unfold var_ren in s1s0.
    rewrite length_combine_eq
    in s1s0;[| rewrite map_length]; auto. 
    apply nth_var_ren_implies in s1s2;auto. exrepnd. rename vsr into vio.
    simpl. rewrite s1s2. simpl.
    destructr (sub_find (filt_combine lvio lnt lf) vio) as [s2st|n2n].

    + apply symmetry in HeqHdeq. rename HeqHdeq into s2s.
      apply sub_find_sub_filter_some in s2s. repnd.
      apply sub_find_first in s2s0. exrepnd.
      unfold var_ren in s2s0. rewrite length_combine_eq
      in s2s0;spc.
      rw combine_nth in s2s2;spc. inverts s2s2 as s2s3 s2s4.
      simpl. rewrite <- Hl1 in s1s0.
     (** clear s2s1. it cannot rule out case when n>n0*) 
      pose proof (no_repeats_index_unique2
               _ _ _ _ _ _ Hnr s1s0 s2s0 s1s4 s2s3) as X99.
      destruct X99. GC.  clear s1s2. clear s1st.
      destructr (sub_find (filt_combine lvi lnt lf) v) as [s3st|n3n].
      * apply symmetry in HeqHdeq. rename HeqHdeq into s3s.
        apply sub_find_sub_filter_some in s3s. repnd.
        apply sub_find_first in s3s0. exrepnd.
        unfold var_ren in s3s0. rewrite length_combine_eq
        in s3s0;spc.
        rw combine_nth in s3s2;spc. inverts s3s2 as s3s3 s3s4.
        simpl.  rewrite  Hl1 in s1s0.
        allfold (@dom_sub p). 
        allunfold (@var_ren p). spcls. 
        assert (n0<n \/ n0=n \/ n<n0) as Htri by omega.
        (dorn Htri);[|(dorn Htri)];
          try (apply s1s1 in Htri); cpx;
          try (apply s3s1 in Htri); cpx.
        destruct Htri. GC. apply nth_select3 in s3s4;[| congruence].
        apply nth_select3 in s2s4; congruence.
      * rename HeqHdeq into n3n. symmetry in n3n. 
        apply sub_find_sub_filter_none in n3n. dorn n3n; [ |sp(**see s1s*)].
        apply sub_find_none2 in n3n.        
        clear s1s1. apply nth_in2 in s1s3;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp.
    + rename HeqHdeq into n2n. symmetry in n2n.
      apply sub_find_sub_filter_none in n2n. dorn n2n.
      * apply sub_find_none2 in n2n. 
        apply nth_in2 in s1s4;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp. 
      * apply nth_in2 in s1s4;[| congruence].
        assert (disjoint lvio lf) as X99 by disjoint_reasoningv.
        apply X99 in s1s4; sp.
  - allsimpl.
    rw <- disjoint_remove_nvars_l in Hdisf.
    apply disjoint_singleton_r in Hdisf.
    allrw in_remove_nvars.
    rw (not_over_and (LIn v lvio) (!LIn v lvi) (in_deq _ deq_nvar v lvio)) in Hdisf.
    rw (not_over_not (LIn v lvi) (in_deq _ deq_nvar v lvi)) in Hdisf.
    allfold @dom_sub.
    assert ((dom_sub (combine lvi lnt)) = lvi) as Xrw  by (spcls;sp).
    rename HeqHdeq into n1n. symmetry in n1n.

    unfold filt_var_ren in n1n.
    unfold filt_combine.
    allrw @sub_find_sub_filter_eq; boolvar; tcsp.
    apply sub_find_none2 in n1n.
    rw @dom_sub_var_ren in n1n; auto.
    repndors; tcsp.
    rw @sub_find_none_if;[|rw @dom_sub_combine; auto].
    rw @sub_find_none_if;[|rw @dom_sub_combine; auto];tcsp.
  }

  { Case "oterm". (**this part is easier!!*)
    allsimpl. f_equal. rewrite map_map. eapply eq_maps; eauto.
    intros bt Hinb. destruct bt as [lv nt].
    unfold compose.
    allsimpl. apply disjoint_app_r in Hdisb. repnd.
    rename Hdisb into Hdisl.
    rename Hdisb0 into Hdisb.
    eapply disjoint_lbt_bt2 in Hdisb; eauto. repnd.
    apply disjoint_app_l in Hdisb0. repnd.
    simpl. f_equal.
    unfold filt_var_ren. unfold filt_combine.
    repeat(rewrite <- sub_filter_app_r).
    eapply Hind; eauto 3 with slow;[disjoint_reasoningv|].
    allrw <- disjoint_remove_nvars_l.
    rw disjoint_flat_map_r in Hdisf. apply Hdisf in Hinb.
    simpl in Hinb. rw <- disjoint_remove_nvars_l in Hinb.
    apply remove_nvars_unchanged in Hdisb1.
    rw remove_nvars_comm in Hinb.
    rewrite Hdisb1 in Hinb. trivial.
  }
Qed.

Lemma lsubst_nest_same_str2 {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst (lsubst t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst t (filt_combine lvi lnt lf).
Proof.
  intros.
  change_to_lsubst_aux4;
    try(apply lsubst_aux_nest_same_str2;try(sp;fail));
    apply disjoint_sym;
    rw <- @disjoint_sub_as_flat_map;
  try(apply sub_filter_sat).
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw <- @lsubst_lsubst_aux; disjoint_reasoningv.
    rw @boundvars_lsubst_vars2; spcls; disjoint_reasoningv.
    + rw @disjoint_sub_as_flat_map. spcls. sp.
    + apply allvars_sub_filter.
    + apply sub_filter_sat. rw @disjoint_sub_as_flat_map.
      spcls. disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
Qed.

Lemma lsubst_nest_same2 {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t)
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> lsubst (lsubst t (var_ren lvi lvio)) (combine lvio lnt)
     = lsubst t (combine lvi lnt).
Proof.
  intros.
  pose proof (sub_filter_nil_r (@var_ren p lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply lsubst_nest_same_str2; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma lsubst_nest_same_alpha2 {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint lvio (remove_nvars lvi (free_vars t))
  -> alpha_eq (lsubst (lsubst t (@var_ren p lvi lvio)) (combine lvio lnt))
      (lsubst t (combine lvi lnt)).
Proof.
  intros.
  pose proof (change_bvars_alpha_wspec (lvio++(flat_map free_vars lnt)) t) as Hf.
  exrepnd.
  alpharws Hf0.
  rw @lsubst_nest_same2;spc.
  alpharws (alpha_eq_sym _ _ Hf0). sp.
Qed.

Lemma approx_starbt_change_fr {p} :
  forall lib op bt1 bt2 (lvn : list NVar),
    op = NCan NFresh
    -> approx_star_bterm lib op bt1 bt2
    -> no_repeats lvn
    -> length lvn = num_bvars bt1
    -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
    -> {sub : Sub
        $ {nt1',nt2' : @NTerm p
        $ approx_star lib (lsubst nt1' sub) (lsubst nt2' sub)
        # nrut_sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2') sub
        # lvn = dom_sub sub
        # alpha_eq_bterm bt1 (bterm lvn nt1')
        # alpha_eq_bterm bt2 (bterm lvn nt2')
       (* # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lvn *)
       }}.
Proof.
  introv d Hab Hnr Hlen Hdis.
  invertsna Hab Hab.
  exrepnd; repndors; exrepnd; tcsp; GC.
  applydup @alphaeqbt_numbvars in Hab2.
  allunfold @num_bvars; allsimpl.

  assert (length x = length sub) as len.
  { subst; allrw @length_dom; auto. }

  dimp (alpha_bterm_pair_change3 _ _ _ _ _ lvn Hab2 Hab1); spcf;[].
  exrepnd.
  assert (approx_star lib (lsubst nt1n sub) (lsubst nt2n sub)) as XX by eauto with slow.
  exists (combine lvn (range sub)).
  exists (lsubst nt1n (var_ren x lvn)).
  exists (lsubst nt2n (var_ren x lvn)).
  rw @dom_sub_combine; allrw @length_range; auto; try omega.
  subst; dands; tcsp.

  - pose proof (lsubst_nest_same_alpha2 nt1n (dom_sub sub) lvn (range sub)) as nest1.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest1 hyp); try omega.
    { apply alpha_eq_bterm_preserves_free_vars in Hab2; allsimpl.
      rw disjoint_app_r in Hdis; repnd.
      rw Hab2 in Hdis0.
      apply alphaeq_preserves_free_vars in hyp0; rw <- hyp0; auto. }
    rw <- @sub_eta in nest1.

    pose proof (lsubst_nest_same_alpha2 nt2n (dom_sub sub) lvn (range sub)) as nest2.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest2 hyp); try omega.
    { apply alpha_eq_bterm_preserves_free_vars in Hab1; allsimpl.
      rw disjoint_app_r in Hdis; repnd.
      rw Hab1 in Hdis.
      apply alphaeq_preserves_free_vars in hyp2; rw <- hyp2; auto. }
    rw <- @sub_eta in nest2.

    pose proof (lsubst_alpha_congr2 nt1 nt1n sub hyp0) as as1.
    pose proof (lsubst_alpha_congr2 nt2 nt2n sub hyp2) as as2.

    eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact nest1].
    eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact nest2].
    eauto 3 with slow.

  - apply (alphaeq_preserves_get_utokens_lib lib) in hyp0.
    apply (alphaeq_preserves_get_utokens_lib lib) in hyp2.
    repeat (rw @get_utokens_lib_lsubst_allvars; eauto with slow).
    rw <- hyp0; rw <- hyp2.
    eapply nrut_sub_change_sub_same_range;[|exact Hab5].
    rw @range_combine; auto; allrw @length_range; allrw @length_dom; auto; try omega.
Qed.

Lemma approx_star_open_bt_trans {pp} :
  forall lib op (a b c : @BTerm pp),
  approx_star_bterm lib op a b
  -> approx_open_bterm lib b c
  -> approx_star_bterm lib op a c.
Proof.
  introv Has Hao.
  applydup @blift_sub_numbvars in Has.
  pose proof (fresh_vars
                (num_bvars a)
                (free_vars_bterm a ++ free_vars_bterm b ++ free_vars_bterm c))
    as Hfr.
  exrepnd.
  destruct (dec_op_eq_fresh op) as [d|d].

  - apply @approx_starbt_change_fr with (lvn:=lvn) in Has;exrepnd; spc;[| disjoint_reasoningv].
    apply @approxbtd_change with (lvn:=lvn) in Hao;spc;[| disjoint_reasoningv].
    assert (alpha_eq_bterm (bterm lvn nt1'0) (bterm lvn nt2')) as XX by eauto with slow.
    apply alpha_eq_bterm_triv in XX.
    unfold approx_open in p0.
    rwhg XX p0.
    fold (approx_open lib nt2' nt2'0) in p0.
    dup p0 as ao.

    pose proof (exists_nrut_sub
                  lvn
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_lib lib nt1'0
                               ++ get_utokens_lib lib nt2'0))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub (get_utokens_lib lib nt1' ++ get_utokens_lib lib nt2')
                  sub0
                  (get_utokens_lib lib nt1'
                               ++ get_utokens_lib lib nt2'
                               ++ get_utokens_lib lib nt1'0
                               ++ get_utokens_lib lib nt2'0))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 5 with slow;[].

    apply (approx_open_lsubst_congr _ _ _ sub0) in p0; eauto 2 with slow.
    eapply approx_star_open_trans in ch; eauto.
    exists lvn nt1' nt2'0.
    dands; tcsp.
    right.

    exists sub0; dands; tcsp.
    eapply nrut_sub_subset;[|exact exnrut1]; eauto with slow.

  - apply @approx_starbt_change with (lvn:=lvn) in Has;exrepnd; spc;[| disjoint_reasoningv].
    apply @approxbtd_change with (lvn:=lvn) in Hao;spc;[| disjoint_reasoningv].
    assert (alpha_eq_bterm (bterm lvn nt1'0) (bterm lvn nt2')) as XX by eauto with slow.
    apply alpha_eq_bterm_triv in XX.
    unfold approx_open in p0.
    rwhg XX p0.
    eapply approx_star_open_trans in Has1; eauto.
    exists lvn nt1' nt2'0.
    dands; tcsp.
Qed.

(* unlike lforall, this unfolds immediately to conjunctions
    if the list is concrete. But, it might confuse tactics like eauto *)
Fixpoint lforall2 {T} (P : T -> [univ]) (l: list T) : [univ] :=
  match l with
  [] => True
  | h::t => ((P h) # (lforall2 P t))
  end.

Notation programs :=  (lforall2 isprogram).

(* end hide *)

(** %\noindent \\*% Howe implicitly uses the following lemma at least twice
    in his proofs. It is essentially a more useful way
    to eliminate (use/destruct) a hypothesis of the form
    [approx_star (oterm o lbt) b].
    The advantage here is that we additionally obtain the hypothesis
    [isprogram (oterm o lbt')]. The [lbt'] that we obtain
    by naive inductive destruction of [approx_star (oterm o lbt) b]
    need not satisify this property. This additional property
    simplifies many proofs. For example, in his proof of
    Lemma 2 (shown below), when Howe says "by Lemma 1
    and the definition of $\le$ on open terms, we may assume that
    $\theta(\overline{t''})$ is closed", he is essentially using this lemma.

    The proof of this lemma involves reasoning like that
    used in the the proof
    of [approx_open_trans].
    Essentially, we substitute arbitrary closed terms for
    free variables in [lbt'] obtained
    by the inductive destruction so that it becomes closed and show that
    this substitution has no effect when it gets applied to other terms
    in the proof. %\\*%

 *)
Lemma approx_star_otd {p} : forall lib o lbt b, 
  approx_star lib (oterm o lbt) b
  -> isprogram b
  -> isprogram (oterm o lbt) (* required near the end *)
  -> {lbt' : (list (@BTerm p))  $  isprogram (oterm o lbt') 
        # approx_open lib (oterm o lbt') b
        # length lbt = length lbt'
        # approx_starbts lib o lbt lbt'}.
Proof.
  introv Has Hisp Hispo.
  invertsna Has Hapb.
  rename lbt1' into lbt''. (* t'' in paper *)  
  unfold approx_open in Hapb1.
  repnud Hapb1.
  remember (oterm o lbt'') as tb.
  pose proof (close_with_axiom tb Hapb2) as Hpr.
  allsimpl. exrepnd.
  dimp (Hapb1 (subst_axiom (free_vars tb))); spc;
      eauto 2 with slow;[ |rw @lsubst_trivial2; auto].
  remember (subst_axiom (free_vars tb)) as subc.
  remember (lsubst tb subc) as tbc.
  rw @lsubst_trivial2 in hyp; sp.
  remember((fun t : BTerm =>
                lsubst_bterm_aux t subc)) as fc.
  exists (map fc lbt'').
  lsubst_lsubst_aux_eq_hyp Heq Heqtbc.
  rw Heqtbc in Hpr. subst tb.
  simpl in Hpr.
  rw <- Heqfc in Hpr.
  dands; try( simpl_list); spc.
  - apply approx_implies_approx_open. subst; spc.
  - unfold approx_starbts; allunfold @lblift_sub; simpl_list; exrepnd.
    dands; spcf. introv Hlt.
    applydup Hapb0 in Hlt.
    rw @selectbt_map; [| omega].
    subst fc.
    apply approx_star_bterm_lsubst_congr with (sub:=subc) in Hlt0; auto;[].
    apply isprogram_ot_iff in Hispo. repnd.
    apply selectbt_in in Hlt.
    rw @lsubst_bterm_trivial in Hlt0; eauto with slow.
Qed.

Ltac prove_isprogram :=
  match goal with
    | [ |- isprogram _ ] =>
      complete (repeat decomp_progh; show_hyps; eauto with extens;
                repeat decomp_progc; eauto with extens)
    | _ => idtac
  end.

Lemma reduces_to_implies_approx_eauto {p} :
  forall lib (t x : @NTerm p),
    isprogram t -> reduces_to lib t x -> approx lib x t.
Proof.
 introv Hp Hr.
  apply reduces_to_implies_approx in Hr; sp.
Qed.

(** %\noindent \\* % We now prove Howe's lemma 2 %\cite{Howe:1989}%. Using the lemma
    [approx_star_otd] above, this proof goes
    pretty much exactly like Howe describes.

*)

Lemma howe_lemma2 {p} :
  forall lib (c : CanonicalOp) (lbt : list BTerm) (b : @NTerm p),
    let t:= oterm (Can c) lbt in
    isprogram t
    -> isprogram b
    -> approx_star lib t b
    -> {lbt' : (list BTerm)
        & approx_starbts lib (Can c) lbt lbt'
        # computes_to_value lib b (oterm (Can c) lbt')}.
Proof.
  introv Hprt Hprb Hap.
  apply approx_star_otd in Hap;spcf;[]. exrepnd.
  rename lbt' into lbt''. (* t'' in paper *)

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose. repnud Hclose.
  dimp (Hclose2 c lbt'');
    eauto;[apply computes_to_value_isvalue_refl; constructor; eauto; fail|].
  exrepnd.
  apply clearbot_relbt in hyp0.

  rename tr_subterms into lbt'. (*( t' in the paper proof *)
  exists lbt'.
  GC. (*clear Hclose*)
  split; auto;[].
  allunfold @lblift.

  repeat (simpl_list). repnd. split; spcf;[].
  introv Hlt.
  applydup_clear Hap0 in Hlt.
  dimp (hyp0 n); try omega;[].
  clear hyp0.
  eapply approx_star_open_bt_trans; eauto.
Qed.

Lemma howe_lemma2_implies_iscan {p} :
  forall lib (t b : @NTerm p),
    isprogram t
    -> iscan t
    -> isprogram b
    -> approx_star lib t b
    -> {v : NTerm & iscan v # (b =v>(lib) v) # approx_star lib t v}.
Proof.
  introv ispt isct ispb apr.
  apply iscan_implies in isct; repndors; exrepnd; subst.
  - apply howe_lemma2 in apr; auto.
    exrepnd.
    eexists; dands; eauto.
    allunfold @approx_starbts.
    apply (apso _ _ _ _ lbt'); auto.
    { allunfold @lblift_sub; repnd; auto. }
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram; eauto 3 with slow.
Qed.

Lemma howe_lemma2_exc {p} :
  forall lib a (e b : @NTerm p),
    isprogram (mk_exception a e)
    -> isprogram b
    -> approx_star lib (mk_exception a e) b
    -> { a' , e' : NTerm
        $ approx_star lib a a'
        # approx_star lib e e'
        # computes_to_exception lib a' b e'}.
Proof.
  introv Hprt Hprb Hap.
  apply approx_star_otd in Hap;spcf;[]. exrepnd.
  rename lbt' into lbt''. (* t'' in paper *)

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose. repnud Hclose.
  allsimpl; cpx.
  applydup @isprogram_exception_implies in Hap1; exrepnd; cpx.
  dimp (Hclose3 a0 t); try (complete (apply computes_to_exception_refl; sp)); exrepnd.
  apply remove_bot_approx in hyp2.
  apply remove_bot_approx in hyp1.

  exists a' e'; sp.

  - inversion Hap0 as [? f]; allsimpl; GC.
    generalize (f 0); clear f; intro k; autodimp k hyp.
    unfold selectbt in k; simpl in k.
    destruct k as [vs k]; exrepnd; repndors; exrepnd; ginv.
    inversion k1; subst; allsimpl; cpx.
    inversion k2; subst; allsimpl; cpx.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil; GC.

    apply @approx_star_alpha_fun_l with (nt1 := nt1); auto;
    try (complete (apply alpha_eq_sym; auto)).
    apply @approx_star_open_trans with (b := nt2); auto.
    eapply approx_open_alpha_rw_l_aux; eauto.
    apply approx_implies_approx_open; auto.

  - inversion Hap0 as [? f]; allsimpl; GC.
    generalize (f 1); clear f; intro k; autodimp k hyp.
    unfold selectbt in k; simpl in k.
    destruct k as [vs k]; exrepnd; repndors; exrepnd; ginv.
    inversion k1; subst; allsimpl; cpx.
    inversion k2; subst; allsimpl; cpx.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil; GC.

    apply @approx_star_alpha_fun_l with (nt1 := nt1); auto;
    try (complete (apply alpha_eq_sym; auto)).
    apply @approx_star_open_trans with (b := nt2); auto.
    eapply approx_open_alpha_rw_l_aux; eauto.
    apply approx_implies_approx_open; auto.
Qed.

(*
Lemma howe_lemma2_mrk {p} :
  forall lib m (b : @NTerm p),
    isprogram b
    -> approx_star lib (mk_marker m) b
    -> computes_to_marker lib b m.
Proof.
  introv Hprb Hap.
  apply approx_star_otd in Hap;spcf;[|repeat constructor; simpl; complete sp]; exrepnd.
  allsimpl; cpx; fold_terms.

  apply approx_open_approx in Hap2; spc.
  invertsna Hap2 Hclose.
  repnud Hclose.
  dimp (Hclose m).
  apply compute_to_marker_mrk.
Qed.
*)

(** Informally, [howe_lemma2] looks a lot like the definition of [close_comput].
    The only difference is that [close_comput] was
    preserved when computation happens on the LHS argument.

    Recall the [approx] can be considered as a greatest fixed point
    of [close_comput]. If we could prove that [approx_star] is preserved
    when computation happens on the LHS argument, a simple coinductive
    argument will prove that [approx_star] implies
    [approx] on closed terms.
    Formally, we only need to prove the following lemma
    %\footnote{Howe did not explicitly call it Lemma 3. But he proves it
        while proving his theorem 1}% :
[[
Lemma howe_lemma3 : forall (a a' b : NTerm),
  isprogram a
  -> isprogram a'
  -> isprogram b
  -> computes_to_value a a'
  -> approx_star a b
  -> approx_star a' b.
]]

  This proof will proceed by the induction on the number of steps that
  [a] took to compute to the value [a']. Since variables don't compute to
  anything, [a] must be of the form [oterm o lbt]. The proof then proceeds
  by case analysis on [o]. Unlike the previous proofs about [approx],
  which were uniform w.r.t the [Opid]s in the language and
  only assumed that the computation system was lazy, this proof
  requires reasoning about each [Opid] in the language.

  Howe abstracts the remainder of the proof of this lemma into the
  following condition (called extensionality) that has to be proved
  for each [Opid] in the language. The last hypothesis ([Hind], the big one)
  in this definition  is essentially the induction hypothesis
  in the proof of [howe_lemma3].
*)

Definition extensional_op_ind {p} lib k :=
  forall (u u' v : @NTerm p),
    isprogram u
    -> isprogram u'
    -> isprogram v
    -> computes_to_val_like_in_max_k_steps lib u u' k
    -> approx_star lib u v
    -> approx_star lib u' v.

Definition extensional_op {p} (o : @Opid p) :=
  forall
    (lib : library)
    (lbt lbt' : list BTerm)
    (a : NTerm)
    (k : nat)
    (Hpa : isprogram a)
    (Hpt : isprogram (oterm o lbt))
    (Hpt' : isprogram (oterm o lbt'))
    (Hcv : computes_to_val_like_in_max_k_steps lib (oterm o lbt) a (S k))
    (Has : lblift_sub lib o (approx_star lib) lbt lbt')
    (Hind : @extensional_op_ind p lib k),
    approx_star lib a (oterm o lbt').

(** %\noindent \\*% It is immediately clear that all the canonical [Opid]s of
    a lazy computation
    system are extensional.  In this case, we have [(oterm o lbt)= a] and
    the conclusion is an immediate consequence of congruence of [approx_star].


 *)
Lemma nuprl_extensional_can {p} :
  forall cop, extensional_op (@Can p cop).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  apply computes_to_val_like_in_max_k_steps_can in Hcv; subst.
  apply approx_star_congruence2;sp; eauto with slow.
Qed.

Lemma nuprl_extensional_exc {p} :
  extensional_op (@Exc p).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  apply computes_to_val_like_in_max_k_steps_exc in Hcv; subst.
  apply approx_star_congruence2;sp; eauto with slow.
Qed.

(** %\noindent% The next definition
  is just compact and equivalent
  restatement of [extensional_op_val] for
  the paper.
  Please ignore if you are reading
  the technical report. Sorry! *)

Definition extensional_opc {p} (o : @Opid p) :=
  forall lib
         (lbt lbt' : list BTerm)
         (a : NTerm)
         (k:nat),
    programs [a,(oterm o lbt),(oterm o lbt')]
    -> computes_to_value_in_max_k_steps lib (S k) (oterm o lbt) a
    -> lblift_sub lib o (approx_star lib) lbt lbt'
    -> (forall (u u' v : @NTerm p),
          programs [u,u',v]
          -> computes_to_value_in_max_k_steps lib k u u'
          -> approx_star lib u v
          -> approx_star lib u' v)
    -> approx_star lib a (oterm o lbt').

(* begin hide *)

Lemma approx_star_bterm_nobnd2 {p} :
  forall lib op a b,
    approx_star_bterm lib op (bterm [] a) (@bterm p [] b)
    -> approx_star lib a b.
Proof.
  introv Has.
  apply approx_star_bterm_nobnd in Has; exrepnd; subst; cpx.
  inversion Has1; subst; sp.
Qed.

Lemma notTrue_btchange {p} : (forall lv nt lvn,
  length lv = length lvn ->
  alpha_eq_bterm (bterm lv nt) (bterm lvn (lsubst nt (@var_ren p lv lvn))))
  -> False.
Proof.
  introv Hc.
  pose proof (Hc [nvarx,nvary] (oterm (NCan (NArithOp ArithOpAdd)) [(bterm [] (vterm nvarx)),(bterm [] (vterm nvary))])
               [nvarz,nvarz] eq_refl) as XX.
  clear Hc.
  unfold mk_apply,lsubst, nobnd in XX.
  simpl in XX.
Abort. (* apply both sides to [1,2] and compute 1 step to get sth which is not alpha equal*)
(* see btchange_alpha for the correct version*)

(*
Lemma approx_star_btermd_samevar {p} :
  forall lib op a lv bt,
    approx_star_bterm lib op (bterm lv a) bt
    -> {b : @NTerm p
        $ alpha_eq_bterm bt (bterm lv b)
        # approx_star lib a b }.
Proof.
  introv Has.
  destruct bt as [lvb b']; allsimpl.
  apply (approx_star_btermd _ _ _ (lv++lvb)) in Has.
  exrepnd.
  pose proof (change_bvars_alpha_wspec (lv++lvb) a) as Hfa.
  exrepnd. rename ntcv into a'. duplicate Hfa0. 
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfa0.
  assert (alpha_eq_bterm (bterm lv a') (bterm lvn nt1')) 
      as Xa by eauto with slow.

  pose proof (change_bvars_alpha_wspec (lvb++lv) b') as Hfb.
  exrepnd. rename ntcv into b.
  apply @alpha_eq_bterm_congr with (lv:=lvb) in Hfb0.
  assert (alpha_eq_bterm (bterm lvb b) (bterm lvn nt2')) 
      as Xb by eauto with slow.
  invertsna Xa Hb.
  invertsna Xb Ha.
  apply lsubst_alpha_congr2 with (sub:=var_ren lv3 lv) in Ha3.
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  apply lsubst_alpha_congr2 with (sub:=var_ren lv0 lv) in Hb3.
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  assert (alpha_eq a' (lsubst nt1' (var_ren lvn lv))) as Xa by eauto with slow.
  clear Hb3.
  apply approx_star_lsubst_vars with (lvi:=lvn) (lvo:=lv) in Has1;spc;[].
  exists (lsubst nt2' (var_ren lvn lv)).
  dands.
  Focus 2. eauto with slow; fail.
Abort. (* probably not true ... see above*)
*)

Lemma approx_star_btermd_1var {p} :
  forall lib op v a bt,
    approx_star_bterm lib op (bterm [v] a) bt
    -> {vr : NVar
        $ {b : @NTerm p
        $ bt = bterm [vr] b
        # approx_star_bterm lib op (bterm [v] a) (bterm [vr] b) }}.
Proof.
  introv Hab.
  destruct bt as [lvb b].
  applydup @blift_sub_numbvars in Hab.
  allunfold @num_bvars; allsimpl.
  alphahypsd.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.

Lemma approx_star_btermd_2var {p} :
  forall lib op v1 v2 a bt,
    approx_star_bterm lib op (bterm [v1, v2] a) bt
    -> {v1r,v2r : NVar
        $ {b : @NTerm p $ bt=(bterm [v1r,v2r] b)
        # approx_star_bterm lib op (bterm [v1,v2] a) (bterm [v1r,v2r] b)}}.
Proof.
  introv Hab.
  destruct bt as [lvb b].
  applydup @blift_sub_numbvars in Hab.
  allunfold @num_bvars.
  allsimpl.
  alphahypsd.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.

(*

Lemma compute_apply_decompose : forall k lbt a,
  computes_to_value_in_max_k_steps (S k) (oterm (NCan NApply) lbt) a
  -> {v : NVar $ {la b arg : NTerm $ lbt = [(bterm [] la), (bterm [] arg)
        # computes_to_value_in_max_k_steps  k la (mk_lambda v b)
        # computes_to_value_in_max_k_steps  k la (mk_lambda v b)

      ] }} *)

Hint Resolve computek_preserves_program : slow.
Ltac lsubst_nest_tac :=
  let X99 := fresh "X438590348" in
  repeat match goal with
           | [ H : (approx_star ?lib (lsubst (lsubst ?t1 (var_ren ?lv1 ?lvn)) (combine ?lvn ?lnt1)) ?rhs) |- _ ]
             => dimp (lsubst_nest_same_alpha t1 lv1 lvn lnt1);
               spc;
               disjoint_reasoningv;
               rename H into X99;
               assert (approx_star lib (lsubst t1 (combine lv1 lnt1)) rhs)
                 as H by eauto with slow; clear X99
           | [ H : (approx_star ?lib ?lhs (lsubst (lsubst ?t1 (var_ren ?lv1 ?lvn)) (combine ?lvn ?lnt1))) |- _ ]
             => dimp (lsubst_nest_same_alpha t1 lv1 lvn lnt1);
               spc;
               disjoint_reasoningv;
               rename H into X99;
               assert (approx_star lib lhs (lsubst t1 (combine lv1 lnt1)))
                 as H by eauto with slow; clear X99
         end.


(* end hide *)

(** We now begin to prove that the non-canonical [Opid]s of Nuprl are extensional.
    The following corollary of Howe's lemma 1 ([lsubst_approx_star_congr]) will
    be very useful in  of the proofs for the
   [Opid]s [NApply, NCbv, NDecide, NSpread].

 *)

Lemma apply_bterm_approx_star_congr {p} :
  forall lib op bt1 bt2 lnt1 lnt2,
    op <> NCan NFresh
    -> approx_star_bterm lib op bt1 bt2
    -> bin_rel_nterm (@approx_star p lib) lnt1 lnt2 (*enforces that the lengths are equal*)
    -> length lnt1 = num_bvars bt1 (*only required for simplicity*)
    -> length lnt1 = length lnt2 (*only required for simplicity*)
    -> approx_star lib (apply_bterm bt1 lnt1) (apply_bterm bt2 lnt2).
Proof.
  introv d Ha0 Hbr H1len H2len.
  applydup @blift_sub_numbvars in Ha0. allunfold @num_bvars.

  apply (approx_star_btermd _ _ _ _ ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2))) in Ha0; auto.
  allunfold @apply_bterm. allsimpl. exrepnd.
  destruct bt1 as [lv1 t1].
  destruct bt2 as [lv2 t2]. rename nt1' into nt1. rename nt2' into nt2.
  rename lvn into lv.
  pose proof (fresh_vars (length lv1) (all_vars nt1 ++ all_vars nt2
               ++ all_vars t1 ++ all_vars t2)).
  exrepnd. simpl in Ha1.
  apply @alphabt_change_var with (lv:=lvn) in Ha4; spc; [| disjoint_reasoningv; fail].
  apply @alphabt_change_var with (lv:=lvn) in Ha3; spc;[| disjoint_reasoningv];[].
  apply approx_star_lsubst_vars with (lvi:=lv) (lvo:=lvn) in Ha0;spc;[].
  apply alpha_eq_sym in Ha6.
  apply alpha_eq_sym in Ha7.
  assert (approx_star lib
    (lsubst t1 (var_ren lv1 lvn)) (lsubst t2 (var_ren lv2 lvn)))
       as XX by eauto with slow. (* alpha replacement *)
  allsimpl. clear Ha0.
  apply @lsubst_approx_star_congr with
      (lvi:=lvn) (lnt1:=lnt1) (lnt2:=lnt2) in XX;spc;[].

   lsubst_nest_tac.
   sp.
Qed.

(* Howe proved the extensionality of the [NApply] [Opid].
    Crary%\cite{Crary98}% proved it for many others. Our [NDecide] and
    [NCbv] are exactly same as his case and let-binding constructs.
    Our proofs of extensionality of these [Opid]s are quite close to
    their descriptions. We will only describe the proofs for

    We will now describe the proof for [NSpread]
    %\footnote{Crary's language has $\pi _1$ and $\pi _2$ constructs}%.
*)


(* begin hide *)



Lemma blift_nobnd_congr {p} : forall R t1 t2,
  R t1 t2
  -> @blift p R (bterm [] t1) (bterm [] t2).
Proof.
  introv Ht.
  exists (@nil NVar) t1 t2.
  dands; eauto with slow.
Qed.

Lemma blift_sub_nobnd_congr {o} :
  forall lib R op (t1 t2 : @NTerm o),
  R t1 t2
  -> blift_sub lib op R (bterm [] t1) (bterm [] t2).
Proof.
  introv Ht.
  exists (@nil NVar) t1 t2; dands; eauto with slow.
  destruct (dec_op_eq_fresh op) as [d|d]; tcsp.
  right; exists ([] : @Sub o); simpl; allrw @lsubst_nil; dands; eauto with slow.
Qed.

Hint Unfold lblift lblift_sub : slow.
Hint Resolve approx_star_congruence2 blift_nobnd_congr blift_sub_nobnd_congr : slow.

Theorem approx_star_congruence3 {p} : forall lib o lbt1 lbt2,
  approx_starbts lib o lbt1 lbt2
  -> @isprogram p (oterm o lbt2)
  -> approx_star lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps Hnt.
   apply approx_star_congruence2; sp.
   eauto with slow.
Qed.


Ltac prove_approx_star := unfold mk_apply;
match goal with
| [ |- approx_star _ ?t ?t] => apply approx_star_refl
| [  |- approx_star _ (oterm ?o _) (oterm ?o _)] =>
       apply approx_star_congruence3
| [ |- isprogram _] => repeat(decomp_progc); eauto with slow
| [  |- approx_starbts _ _ _ _ ] =>
  (unfold approx_starbts, lblift_sub; simpl; dands;[spc|];
   let Hlt := fresh "XXHlt" in
   let n := fresh "XXn" in
   intros n Hlt;
   ( let rnum := (get_lt_rhs  Hlt) in
     fail_if_not_number rnum; (*fail if not a normal form*)
     repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
  ))
| [  |- approx_star_bterm _ _ (bterm [] ?t1) (bterm [] ?t2)] =>
  apply blift_sub_nobnd_congr
| [  |- blift_sub _ _ (approx_star _) (bterm [] ?t1) (bterm [] ?t2)] =>
  apply blift_sub_nobnd_congr
end.


Ltac duplicateas H newname :=
  let name := fresh newname
  in remember H as name;
  clears_last.





Ltac approxrelbtd :=
  match goal with 
  | [H: 0 = length _ |- _ ] => symmetry in H; apply length0 in H; subst
  | [H: 1 = length _ |- _ ] => symmetry in H; apply length1 in H; exrepnd; subst
  | [H: 2 = length _ |- _ ] => symmetry in H; apply length2 in H; exrepnd; subst
  | [H: 3 = length _ |- _ ] => symmetry in H; apply length3 in H; exrepnd; subst
  | [H: 4 = length _ |- _ ] => symmetry in H; apply length4 in H; exrepnd; subst
  | [H: _ = S (length _) |- _ ] =>  inverts H as H
  | [H: (forall _:nat, (_< ?m) -> blift_sub _ _ _ _ _)  |- _ ] => 
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simpl in XXX); clear H
  | [H: approx_star_bterm _ _ (bterm [] _) (bterm [] _) |- _] => hide_hyp H
  | [H: blift_sub _ _ (approx_star _) (bterm [] _) (bterm [] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: blift_sub _ _ (approx_star _) (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: blift_sub _ _ (approx_star _) (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [] ?nt) _ |- _] =>
    apply approx_star_bterm_nobnd in H;
      let ntr := fresh nt "r" in
      (destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ _ (approx_star _) (bterm [] ?nt) _ |- _] =>
    apply approx_star_bterm_nobnd in H;
      let ntr := fresh nt "r" in
      (destruct H as [ntr H]);
        repnd; subst
  | [H: approx_star_bterm _ _ (bterm [?v] ?nt) _ |- _] =>
    apply approx_star_btermd_1var in H;
      let vr := fresh v "r" in
      let ntr := fresh nt "r" in
      (destruct H as [vr H]; destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ _ (approx_star _) (bterm [?v] ?nt) _ |- _] =>
    apply approx_star_btermd_1var in H;
      let vr := fresh v "r" in
      let ntr := fresh nt "r" in
      (destruct H as [vr H]; destruct H as [ntr H]);
        repnd; subst
  | [H: approx_star_bterm _ _ (bterm [?v1, ?v2] ?nt) _ |- _] =>
    apply approx_star_btermd_2var in H;
      let v1r := fresh v1 "r" in
      let v2r := fresh v2 "r" in
      let ntr := fresh nt "r" in
      (destruct H as [v1r H]; destruct H as [v2r H]; destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ _ (approx_star _) (bterm [?v1, ?v2] ?nt) _ |- _] =>
    apply approx_star_btermd_2var in H;
      let v1r := fresh v1 "r" in
      let v2r := fresh v2 "r" in
      let ntr := fresh nt "r" in
      (destruct H as [v1r H]; destruct H as [v2r H]; destruct H as [ntr H]);
        repnd; subst
  | [H : approx_star_bterm _ _ (bterm ?lv ?a) (bterm ?lv ?b) |- _ ] =>
    apply approx_star_samevar in H; subst
  | [H : blift (approx_star _) (bterm ?lv ?a) (bterm ?lv ?b) |- _ ] =>
    apply approx_star_samevar in H; subst
  | [H : blift _ _ _ |- _ ] => unfold blift in H; exrepnd
  end.



Hint Resolve compute_max_steps_eauto compute_max_steps_eauto2: extens.


Lemma reduces_to_implies_approx_open {p} :
  forall lib t x,
    @isprogram p t
    -> reduces_to lib t x
    -> approx_open lib x t # approx_open lib t x.
Proof.
  introv Hp Hr. apply reduces_to_implies_approx in Hr; auto. repnd.
  split; apply approx_implies_approx_open; auto.
Qed.

(*
    We begin by proving extensionality of the [NApply] [Opid].
    Our proof essentially follows Howe's proof. We will, however
    describe the proof to describe some details specific to our
    formalization, and also sketch the general recipe for such proofs.
%\footnote {In hind-sight, it seems possible to write an
    automated tactic that can finish these proofs}.%

    Also, the shape of [bargs] has to be
    the one that
    [(map (fun x => 0) pargs ++ map num_bvars npargs) = OpBindings (NCan op)].

      Morevover, the head [Opid] of this canonical form
      ([v]) should be compatiable with [op].
      For example, if [op = NApply],
      [c] must be [NLambda]. Similarly, if [op = NDecide], [c] must either
      be [NInl] or [NInr]. For [NCbv], [c] can be canonical [Opid].
      One can look at the definition of the [compute_step]
      function to find out such relations.
      Often, [op] is called the elim form of the intro form [c].
*)

Definition get_bterms {p} (nt:@NTerm p) : list BTerm :=
  match nt with
    | vterm v => []
    | oterm o lbt => lbt
  end.

(* use this to typecheck all the composite terms in the long comment below*)
(*
  Definition v := nvarx.
  Definition v1 := nvarx.
  Definition v2 := nvarx.
  Definition b := (vterm nvarx).
  Definition bl := (vterm nvarx).
  Definition br := (vterm nvarx).
  Definition pi1 := (vterm nvarx).
  Definition arg := (vterm nvarx).
  Definition pi2 := (vterm nvarx).
  Definition lbt := @nil BTerm.
  Definition lbtc := @nil BTerm.
  Definition lbt' := @nil BTerm.
  Definition bargs := @nil BTerm.
  Definition bargs' := @nil BTerm.
  Definition pnt := @nil NTerm.
  Definition pnt' := @nil NTerm.
  Definition pntc := @nil NTerm.
  Definition pntc' := @nil NTerm.
  Definition op := NFix.
  Definition cc := NLambda.
  Definition f := fun  l: list BTerm => (vterm nvarx).
*)

(* end hide *)

(** Howe and Crary prove extensionality of many non-canonical [Opid]s.
    Our computation system has some new ones and the operational
    semantics of some earlier ones like [NFix] is different.
    We have formally proved that all [Opid]s in our system are extensional.
    Instead of describing these proofs separately, we will describe the
    general recipe. A reader who
    wishes to delve into very concrete details can walk through
     the coq proof
    scripts for the extensionality lemmas.

    In general, whenever a computation in which an arbitrary non-cononical term
    [(oterm (NCan op) lbt)] computes to a value [a], [lbt] can be expressed as
    [(map (bterm []) pnt)++bargs], where [pnt] are the principal arguments of [op].
    The length of [pargs] depends on [op].
    For [NCompOp] and [NCanTest], it is 2 and it is 1 for the rest.
    The [S k] steps of computation from [(oterm (NCan op) (map (bterm []) pnt ++ bargs))]
    to the value [a] (see hypothesis [Hcv] in [extensional_op])
    can be split into the following three parts
    that happen one after the other.

    - Each element of [pnt] converges to some canonical [NTerm].
      At the end of this stage, the overall term is of the form
      [(oterm (NCan op) ((map (bterm []) pntc)++bargs))] such that
      elements of [pnt] converge respectively to canonical elements of [pntc].

    - One interesting step of computation happens by the interaction of
      the canonical [Opid]s in [pntc] and the corresponding non-canonical [Opid]
      [op]. Let the overall term after this step
      be [t]. Let [llbt] be [(bargs ++ (flat_map get_bterms pntc))].
      For the proof of [extensional_op (NCan op)], the key property
      here is that [t] can always be written as some [f llbt] such that
      [forall lbt1 lbt2, approx_starbts lbt1 lbt2 -> approx_star (f lbt1) (f lbt2)].
      The details of this depend on the specific [op].
      We consider all cases
      one by one. The reader might want to revisit the definition of [compute_step]
      to understand the claims below.  [op=]
      -- [NApply] : In this case, [pntc] is of the form
          [[oterm (Can NLambda) [(bterm [v] b)]]] and [bargs] is of the form
          [[bterm [] arg]] and  [t= apply_bterm (bterm [v] b) [arg]]. For this
          and the next 4 cases, the required property of [f] is a direct consequence
          of the lemma [apply_bterm_approx_star_congr] above.
      -- [NCbv] : [pntc] is of the form [[oterm (Can cc) lbtc]] and
          [bargs] is of the form [bterm [v] b].
          [t= apply_bterm (bterm [v] b) [(oterm (Can cc) lbtc)]].
      -- [NSpread] : [pntc] is of the form
          [[oterm (Can NPair) [bterm [] pi1,bterm [] pi2]]]
          and [bargs] is of the form [bterm [v1,v2] b].
          [t= apply_bterm (bterm [v1,v2] b) [pi1,pi2]]
      -- [NDecide] : [pntc] is of the form
          [[oterm (Can NInl) [bterm [] arg]]] or [[oterm (Can NInr) [bterm [] arg]]]
          and [bargs] is of the form [[bterm [v] bl,bterm [v] br]]
          and  [t= apply_bterm (bterm [v] bl) [arg]] or
          [t= apply_bterm (bterm [v] br) [arg]] depending on [pntc].
      -- [NArithOp] : [pntc] is of the form
          [[oterm (Can (Nint n1)) [], oterm (Can (Nint n2)) []]]
          and [bargs] is []. [t = oterm (Can (Nint (n1+n2))) []]
          The [f] in this case does not depend on any [BTerm]s
          (there aren't any in this case)
          and is hence a constant function.
          The same reason applies for the three cases below.
      -- [NCompOp] : and [bargs] is of the form [arg3, arg4].
          [t] is either [arg3] or [arg4] depending only on the
          head canonical [Opid]s of the [NTerm]s in [pntc]
      -- [NCanTest] : exactly same as above.
    - t converges to a.

    One key observation here is that the second part of this
    3-way split consumes exactly one step. Hence the the first and last
    parts consume at most [k] steps and hence [Hind] (in the definition
    of [extensional_op]) can be applied to
    both these parts.

    To prove [extensional_op op], we use the hypothesis [Has] to infer
    that [lbt'] can also be expressed as [(map (bterm []) pnt')++bargs']
     (see the lemma [blift_numbvars]) such that we have
     [Hasp : bin_rel_nterm approx_star pnt pnt']
     Applying [Hind] along with [Hasp] to the first stage of computation where
     [pnt] converges pointwise to [pntc],
     and  we get
    [Haspc : bin_rel_nterm approx_star pntc pnt'].
    Next, we apply
    [howe_lemma2] pointwise to [Haspc](* make a corollary? *), we get [pntc']
    such that elements of [pnt'] converges to [pntc'] respectively
    such that we have [Haspcc : bin_rel_nterm approx_star pntc pntc']

    Next, the second stage of computation happens and we get that
    [oterm (NCan op) ((map (bterm []) pntc')++bargs')] computes to some
    [t'] in exactly one step. By the property of this
    one step function [f] that we described casewise above,
    we get [Hapt : approx_star t t'].

    Finally, we apply [Hind] to the third stage again to get
    [Hapa : approx_star a t'].
    Since [oterm (NCan op) ((map (bterm []) pnt')++bargs')] reduced to
    [t'], we use the lemma [reduces_to_implies_approx_open] above to get
    [Hao : approx_open t' (oterm (NCan op) ((map (bterm []) pnt')++bargs'))]
    Now, we can use [approx_star_open_trans] on [Hapa] and [Hao] to get
    the desired conclusion of [extensional_op op].

    The concrete Coq proofs of the extensionality lemmas below follow this overall recipe.


*)

Ltac splr :=
  first [ complete sp
        | complete (left; sp; splr)
        | complete (right; sp; splr)
        ].

Ltac make_red_val_or_exc H h :=
  let hyp := fresh h in
  let T := type of H in
  match T with
    | reduces_in_atmost_k_steps ?lib ?t1 ?t2 ?k =>
      assert (computes_to_val_or_exc_in_max_k_steps lib t1 t2 k)
        as hyp
          by (split; [ complete eauto
                     | splr
                     ]
             )
  end.

Ltac make_red_val_like H h :=
  let hyp := fresh h in
  let T := type of H in
  match T with
    | reduces_in_atmost_k_steps ?lib ?t1 ?t2 ?k =>
      assert (computes_to_val_like_in_max_k_steps lib t1 t2 k)
        as hyp
          by (split; [ complete eauto
                     | splr
                     ]
             )
  end.

Lemma approx_star_exception {p} :
  forall lib (a1 a2 e1 e2 : @NTerm p),
    approx_star lib a1 a2
    -> approx_star lib e1 e2
    -> approx_star lib (mk_exception a1 e1) (mk_exception a2 e2).
Proof.
  introv ap1 ap2.
  apply approx_star_congruence; simpl; sp.
  unfold approx_starbts, lblift_sub; simpl; dands; auto; introv j.
  repeat (destruct n; cpx);
    unfold selectbt; simpl; unfold blift_sub.
  - exists ([] : list NVar) a1 a2; dands; auto; left; dands; tcsp; intro i; ginv.
  - exists ([] : list NVar) e1 e2; dands; auto; left; dands; tcsp; intro i; ginv.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma reduces_to_primarg_marker {o} :
  forall lib nc m (l bs : list (@BTerm o)) v,
    reduces_to lib (oterm (NCan nc) (nobnd (oterm (Mrk m) l) :: bs)) v
    -> v = oterm (NCan nc) (nobnd (oterm (Mrk m) l) :: bs).
Proof.
  introv comp.
  unfold reduces_to in comp; exrepnd.
  allapply @reduces_in_atmost_k_steps_primarg_marker; subst; auto.
Qed.

(* !! MOVE to approx *)
Lemma approx_ncan_primarg_marker {o} :
  forall lib ncan m l bs (t : @NTerm o),
    isprogram (oterm (NCan ncan) (nobnd (oterm (Mrk m) l) :: bs))
    -> isprogram t
    -> approx lib (oterm (NCan ncan) (nobnd (oterm (Mrk m) l) :: bs)) t.
Proof.
  introv isp1 isp2.
  unfold approx.
  constructor.
  unfold close_comput; repnd; dands; auto.

  - unfold close_compute_val; introv comp.
    unfold computes_to_value in comp; repnd.
    apply reduces_to_primarg_marker in comp0; ginv.

  - unfold close_compute_exc; introv comp.
    unfold computes_to_exception in comp; repnd.
    apply reduces_to_primarg_marker in comp; ginv.

  - unfold close_compute_mrk; introv comp.
    unfold computes_to_marker in comp; repnd.
    apply reduces_to_primarg_marker in comp; ginv.
Qed.
*)

Lemma approx_star_nat {p} :
  forall lib (t : @NTerm p) n,
    isprogram t
    -> approx_star lib (mk_nat n) t
    -> computes_to_value lib t (mk_nat n).
Proof.
  introv isp apr.
  apply howe_lemma2 in apr; fold_terms; eauto 3 with slow.
  exrepnd.
  unfold approx_starbts, lblift_sub in apr1; allsimpl; repnd; cpx.
Qed.

Lemma approx_star_choice_seq {o} :
  forall lib (t : @NTerm o) n,
    isprogram t
    -> approx_star lib (mk_choice_seq n) t
    -> computes_to_value lib t (mk_choice_seq n).
Proof.
  introv isp apr.
  apply howe_lemma2 in apr; fold_terms; fold (@mk_choice_seq o n) in *; eauto 3 with slow.
  exrepnd.
  unfold approx_starbts, lblift_sub in apr1; allsimpl; repnd; cpx.
Qed.

Lemma bin_rel_nterm_singleton {o} :
  forall (a b : @NTerm o) R,
    R a b -> bin_rel_nterm R [a] [b].
Proof.
  introv h.
  unfold bin_rel_nterm, binrel_list; dands; simpl; auto.
  introv i; destruct n; try omega; auto.
Qed.
Hint Resolve bin_rel_nterm_singleton : slow.

(* !! Move to terms2 *)
Lemma isprogram_cbv_iff2 {p} :
  forall (a : @NTerm p) v b,
    isprogram (mk_cbv a v b)
    <=> isprogram a # isprogram_bt (bterm [v] b).
Proof.
  introv.
  rw @isprogram_cbv_iff.
  unfold isprogram_bt; simpl.
  unfold closed_bt; simpl.
  rw <- null_iff_nil.
  rw null_remove_nvars.
  rw subvars_prop.
  split; intro k; repnd; dands; auto.
  inversion k; sp.
Qed.

Lemma compute_step_cbv_iscan {o} :
  forall lib (t : @NTerm o) v u,
    iscan t
    -> compute_step lib (mk_cbv t v u) = csuccess (subst u v t).
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst; csunf; simpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma reduces_to_implies_approx_open1 {o} :
  forall lib (t x : @NTerm o),
    isprogram t
    -> reduces_to lib t x
    -> approx_open lib x t.
Proof.
  introv isp r.
  apply reduces_to_implies_approx_open in r; sp.
Qed.

Lemma compute_step_try_iscan {o} :
  forall lib (t : @NTerm o) n v u,
    iscan t
    -> compute_step lib (mk_try t n v u)
       = csuccess (mk_atom_eq n n t mk_bot).
Proof.
  introv isc.
  apply iscan_implies in isc; repndors; exrepnd; subst; csunf; simpl;
  unfold apply_bterm; simpl; auto.
Qed.

Lemma approx_star_mk_atom_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx_star lib a1 a2
    -> approx_star lib b1 b2
    -> approx_star lib c1 c2
    -> approx_star lib d1 d2
    -> approx_star lib (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv apra aprb aprc aprd.
  apply approx_star_congruence; simpl; unfold num_bvars; simpl; auto.
  unfold approx_starbts, lblift_sub; simpl; dands; auto.
  introv i.
  unfold selectbt.
  repeat (destruct n; simpl; try omega;
          try (complete (apply blift_sub_nobnd_congr; auto))).
Qed.

Lemma no_change_after_val_like3 {o} :
  forall lib (t : @NTerm o) k1 v1 k2,
    reduces_in_atmost_k_steps lib t v1 k1
    -> isprogram v1
    -> isvalue_like v1
    -> k1 <= k2
    -> reduces_in_atmost_k_steps lib t v1 k2.
Proof.
  introv r isp isv leq.
  eapply no_change_after_val_like; eauto.
Qed.

Ltac extensional_ind H k hyp :=
    match type of H with
      | reduces_in_atmost_k_steps ?lib ?t ?v ?n =>
        apply (no_change_after_val_like3 lib t n v k) in H;
          auto;
          make_red_val_like H hyp
    end.

Lemma approx_star_bterm_numvars {o} :
  forall lib op (b1 b2 : @BTerm o),
    approx_star_bterm lib op b1 b2
    -> num_bvars b1 = num_bvars b2.
Proof.
  destruct b1, b2; introv ap.
  unfold approx_star_bterm, blift_sub in ap; exrepnd.
  inversion ap2; subst.
  inversion ap0; subst.
  unfold num_bvars; simpl; omega.
Qed.

Lemma approx_starbts_numvars {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)),
    approx_starbts lib op bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; intro ap; allsimpl; auto;
  unfold approx_starbts, lblift_sub in ap; repnd; allsimpl; cpx.
  pose proof (ap 0) as h; autodimp h hyp; [omega|].
  unfold selectbt in h; allsimpl.
  apply eq_cons; [ complete (eapply approx_star_bterm_numvars; eauto)|].
  apply IHbs1.
  unfold approx_starbts, lblift_sub; dands; auto; introv k.
  pose proof (ap (S n)) as x; autodimp x hyp; omega.
Qed.


(*
Lemma extensional_apseq {p} : forall s : nseq, extensional_op (@NCan p (NApseq s)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  assert (m <= S k) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_cbv_implies; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    try (complete (csunf XX1; allsimpl; ginv));[].

    csunf XX1; allsimpl.
    apply compute_step_apseq_success in XX1; exrepnd; subst.
    allrw <- @isprogram_apseq_iff.
    apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto; [].

    unfold lblift_sub in Has; repnd; allsimpl; cpx.
    repeat(approxrelbtd); show_hyps.
    allrw <- @isprogram_apseq_iff.
    fold_terms.

    make_red_val_like Hcv3 h.
    pose proof (Hi la (mk_nat n) lar) as q.
    repeat (autodimp q hyp).
    apply howe_lemma2 in q; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in q1; repnd; allsimpl; cpx.
    clear q1.
    fold_terms.

    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    unfold computes_to_value in q0; repnd.
    eapply reduces_to_trans;[apply reduces_to_prinarg;exact q1|].
    apply reduces_to_if_step; csunf; simpl.
    rw @Znat.Nat2Z.id.
    boolvar; try omega; auto.

  - allapply @isprogram_apseq_implies; exrepnd; ginv.
    apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    apply approx_star_bterm_nobnd2 in Has0bt.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := a2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @fold_cbv.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_apseq s (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
*)


(*
(* !! MOVE to computation4 *)
Lemma computes_to_val_like_in_max_k_steps_primarg_marker {o} :
  forall (lib : @library o) k nc mrk l bs v,
    computes_to_val_like_in_max_k_steps
      lib
      (oterm (NCan nc) (nobnd (oterm (Mrk mrk) l) :: bs))
      v k
    -> False.
Proof.
  introv h.
  unfold computes_to_val_like_in_max_k_steps in h; repnd.
  apply reduces_in_atmost_k_steps_primarg_marker in h0; subst.
  dorn h; sp.
Qed.
*)

(*
Lemma lblift_approx_star_implies_sub_range_rel {o} :
  forall lib (bs1 bs2 : list (@BTerm o)) vars,
    lblift (approx_star lib) bs1 bs2
    -> sub_range_rel
         (approx_star lib)
         (mk_abs_subst vars bs1)
         (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; introv ap; allsimpl; auto.
  - rw @mk_abs_subst_nil_r; simpl; auto.
  - unfold lblift in ap; cpx.
  - unfold lblift in ap; cpx.
  - destruct vars; simpl; auto.
    destruct a as [l1 t1]; destruct b as [l2 t2].
    unfold lblift in ap; simpl in ap; repnd; cpx.
    pose proof (ap 0) as h; autodimp h hyp; [omega|].
    unfold selectbt in h; simpl in h.
    unfold blift in h; exrepnd.
    inversion h2; inversion h0; subst; allsimpl; cpx; GC.
    destruct l1; destruct l2; allsimpl; cpx; GC.
    allunfold @var_ren; allsimpl.
    allrw @lsubst_nil.
    dands; eauto with slow.
    apply IHbs1.
    unfold lblift; dands; auto; introv k.
    pose proof (ap (S n0)) as x; autodimp x hyp; omega.
Qed.
*)

(*
Inductive so_approx_star {o} :
  @library o -> @SOTerm o -> @SOTerm o -> [univ] :=
| soapsv:
    forall lib v t2,
      so_approx_open lib (sovar v ts1) t2
      -> so_approx_star lib (sovar v ts2) t2
| soapso:
    forall lib
           (op : Opid) (t2: NTerm)
           (lbt1 lbt1' : list BTerm),
      length lbt1 = length lbt1'
      -> lblift (approx_star lib) lbt1 lbt1'
      -> approx_open lib (oterm op lbt1') t2
      -> approx_star lib (oterm op lbt1) t2.
*)

(*
Lemma computes_to_val_or_exc_in_max_k_steps_marker {o} :
  forall lib (k : nat) mrk (l : list (@BTerm o)) (v : NTerm),
    computes_to_val_or_exc_in_max_k_steps lib (oterm (Mrk mrk) l) v k
    -> False.
Proof.
  introv comp.
  unfold computes_to_val_or_exc_in_max_k_steps in comp; repnd.
  apply reduces_in_atmost_k_steps_marker in comp0; subst.
  dorn comp; sp.
Qed.
*)

(*
Lemma computes_to_val_like_in_max_k_steps_marker {o} :
  forall lib (k : nat) mrk (l : list (@BTerm o)) (v : NTerm),
    computes_to_val_like_in_max_k_steps lib (oterm (Mrk mrk) l) v k
    -> v = oterm (Mrk mrk) l.
Proof.
  induction k; introv comp.
  - rw @computes_to_val_like_in_max_k_steps_0 in comp; repnd; auto.
  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    simpl in comp1; ginv.
    apply IHk in comp0; auto.
Qed.

Lemma nuprl_extensional_mrk {p} :
  forall m : marker, @extensional_op p (Mrk m).
Proof.
  introv.
  unfold extensional_op.
  introv isp1 isp2 isp3 comp ap ext.
  apply computes_to_val_like_in_max_k_steps_marker in comp; subst.
  apply ismrk_implies in isp2; tcsp; exrepnd.
  inversion isp0; subst.
  apply ismrk_implies in isp3; tcsp; exrepnd.
  inversion isp2; subst; fold_terms.
  apply (apso _ _ _ [] []); simpl; auto; fold_terms.
  apply approx_implies_approx_open.
  unfold approx; constructor.
  unfold close_comput; dands; auto.
  - unfold close_compute_val; introv comp.
    unfold computes_to_value in comp; repnd.
    apply reduces_to_marker in comp0; tcsp.
    inversion comp0.

  - unfold close_compute_exc; introv comp.
    unfold computes_to_exception in comp; repnd.
    apply reduces_to_marker in comp; tcsp.
    inversion comp.

  - unfold close_compute_mrk; introv comp.
    unfold computes_to_marker in comp; repnd.
    apply reduces_to_marker in comp; tcsp.
    inversion comp; subst.
    apply compute_to_marker_mrk.
Qed.
*)

Lemma computes_to_val_like_in_max_k_steps_parallel_implies2 {o} :
  forall lib k (bs : list (@BTerm o)) v,
    computes_to_val_like_in_max_k_steps lib (oterm (NCan NParallel) bs) v k
    -> {x : NTerm
        & {u : NTerm
        & {bs' : list BTerm
        & {m : nat
        & k = S m
        # bs = nobnd u :: bs'
        # computes_to_val_like_in_max_k_steps lib u x m
        # {c : CanonicalOp & {bs : list BTerm & x = oterm (Can c) bs # v = mk_axiom}}
          [+]
          (isexc x # x = v)}}}}.
Proof.
  induction k; introv comp; simpl.

  - allunfold @computes_to_val_like_in_max_k_steps.
    rw @reduces_in_atmost_k_steps_0 in comp; repnd; subst.
    unfold isvalue_like in comp; allsimpl; sp.

  - rw @computes_to_val_like_in_max_k_steps_S in comp; exrepnd.
    csunf comp1; allsimpl.
    destruct bs as [|b bs]; ginv.
    destruct b as [l t].
    destruct l; ginv.
    destruct t as [z|op bts]; ginv;[].
    dopid op as [can|ncan|exc|abs] Case; ginv.

    + Case "Can".
      apply compute_step_parallel_success in comp1; subst.
      apply computes_to_val_like_in_max_k_steps_can_iff in comp0; subst.
      exists (oterm (Can can) bts) (oterm (Can can) bts) bs k; dands; auto.
      { apply computes_to_val_like_in_max_k_steps_can_iff; sp. }
      left; eexists; eexists; dands; eauto.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst; allunfold @nobnd; ginv.
      exists x (oterm (NCan ncan) bts) bs' (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists u; auto.

    + Case "Exc".
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      exists (oterm Exc bts) (oterm Exc bts) bs k; dands; auto.
      apply computes_to_val_like_in_max_k_steps_exc_iff; sp.

    + Case "Abs".
      remember (compute_step lib (oterm (Abs abs) bts)) as comp'; destruct comp'; ginv.
      apply IHk in comp0; clear IHk; exrepnd; subst.
      allunfold @nobnd; ginv.
      exists x (oterm (Abs abs) bts) bs' (S m); dands; auto.
      rw @computes_to_val_like_in_max_k_steps_S.
      exists u; auto.
Qed.

Lemma isprogram_comp_seq1_implies_ex {o} :
  forall (l : list (@BTerm o)),
    isprogram (oterm (NCan NCompSeq1) l)
    -> {t1 : NTerm & {t2 : NTerm
        & l = [nobnd t1, nobnd t2]
        # isprogram t1
        # isprogram t2}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  destruct l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Lemma isprogram_comp_seq2_implies_ex {o} :
  forall nfo (l : list (@BTerm o)),
    isprogram (oterm (NCan (NCompSeq2 nfo)) l)
    -> {t1 : NTerm & {t2 : NTerm
        & l = [nobnd t1, nobnd t2]
        # isprogram t1
        # isprogram t2}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  destruct l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Lemma isprogram_comp_seq1_implies {o} :
  forall (a b : @NTerm o),
    isprogram (mk_comp_seq1 a b)
    -> (isprogram a # isprogram b).
Proof.
  introv isp.
  apply isprogram_comp_seq1_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma isprogram_comp_seq2_implies {o} :
  forall l k (a b : @NTerm o),
    isprogram (mk_comp_seq2 l k a b)
    -> (isprogram a # isprogram b).
Proof.
  introv isp.
  apply isprogram_comp_seq2_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_isvalue_implies {o} :
  forall lib k (a b : @NTerm o),
    reduces_in_atmost_k_steps lib a b k
    -> isvalue a
    -> b = a.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    rewrite compute_step_value in comp1; auto; ginv.
    apply IHk in comp0; auto.
Qed.

Lemma isvalue_mk_fresh_choice_nat_seq {o} :
  forall (lib : @library o) l,
    isvalue (mk_fresh_choice_nat_seq lib l).
Proof.
  introv.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isvalue_mk_fresh_choice_nat_seq : slow.

Lemma implies_isprogram_mk_comp_seq2 {o} :
  forall l i (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_comp_seq2 l i a b).
Proof.
  introv ispa ispb.
  unfold isprogram, closed in *; repnd; simpl in *.
  allrw; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_mk_comp_seq2 : slow.

Lemma approx_star_bterm_nobnd_iff {o} :
  forall lib (op : Opid) (a b : @NTerm o),
    approx_star_bterm lib op (bterm [] a) (bterm [] b) <=> approx_star lib a b.
Proof.
  introv; split; intro h.
  - eapply approx_star_bterm_nobnd2; eauto.
  - unfold approx_star_bterm, blift_sub; simpl.
    exists ([] : list NVar) a b; dands; auto.
    destruct (dec_op_eq_fresh op); subst; tcsp.
    right.
    exists ([] : @Sub o); dands; autorewrite with slow; tcsp; eauto 3 with slow.
Qed.

Lemma approx_starbts_nil {o} :
  forall (lib : @library o) nc, approx_starbts lib nc [] [].
Proof.
  introv; unfold approx_starbts, lblift_sub; simpl; dands; tcsp.
Qed.
Hint Resolve approx_starbts_nil : slow.

Lemma implies_approx_star_mk_comp_seq2 {o} :
  forall lib l i (a b c d : @NTerm o),
    approx_star lib a c
    -> approx_star lib b d
    -> approx_star lib (mk_comp_seq2 l i a b) (mk_comp_seq2 l i c d).
Proof.
  introv apra aprb.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_comp_seq2 : slow.

Lemma implies_approx_star_mk_apply {o} :
  forall lib (a b c d : @NTerm o),
    approx_star lib a c
    -> approx_star lib b d
    -> approx_star lib (mk_apply a b) (mk_apply c d).
Proof.
  introv apra aprb.
  apply approx_star_congruence; simpl; auto.
  allrw @approx_starbts_cons.
  allrw @approx_star_bterm_nobnd_iff; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_apply : slow.

Lemma implies_approx_star_mk_zero {o} :
  forall (lib : @library o),
    approx_star lib mk_zero mk_zero.
Proof.
  introv.
  apply approx_star_congruence; simpl; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_zero : slow.

Hint Resolve isprogram_mk_nat : slow.

Lemma implies_approx_star_mk_nat {o} :
  forall (lib : @library o) k,
    approx_star lib (mk_nat k) (mk_nat k).
Proof.
  introv.
  apply approx_star_congruence; simpl; auto; eauto 2 with slow.
Qed.
Hint Resolve implies_approx_star_mk_nat : slow.
