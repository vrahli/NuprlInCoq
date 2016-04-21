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
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> subset (get_utokens t1) l'
    -> subset (get_utokens t2) l'
    -> approx_star lib (lsubst t1 sub) (lsubst t2 sub)
    -> approx_star lib (lsubst t1 sub') (lsubst t2 sub').
Proof.
  introv nrut1 nrut2 eqdoms ss1 ss2 ss3 ss4 apr.

  pose proof (length_dom sub) as len.
  rw eqdoms in len; rw @length_dom in len.

  pose proof (change_nr_ut_sub_in_lsubst_aux_approx_star
                lib (lsubst t1 sub) (lsubst t2 sub)
                (nrut_subs_to_utok_ren sub sub')) as h.
  erewrite @range_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  erewrite @dom_utok_ren_nrut_subs_to_utok_ren in h; eauto.
  repeat (autodimp h hyp); eauto 3 with slow.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss3 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

    + apply in_get_utokens_sub in j0; exrepnd.
      apply in_sub_keep_first in j1; repnd.
      apply sub_find_some in j2.
      destruct j.
      apply in_sub_eta in j2; repnd.
      unfold get_utokens_sub; rw lin_flat_map.
      eexists; dands; eauto.

  - introv i j.
    allrw in_diff; repnd.
    apply get_utokens_lsubst in j0; allrw in_app_iff; repndors.

    + apply ss4 in j0.
      unfold nrut_sub in nrut2; repnd.
      apply nrut2 in j0; sp.

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
  nterm_ind1s b as [x|f ind|o lbt Hind] Case; introv Hap H1len H2len Hdis Hbin;
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

  - Case "sterm".
    allsimpl.
    inversion Hap as [|? ? ? ? imp aop|]; subst; clear Hap.
    econstructor; eauto.
    apply (approx_open_lsubst_congr _ _ _ (combine lvi lnta')) in aop; eauto 3 with slow.
    autorewrite with slow in *.
    unfold lsubst in aop; boolvar; auto.
    allrw disjoint_app_r; repnd.
    allrw <- @sub_free_vars_is_flat_map_free_vars_range.
    rw @sub_free_vars_combine in n; tcsp.

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
                    (get_utokens nt1'
                                 ++ get_utokens nt2'
                                 ++ flat_map get_utokens lnta
                                 ++ flat_map get_utokens lnta'))
        as exnrut; exrepnd.

      pose proof (approx_star_change_nrut_sub
                    lib nt1' nt2' sub (get_utokens nt1' ++ get_utokens nt2')
                    sub0
                    (get_utokens nt1'
                                 ++ get_utokens nt2'
                                 ++ flat_map get_utokens lnta
                                 ++ flat_map get_utokens lnta'))
           as ch.
      repeat (autodimp ch hh); tcsp; eauto 3 with slow.

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
        apply get_utokens_lsubst_aux in i; rw in_app_iff in i; repndors; tcsp;
        apply in_get_utokens_sub in i; exrepnd; apply in_sub_keep_first in i0; repnd;
        apply sub_find_some in i2; apply in_sub_filter in i2; repnd; apply in_combine in i3; repnd.
        - right; right; left; rw lin_flat_map; eexists; dands; eauto.
        - right; right; right; rw lin_flat_map; eexists; dands; eauto.
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
                  (get_utokens nt1'
                               ++ get_utokens nt2'
                               ++ get_utokens_sub sub))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub0 (get_utokens nt1' ++ get_utokens nt2')
                  sub1
                  (get_utokens nt1'
                               ++ get_utokens nt2'
                               ++ get_utokens_sub sub))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 3 with slow.

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
      apply get_utokens_lsubst in i; rw in_app_iff in i; repndors; tcsp;
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
  nterm_ind1s t as [v|f ind|o lbt Hind] Case;
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
        # nrut_sub (get_utokens nt1' ++ get_utokens nt2') sub
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

  - apply alphaeq_preserves_utokens in hyp0.
    apply alphaeq_preserves_utokens in hyp2.
    repeat (rw @get_utokens_lsubst_allvars; eauto with slow).
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
                  (get_utokens nt1'
                               ++ get_utokens nt2'
                               ++ get_utokens nt1'0
                               ++ get_utokens nt2'0))
      as exnrut; exrepnd.

    pose proof (approx_star_change_nrut_sub
                  lib nt1' nt2' sub (get_utokens nt1' ++ get_utokens nt2')
                  sub0
                  (get_utokens nt1'
                               ++ get_utokens nt2'
                               ++ get_utokens nt1'0
                               ++ get_utokens nt2'0))
      as ch.
    repeat (autodimp ch hh); tcsp; eauto 3 with slow.

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

Lemma howe_lemma2_seq {o} :
  forall lib (f : @ntseq o) (b : @NTerm o),
    isprogram (sterm f)
    -> isprogram b
    -> approx_star lib (sterm f) b
    -> {f' : ntseq
        & (forall n, alpha_eq (f n) (f' n))
        # computes_to_seq lib b f'}.
Proof.
  introv Hprt Hprb Hap.
  inversion Hap as [|? ? ? ? imp aop|]; clear Hap; subst.

  apply approx_open_approx in aop; eauto 3 with slow.
  invertsna aop Hclose.
  repnud Hclose.
  dimp (Hclose4 f2); [apply reduces_to_symm|].
  exrepnd.
  eexists; dands;[|eauto].
  introv; eauto 3 with slow.
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
  - apply howe_lemma2_seq in apr; auto.
    exrepnd.
    unfold computes_to_value.
    unfold computes_to_seq in apr0.
    eexists;dands;[|eauto| |]; simpl; eauto 3 with slow.
    apply alpha_implies_approx_star; eauto 3 with slow.
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
    (Has : lblift_sub o (approx_star lib) lbt lbt')
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
    -> lblift_sub o (approx_star lib) lbt lbt'
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

Lemma blift_sub_nobnd_congr {p} :
  forall R op t1 t2,
  R t1 t2
  -> @blift_sub p op R (bterm [] t1) (bterm [] t2).
Proof.
  introv Ht.
  exists (@nil NVar) t1 t2; dands; eauto with slow.
  destruct (dec_op_eq_fresh op) as [d|d]; tcsp.
  right; exists ([] : @Sub p); simpl; allrw @lsubst_nil; dands; eauto with slow.
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
| [  |- blift_sub _ (approx_star _) (bterm [] ?t1) (bterm [] ?t2)] =>
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
  | [H: (forall _:nat, (_< ?m) -> blift_sub _ _ _ _)  |- _ ] => 
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
  | [H: blift_sub _ (approx_star _) (bterm [] _) (bterm [] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: blift_sub _ (approx_star _) (bterm [_] _) (bterm [_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: blift_sub _ (approx_star _) (bterm [_,_] _) (bterm [_,_] _) |- _] => hide_hyp H
  | [H: approx_star_bterm _ _ (bterm [] ?nt) _ |- _] =>
    apply approx_star_bterm_nobnd in H;
      let ntr := fresh nt "r" in
      (destruct H as [ntr H]);
        repnd; subst
  | [H: blift_sub _ (approx_star _) (bterm [] ?nt) _ |- _] =>
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
  | [H: blift_sub _ (approx_star _) (bterm [?v] ?nt) _ |- _] =>
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
  | [H: blift_sub _ (approx_star _) (bterm [?v1, ?v2] ?nt) _ |- _] =>
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
    | sterm _ => []
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

Hint Resolve isprogram_mk_nseq : slow.

Lemma approx_star_nseq {p} :
  forall lib (t : @NTerm p) s,
    isprogram t
    -> approx_star lib (mk_nseq s) t
    -> computes_to_value lib t (mk_nseq s).
Proof.
  introv isp apr.
  apply howe_lemma2 in apr; fold_terms; eauto 3 with slow.
  exrepnd.
  unfold approx_starbts, lblift_sub in apr1; allsimpl; repnd; cpx.
Qed.

Lemma extensional_apply {p} : extensional_op (@NCan p NApply).
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
  apply isprogram_apply_implies in Hcv6; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { csunf XX1; allsimpl.
      apply compute_step_apply_success in XX1; repndors; exrepnd; subst; ginv.

      + (* destruct lhs for a bit so that the args of lambda show up*)
        rename v into lamv.
        rename b into lamb.
        rename la into lamnt.
        apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
        duplicate Has.
        unfold lblift_sub in Has; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        make_red_val_like Hcv3 h.
        unfold extensional_op_ind in Hi.
        apply Hi with (v := lamntr) in h; eauto; prove_isprogram.
        apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
        duplicate h1.
        rename a into c.
        unfold approx_starbts, lblift_sub in h1; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        apply apply_bterm_approx_star_congr with
        (lnt1:= [arg]) (lnt2:= [argr]) in h10bt; tcsp;
        try (complete (intro xx; ginv));
        [|prove_bin_rel_nterm; fail].
        apply no_change_after_val_like with (k2 := k) in XX0; auto.
        repnud h0.

        match goal with
            [ |- approx_star _ _ (oterm (NCan ?no) _)] =>
            let T := type of Has0 in
            match T with
              | lblift_sub _ (approx_star _) _ (_::?tr) =>
                apply reduces_to_prinarg
                with (lbt:= tr) (op:=no) in h1
            end
        end. (* this will be used later in this proof *)
        pose proof (reduces_to_preserves_program _ _ _ h1 Hprt') as Hispr.
        apply reduces_atmost_preserves_program in Hcv4; auto; try omega.

        make_red_val_like XX0 hh.

        let T:= type of h10bt  in
        match T with
          | approx_star ?lib ?tl ?tr =>
            assert (isprogram tl) by (apply (preserve_compute_step lib) with (t2:=tl) in Hcv4;sp);
              assert(isprogram tr) by (apply (preserve_compute_step lib) with (t2:=tr) in Hispr;sp);
              apply Hi with (v:=tr) in hh; auto;
              apply approx_star_open_trans with (b:= tr); auto
        end.
        apply approx_implies_approx_open;
          apply reduces_to_implies_approx_eauto;auto;
          eapply reduces_to_if_split1; eauto.

      + apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
        duplicate Has.
        unfold lblift_sub in Has; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        make_red_val_like Hcv3 h.
        unfold extensional_op_ind in Hi.
        apply Hi with (v := lar) in h; eauto; prove_isprogram.
        apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
        unfold approx_starbts, lblift_sub in h1; repnd; allsimpl; cpx.
        clear h1.
        rename a into c.
        apply no_change_after_val_like with (k2 := k) in XX0; auto.
        repnud h0.

        match goal with
            [ |- approx_star _ _ (oterm (NCan ?no) _)] =>
            let T := type of Has0 in
            match T with
              | lblift_sub _ (approx_star _) _ (_::?tr) =>
                apply reduces_to_prinarg
                with (lbt:= tr) (op:=no) in h1
            end
        end. (* this will be used later in this proof *)
        pose proof (reduces_to_preserves_program _ _ _ h1 Hprt') as Hispr.
        apply reduces_atmost_preserves_program in Hcv4; auto; try omega.

        make_red_val_like XX0 hh.

        allrw <- @isprogram_apply_iff; repnd.

        pose proof (Hi (mk_eapply (mk_nseq f) arg) c (mk_eapply (mk_nseq f) argr)) as q.
        repeat (autodimp q hyp); try (apply isprogram_eapply); auto.
        { apply approx_star_congruence3; try (apply isprogram_eapply); auto.
          repeat (apply approx_starbts_cons; dands; eauto 3 with slow).
          { unfold nobnd; prove_approx_star; auto.
            apply approx_open_implies_approx_star.
            apply approx_implies_approx_open; eauto 3 with slow. }
          { unfold nobnd; prove_approx_star; auto. }
          { unfold approx_starbts, lblift_sub; simpl; sp. }
        }

        eapply approx_star_open_trans;[exact q|].
        apply approx_implies_approx_open.
        apply reduces_to_implies_approx_eauto;
          allrw <- @isprogram_apply_iff; auto.
        eapply reduces_to_if_split1; eauto.
    }

    { allsimpl.
      csunf XX1; allsimpl; ginv.
      apply no_change_after_value_ra with (k2:=k) in Hcv3; eauto 2 with slow.

      unfold lblift_sub in Has; repnd; allsimpl; cpx.
      repeat(approxrelbtd); show_hyps.
      allrw <- @isprogram_apply_iff; repnd.
      fold_terms.

      make_red_val_like Hcv3 h.
      pose proof (Hi la (sterm f0) lar) as q.
      repeat (autodimp q hyp).
      apply howe_lemma2_seq in q; exrepnd; auto; prove_isprogram.

      apply reduces_in_atmost_k_steps_eapply_sterm_to_isvalue_like in XX0; auto.
      repndors; exrepnd.

      - apply no_change_after_value_ra with (k2:=k) in XX2; eauto 2 with slow; try omega;[].
        pose proof (Hi a0 (mk_nat n) a0r) as z.
        make_red_val_like XX2 ca0.
        repeat (autodimp z hyp); eauto 2 with slow;[].
        apply approx_star_nat in z; auto.

        apply approx_open_implies_approx_star.
        apply approx_implies_approx_open.
        eapply approx_trans;
          [apply reduces_to_implies_approx_eauto;[|eexists;exact XX1];eauto 3 with slow
          |].
        eapply approx_trans;
          [|apply reduces_to_implies_approx_eauto;[|apply apply_sterm_nat_implies; eauto];
            eauto 3 with slow].
        apply alpha_implies_approx3; eauto 3 with slow.

      - apply isexc_implies in XX1; auto; exrepnd; subst.
        apply no_change_after_val_like with (k2:=k) in XX2; try splr; try omega.
        make_red_val_like XX2 ca0.
        pose proof (Hi a0 (mk_exception a1 e) a0r) as z.
        repeat (autodimp z hyp); eauto 2 with slow;[].
        apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

        apply approx_star_open_trans with (b := mk_exception a' e').
        { apply approx_star_exception; auto. }

        apply approx_implies_approx_open.
        apply computes_to_exception_implies_approx; auto; prove_isprogram.
        allrw @computes_to_exception_as_reduces_to.
        apply reduces_to_trans with (b := mk_apply (sterm f') a0r).
        { apply reduces_to_prinarg; auto. }

        eapply apply_sterm_exception_implies; auto.
        apply reduces_to_symm.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    allrw @fold_exception.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := lar) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_apply (mk_exception a' e') a0r).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
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

Lemma extensional_eapply {p} : extensional_op (@NCan p NEApply).
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
  apply isprogram_eapply_implies in Hcv6; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
    unfold lblift_sub in Has; repnd; allsimpl; cpx.
    repeat(approxrelbtd); show_hyps.
    make_red_val_like Hcv3 h.
    pose proof (Hi la f lar) as q.
    repeat (autodimp q hyp); prove_isprogram.
    allrw <- @isprogram_eapply_iff; repnd.

    apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { csunf XX1; allsimpl.

      apply compute_step_eapply_success in XX1; exrepnd; allunfold @nobnd; ginv.
      apply eapply_wf_def_oterm_implies in XX3.
      destruct XX3 as [XX3|XX3]; exrepnd; subst; ginv.

      { apply howe_lemma2 in q; exrepnd; auto.
        unfold approx_starbts, lblift_sub in q1; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        fold_terms.
        applydup @preserve_program in q0; auto.

        repndors; exrepnd; subst; ginv.

        - applydup @howe_lemma2_implies_iscan in Has1bt; auto; exrepnd.
          applydup @preserve_program in Has1bt2; auto.

          eapply approx_star_open_trans in Has1bt;
            [|apply approx_implies_approx_open;
               apply computes_to_value_implies_approx2;[|exact Has1bt2];
               auto].

          apply apply_bterm_approx_star_congr with
          (lnt1:= [arg2]) (lnt2:= [v0]) in q10bt; simpl; tcsp; eauto 2 with slow;
          try (complete (intro xx; ginv)).

          apply no_change_after_val_like with (k2 := k) in XX0; auto.
          make_red_val_like XX0 w.
          pose proof (Hi
                        (apply_bterm (bterm [v] t) [arg2])
                        a
                        (apply_bterm (bterm [vr] tr) [v0])) as z.
          repeat (autodimp z hyp); prove_isprogram;
          try (apply isprogram_bt_implies; simpl; auto; prove_isprogram;
               try (apply implies_isprogram_bt_lam; auto);
               introv i; repndors; subst; tcsp);[].

          eapply approx_star_open_trans;[exact z|].
          apply approx_implies_approx_open.
          apply reduces_to_implies_approx_eauto; prove_isprogram.
          apply eapply_red_lam_val_implies; simpl; auto.

        - apply isexc_implies in XX2; auto; exrepnd; subst.
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply howe_lemma2_exc in Has1bt; prove_isprogram; exrepnd.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_lam_exception_implies; eauto.

        - fold_terms.
          apply reduces_in_atmost_k_steps_eapply_lam_to_isvalue_like in XX0; auto.

          repndors; exrepnd.

          + apply no_change_after_val_like with (k2:=k) in XX2; eauto 2 with slow; try omega;[].
            make_red_val_like XX2 cak.

            applydup @preserve_compute_step in XX1; auto.
            applydup @reduces_atmost_preserves_program in XX5; auto.
            assert (reduces_in_atmost_k_steps lib arg2 c (S i)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
            apply no_change_after_val_like with (k2:=k) in ra2; eauto 2 with slow; try omega;[].
            make_red_val_like ra2 cck.
            pose proof (Hi arg2 c a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            applydup @howe_lemma2_implies_iscan in z; auto; exrepnd.

            eapply approx_star_open_trans in z;
              [|apply approx_implies_approx_open;
                 apply computes_to_value_implies_approx2;[|exact z2];
                 auto];[].

            apply apply_bterm_approx_star_congr
            with (lnt1:= [c]) (lnt2:= [v0]) in q10bt;
              simpl; tcsp; eauto 2 with slow;
              try (complete (intro xx; ginv));[].
            allunfold @apply_bterm; allsimpl; allrw @fold_subst.

            pose proof (Hi (subst t v c) a (subst tr vr v0)) as w.
            repeat (autodimp w hyp); prove_isprogram;
            try (try (apply isprogram_subst_if_bt);
                 try (apply isprogram_bt_implies);
                 try (apply implies_isprogram_bt_lam);
                 simpl; auto; prove_isprogram;
                 introv i; repndors; subst; tcsp).

            eapply approx_star_open_trans;[exact w|].
            apply approx_implies_approx_open.
            apply reduces_to_implies_approx_eauto; prove_isprogram.
            apply eapply_red_lam_val_implies; simpl; auto.

          + apply isexc_implies in XX2; auto; exrepnd; subst.

            assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }

            apply no_change_after_val_like with (k2:=k) in ra2; try splr; try omega.
            make_red_val_like ra2 ca0.
            pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

            apply approx_star_open_trans with (b := mk_exception a' e').
            { apply approx_star_exception; auto. }

            apply approx_implies_approx_open.
            apply computes_to_exception_implies_approx; auto; prove_isprogram.
            allrw @computes_to_exception_as_reduces_to.
            eapply eapply_lam_exception_implies; eauto.
      }

      { fold_terms.
        apply approx_star_nseq in q; auto;[].

        repndors; exrepnd; subst; ginv.

        - eapply compute_step_eapply2_success in XX1; repnd; GC.
          repndors; exrepnd; ginv;[].
          apply approx_star_nat in Has1bt; auto;[].
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply approx_open_implies_approx_star.
          apply approx_implies_approx_open.
          apply reduces_to_implies_approx1;[apply isprogram_eapply;eauto 2 with slow|].
          allunfold @computes_to_value; repnd.
          eapply reduces_to_trans;
            [apply implies_eapply_red;
              [|eauto
               |eauto]
            |]; eauto 3 with slow.
          apply reduces_to_if_step; csunf; simpl.
          dcwf xx; simpl; boolvar; try omega.
          rw @Znat.Nat2Z.id; auto.

        - apply isexc_implies in XX2; auto; exrepnd; subst.
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply howe_lemma2_exc in Has1bt; prove_isprogram; exrepnd.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_nseq_exception_implies; eauto.

        - fold_terms.
          apply reduces_in_atmost_k_steps_eapply_nseq_to_isvalue_like in XX0; auto.

          repndors; exrepnd; subst.

          + applydup @preserve_compute_step in XX1; auto.
            assert (reduces_in_atmost_k_steps lib arg2 (mk_nat n) (S i)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
            apply no_change_after_val_like with (k2:=k) in ra2; eauto 2 with slow; try omega;[].
            make_red_val_like ra2 cck.
            pose proof (Hi arg2 (mk_nat n) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply approx_star_nat in z; eauto 2 with slow;[].

            apply approx_open_implies_approx_star.
            apply approx_implies_approx_open.
            apply reduces_to_implies_approx1;[apply isprogram_eapply;eauto 2 with slow|].
            allunfold @computes_to_value; repnd.
            eapply reduces_to_trans;
              [apply implies_eapply_red;
                [|eauto
                 |eauto]
              |]; eauto 3 with slow.
            apply reduces_to_if_step; csunf; simpl.
            dcwf xx; simpl; boolvar; try omega.
            rw @Znat.Nat2Z.id; auto.

          + apply isexc_implies in XX2; auto; exrepnd; subst.

            assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }

            apply no_change_after_val_like with (k2:=k) in ra2; try splr; try omega.
            make_red_val_like ra2 ca0.
            pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

            apply approx_star_open_trans with (b := mk_exception a' e').
            { apply approx_star_exception; auto. }

            apply approx_implies_approx_open.
            apply computes_to_exception_implies_approx; auto; prove_isprogram.
            allrw @computes_to_exception_as_reduces_to.
            eapply eapply_nseq_exception_implies; eauto.
      }

    }


    { allsimpl.
      csunf XX1; allsimpl; ginv.
      apply howe_lemma2_seq in q; exrepnd; auto; prove_isprogram.
      apply compute_step_eapply_success in XX1; exrepnd; allunfold @nobnd; ginv.
      applydup @reduces_to_preserves_program in q0; auto.
      fold_terms.

      repndors; exrepnd; subst.

      - apply compute_step_eapply2_success in XX1; repnd; GC.
        repndors; exrepnd; ginv.
        apply approx_star_nat in Has1bt; auto.

        apply no_change_after_val_like with (k2:=k) in XX0; eauto 2 with slow; try omega;[].
        make_red_val_like XX0 ca0.
        pose proof (Hi (f n) a (f' n)) as z.
        repeat (autodimp z hyp); eauto 2 with slow;[|].
        { apply alpha_implies_approx_star; eauto 3 with slow. }

        eapply approx_star_open_trans;[eauto|].
        apply approx_implies_approx_open.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        apply eapply_red_sterm_nat_implies; auto.

      - apply isexc_implies in XX2; auto; exrepnd; subst.
        apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
        apply howe_lemma2_exc in Has1bt; exrepnd; auto; prove_isprogram.

        apply approx_star_open_trans with (b := mk_exception a' e').
        { apply approx_star_exception; auto. }

        apply approx_implies_approx_open.
        apply computes_to_exception_implies_approx; auto; prove_isprogram.
        eapply eapply_red_sterm_exception_implies; eauto.

      - apply reduces_in_atmost_k_steps_eapply_sterm_to_isvalue_like in XX0; auto.
        repndors; exrepnd.

        + assert (reduces_in_atmost_k_steps lib arg2 (mk_nat n) (S i)) as ra2.
          { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
          apply no_change_after_value_ra with (k2:=k) in ra2; eauto 2 with slow; try omega;[].
          pose proof (Hi arg2 (mk_nat n) a0r) as z.
          make_red_val_like ra2 ca0.
          repeat (autodimp z hyp); eauto 2 with slow;[].
          apply approx_star_nat in z; auto.

          apply no_change_after_val_like with (k2:=k) in XX2; eauto 2 with slow; try omega;[].
          make_red_val_like XX2 caf.
          pose proof (Hi (f0 n) a (f' n)) as w.
          repeat (autodimp w hyp); eauto 2 with slow;[|].
          { apply alpha_implies_approx_star; eauto 3 with slow. }
          eapply approx_star_open_trans;[eauto|].

          apply approx_implies_approx_open.
          apply reduces_to_implies_approx_eauto; prove_isprogram.
          apply eapply_red_sterm_nat_implies; auto.

        + apply isexc_implies in XX2; auto; exrepnd; subst.
          assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
          { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
          apply no_change_after_val_like with (k2:=k) in ra2; try splr; try omega.
          make_red_val_like ra2 ca0.
          pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
          repeat (autodimp z hyp); eauto 2 with slow;[].
          apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_red_sterm_exception_implies; eauto.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    allrw @fold_exception.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := lar) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_eapply (mk_exception a' e') a0r).
    { apply reduces_to_prinarg; auto. }
    apply reduces_to_if_step; reflexivity.
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

Lemma extensional_fix {p} : extensional_op (@NCan p NFix).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  assert (m<= S k ) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_fix_implies; exrepnd; subst; cpx.

  dorn Hcv0.

  - unfold lblift_sub in Has; repnd; allsimpl; GC.
    repeat(approxrelbtd). show_hyps.
    apply approx_star_bterm_nobnd2 in Has0bt.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
    make_red_val_like Hcv3 h.

    apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { simpl in XX1; inversion XX1; subst; GC.
      apply (Hi _ _ f0) in h; auto.

      apply howe_lemma2 in h; exrepnd; auto.
      repnud h0.
      rename a into cc.
      apply reduces_to_prinarg with (lbt:= []) (op:=NFix) in h2.
      (* this will be used later in this proof *)
      assert (approx_star
                lib
                (mk_apply (oterm (Can c) bterms)
                          (oterm (NCan NFix) [bterm [] (oterm (Can c) bterms)]))
                (mk_apply (oterm (Can c) lbt')
                          (oterm (NCan NFix) [bterm [] (oterm (Can c) lbt')])))
        as XXX.
      { repeat (prove_approx_star; auto; prove_isprogram). }

      apply no_change_after_val_like with (k2:=k) in XX0; auto.
      make_red_val_like XX0 h.
      apply (Hi _ _ (mk_apply (oterm (Can c) lbt')
                              (oterm (NCan NFix) [bterm [] (oterm (Can c) lbt')])))
        in h; auto; prove_isprogram.

      match goal with
          [ H : approx_star ?lib ?cc ?t2 |- approx_star ?lib ?cc ?t1] =>
          apply (approx_star_open_trans lib) with (b:=t2) end; auto.

      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; try (rw <- @isprogram_fix_iff; auto).
      eapply reduces_to_if_split1; eauto.
    }

    { csunf XX1; allsimpl; ginv.
      apply (Hi _ _ f0) in h; auto.
      apply howe_lemma2_seq in h; exrepnd; auto.

      apply no_change_after_val_like with (k2:=k) in XX0; auto.
      make_red_val_like XX0 ca0.
      apply (Hi _ _ (mk_apply (mk_ntseq f') (oterm (NCan NFix) [bterm [] (sterm f')]))) in ca0;
        try prove_isprogram;
        [|apply isprogram_apply; eauto 2 with slow;
          apply isprogram_fix; eauto 2 with slow
         |repeat (prove_approx_star; eauto 2 with slow; prove_isprogram);
           try (apply alpha_implies_approx_star; eauto 3 with slow)];[].

      eapply approx_star_open_trans;[exact ca0|].
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; try (rw <- @isprogram_fix_iff; auto).
      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact h0|].
      eapply reduces_to_if_step.
      csunf; simpl; auto.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
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
    apply Hi with (v := f0) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e'); try (rw fold_fix).
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_fix (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.


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

Lemma extensional_cbv {p} : extensional_op (@NCan p NCbv).
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

  - unfold lblift_sub in Has; repnd; allsimpl; GC.
    repeat(approxrelbtd); show_hyps.
    allapply @approx_star_bterm_nobnd2.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto; [].
    make_red_val_like Hcv3 h.
    apply (Hi _ _ t2) in h; auto; prove_isprogram;[].
    applydup @howe_lemma2_implies_iscan in h; auto; exrepnd.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [t1]) (lnt2:= [v1])
      in Has1bt;
      eauto 2 with slow;
      try (complete (intro xx; ginv)).
    allunfold @apply_bterm; allsimpl; allrw @fold_subst; fold_terms.
    rw @compute_step_cbv_iscan in XX1; auto;[]; ginv.

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (subst b0 v0 v1)) in hh; auto; prove_isprogram;
    try (try (apply isprogram_subst_if_bt);
         try (apply isprogram_bt_implies);
         try (apply implies_isprogram_bt_lam);
         simpl; auto; prove_isprogram;
         introv i; repndors; subst; tcsp);[].
    allunfold @computes_to_value; repnd.

    eapply approx_star_open_trans;[eauto|].
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto;
      try (apply isprogram_cbv_iff2;dands;auto).
    eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|]; fold_terms.
    apply reduces_to_if_step.
    rw @compute_step_cbv_iscan; auto.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
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
    apply Hi with (v := t2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @fold_cbv.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_cbv (mk_exception a' e') v0 b0).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
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

Lemma extensional_trycatch {p} : extensional_op (@NCan p NTryCatch).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  repnud Hcv.
  assert (m <= S k) as XX by omega.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_trycatch_implies; exrepnd; subst; cpx.
  allrw @fold_try.
  unfold lblift_sub in Has; repnd; simpl in Has0, Has; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  dorn Hcv0.

  - apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    make_red_val_like Hcv3 h.
    apply (Hi _ _ t2) in h; auto.
    applydup @howe_lemma2_implies_iscan in h; auto; exrepnd.
    allunfold @computes_to_value; repnd.
    fold_terms.
    rw @compute_step_try_iscan in XX1; ginv.

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (mk_atom_eq a1 a1 v1 mk_bot)) in hh;
      auto; prove_isprogram;
      try (apply isprogram_mk_atom_eq; dands; auto);
      eauto 2 with slow;
      try (complete (apply approx_star_mk_atom_eq; auto;
                     apply approx_star_refl; eauto 3 with slow)).

    eapply approx_star_open_trans;[eauto|].
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto;
      try (apply isprogram_try_iff2;dands;auto);[].
    eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|]; fold_terms.
    apply reduces_to_if_step.
    rw @compute_step_try_iscan; auto.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    applydup @isprogram_exception_iff in Hcv8.
    csunf XX1; simpl in XX1; ginv.

    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    apply no_change_after_val_like with (k2:=k) in XX0; try splr.
    unfold extensional_op_ind in Hi.
    make_red_val_like Hcv3 h.
    apply Hi with (v := t2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.
    applydup @computes_to_exception_preserves_program in h1; auto.

    apply apply_bterm_approx_star_congr
    with (lnt1:=[e]) (lnt2:=[e']) in Has2bt;
      auto;
      try (complete (intro xx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].
    unfold apply_bterm in Has1bt; simpl in Has1bt; repeat (rw fold_subst in Has1bt).

    make_red_val_like XX0 hh.
    apply Hi with (v := mk_atom_eq a1 a' (subst b0 v0 e') (mk_exception a' e')) in hh; auto; prove_isprogram;
    try (apply isprogram_subst_if_bt; auto).

    {
      eapply approx_star_open_trans; eauto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram;
      try (apply isprogram_try_iff2; sp).
      apply (reduces_to_trans _ _ (mk_try (mk_exception a' e') a1 v0 b0)).
      * apply reduces_to_prinarg; auto.
      * apply reduces_to_if_step; csunf; simpl; boolvar; tcsp.
    }

    {
      apply isprogram_mk_atom_eq; dands; auto.
      apply isprogram_subst_if_bt; auto.
    }

    {
      apply isprogram_mk_atom_eq; dands; auto; prove_isprogram.
      - apply @preserve_program_exc2 in h1; sp.
      - apply isprogram_subst_if_bt; auto.
      - apply isprogram_exception; auto.
        apply @preserve_program_exc2 in h1; sp.
    }

    {
      apply approx_star_congruence3.
      - unfold approx_starbts, lblift_sub; allsimpl; dands; auto.
        introv i; repeat (destruct n; cpx); unfold selectbt; simpl;
        apply blift_sub_nobnd_congr; auto.
        apply approx_star_congruence3.
        + unfold approx_starbts, lblift_sub; allsimpl; dands; auto.
          introv j; repeat (destruct n; cpx); unfold selectbt; simpl;
          apply blift_sub_nobnd_congr; auto.
        + apply isprogram_exception; auto.
          apply @preserve_program_exc2 in h1; sp.
      - apply isprogram_mk_atom_eq; dands; auto; prove_isprogram.
        + apply @preserve_program_exc2 in h1; sp.
        + apply isprogram_subst_if_bt; auto.
        + apply isprogram_exception; auto.
          apply @preserve_program_exc2 in h1; sp.
    }
Qed.


Lemma extensional_spread {p} : extensional_op (@NCan p NSpread).
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
  allapply @isprogram_spread_implies; exrepnd; subst; cpx.
  allrw @fold_spread.

  unfold lblift_sub in Has; repnd; simpl in Has, Has0; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  allsimpl; GC.

  apply no_change_after_val_like with (k2:=k) in Hcv3;auto;[].
  make_red_val_like Hcv3 h.
  apply (Hi _ _ t2) in h; auto; prove_isprogram.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv;[].

    apply compute_step_spread_success in XX1; exrepnd; subst; cpx; GC.
    applydup @isprogram_pair_iff in Hcv8; repnd.
    apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd.
    repeat (destruct lbt'; simpl in h2; cpx); GC.
    repeat(approxrelbtd); show_hyps.
    applydup @computes_to_value_preserves_program in h0; auto.
    applydup @isprogram_pair_iff in h1; repnd.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [a0,b1]) (lnt2:= [a0r,b1r])
      in Has1bt;
      auto;
      try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (lsubst b0 [(v0,a0r),(v3,b1r)])) in hh; auto; prove_isprogram;
    try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
         introv i; repdors; cpx; auto).

    apply approx_star_open_trans with (b := lsubst b0 [(v0, a0r), (v3, b1r)]); auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_spread (mk_pair a0r b1r) v0 v3 b0).
    apply reduces_to_prinarg; auto; destruct h0; auto.
    apply reduces_to_if_step; reflexivity.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_spread (mk_exception a' e') v0 v3 b0).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

Lemma extensional_dsup {p} : extensional_op (@NCan p NDsup).
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
  allapply @isprogram_dsup_implies; exrepnd; subst; cpx.
  allrw @fold_spread.

  unfold lblift_sub in Has; repnd; simpl in Has, Has0; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  allsimpl; GC.

  apply no_change_after_val_like with (k2:=k) in Hcv3;auto;[].
  make_red_val_like Hcv3 h.
  apply (Hi _ _ t2) in h; auto; prove_isprogram.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv;[].

    apply compute_step_dsup_success in XX1; exrepnd; subst; cpx; GC.
    applydup @isprogram_sup_iff in Hcv8; repnd.

    apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd.
    repeat (destruct lbt'; simpl in h2; cpx); GC.
    repeat(approxrelbtd); show_hyps.
    applydup @computes_to_value_preserves_program in h0; auto.
    applydup @isprogram_sup_iff in h1; repnd.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [a0,b1]) (lnt2:= [a0r,b1r])
      in Has1bt;
      auto; try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (lsubst b0 [(v0,a0r),(v3,b1r)])) in hh; auto; prove_isprogram;
    try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
         introv i; repdors; cpx; auto).

    apply approx_star_open_trans with (b := lsubst b0 [(v0, a0r), (v3, b1r)]); auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_dsup (mk_sup a0r b1r) v0 v3 b0).
    apply reduces_to_prinarg; auto; destruct h0; auto.
    apply reduces_to_if_step; reflexivity.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_dsup (mk_exception a' e') v0 v3 b0).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

Lemma extensional_decide {p} : extensional_op (@NCan p NDecide).
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
  allapply @isprogram_decide_implies; exrepnd; subst; cpx.
  allrw @fold_decide.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply no_change_after_val_like with (k2:=k) in Hcv3;auto;[].
  make_red_val_like Hcv3 hh.
  apply (Hi _ _ t2) in hh; auto; prove_isprogram.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv;[].

    apply compute_step_decide_success in XX1; exrepnd; subst; cpx; GC.
    apply howe_lemma2 in hh; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in hh1; simpl in hh1; repnd; cpx.
    repeat(approxrelbtd); show_hyps.
    applydup @computes_to_value_preserves_program in hh0; auto.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [d]) (lnt2:= [dr])
      in Has1bt;
      auto; try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply apply_bterm_approx_star_congr
    with (lnt1:= [d]) (lnt2:= [dr])
      in Has2bt;
      auto; try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.

    destruct XX2 as [XX2|XX2]; repnd; subst.

    + applydup @isprogram_inl_iff in Hcv8; repnd.
      applydup @isprogram_inl_iff in hh1; repnd.

      apply (Hi _ _ (subst b0 v0 dr)) in hh; auto; prove_isprogram;
      try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
           introv i; repdors; cpx; auto).

      apply approx_star_open_trans with (b := subst b0 v0 dr); auto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_trans with (b := mk_decide (mk_inl dr) v0 b0 v3 b3).
      apply reduces_to_prinarg; auto; destruct hh0; auto.
      apply reduces_to_if_step; reflexivity.

    + applydup @isprogram_inr_iff in Hcv8; repnd.
      applydup @isprogram_inr_iff in hh1; repnd.

      apply (Hi _ _ (subst b3 v3 dr)) in hh; auto; prove_isprogram;
      try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
           introv i; repdors; cpx; auto).

      apply approx_star_open_trans with (b := subst b3 v3 dr); auto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_trans with (b := mk_decide (mk_inr dr) v0 b0 v3 b3).
      apply reduces_to_prinarg; auto; destruct hh0; auto.
      apply reduces_to_if_step; reflexivity.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in hh; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_decide (mk_exception a' e') v0 b0 v3 b3).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

Lemma extensional_arith {p} : forall a, extensional_op (@NCan p (NArithOp a)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_arithop_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_arithop_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_arith_implies in Hcv;
    [|eauto with slow|eauto with slow].

  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_value_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_value_in_max_k_steps in Hcv4; repnd.
    apply @no_change_after_value_ra with (k2:=k) in Hcv0; auto; try omega; [].
    apply @no_change_after_value_ra with (k2:=k) in Hcv5; auto; try omega; [].
    make_red_val_like Hcv0 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv5 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    apply howe_lemma2 in h2; auto; prove_isprogram.
    exrepnd.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd; cpx.
    unfold approx_starbts, lblift_sub in h2; simpl in h2; repnd; cpx.
    allrw @fold_integer.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                        [ bterm [] (mk_integer nv1),
                                          bterm [] (mk_integer nv2)]).
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_if_step; reflexivity.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduce_to_prinargs_arith; eauto 3 with slow.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
    try omega; try (complete (unfold isvalue_like; simpl; sp)).
    make_red_val_like Hcv3 h1.
    apply Hi with (v := a2) in h1; auto.
    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                        [ bterm [] (mk_exception a' e'),
                                          bterm [] b0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply isprogram_arithop_iff.
        eexists; eexists; dands; try reflexivity; auto;
        rw @isprogram_exception_iff; tcsp.
      }
      apply reduces_to_if_step; reflexivity.
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_value_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_exception_in_max_k_steps in Hcv4; repnd.
    applydup @reduces_atmost_preserves_program in Hcv2; auto.
    assert (@isvalue p (mk_integer z)) as isvx by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv2; auto; try omega; [].
    apply @no_change_after_val_like with (k2:=k) in Hcv4; auto; try omega;
    try (complete (unfold isvalue_like; simpl; sp)); [].
    make_red_val_like Hcv2 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv4 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2_exc in h2; auto; prove_isprogram; exrepnd.
    apply howe_lemma2 in h1; auto; prove_isprogram; exrepnd.
    applydup @computes_to_value_preserves_program in h4; auto.
    applydup @preserve_program_exc2 in h2; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                         [ bterm [] (oterm (Can (Nint z)) lbt'),
                                           bterm [] (mk_exception a' e')]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram;[|].
      { apply isprogram_arithop_iff; eexists; eexists; dands; try reflexivity; auto.
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto;[].
        allapply @isprogram_nat_implies; subst.
        allunfold @ca_wf; ginv.
      }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduce_to_prinargs_arith; auto.
      allapply @isprogram_nat_implies; subst.
      fold_terms; eauto 3 with slow.
    }
Qed.

Lemma extensional_ncomp {p} : forall a, extensional_op (@NCan p (NCompOp a)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_compop_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_compop_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_comp_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto)).
  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    applydup @reduces_atmost_preserves_program in Hcv6 as ispc1; auto.
    applydup @reduces_atmost_preserves_program in Hcv7 as ispc2; auto.
    assert (isvalue (pk2term pk1)) as isvc1 by (apply isvalue_iff; sp).
    assert (isvalue (pk2term pk2)) as isvc2 by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv6; auto; try omega; [].
    apply @no_change_after_value_ra with (k2:=k) in Hcv7; auto; try omega; [].
    applydup @reduces_atmost_preserves_program in Hcv6; auto.
    applydup @reduces_atmost_preserves_program in Hcv7; auto.
    make_red_val_like Hcv6 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv7 h2.
    apply Hi with (v := b0) in h2; auto.
    allrw @pk2term_eq.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    apply howe_lemma2 in h2; auto; prove_isprogram.
    allrw <- @pk2term_eq.
    exrepnd.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd; cpx.
    unfold approx_starbts, lblift_sub in h2; simpl in h2; repnd; cpx.

    unfold computes_to_val_like_in_max_k_steps in Hcv5; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv10; auto; try omega; [].
    make_red_val_like Hcv10 g.
    apply Hi with (v := if d1 then c0 else d0) in g; auto;
    try (complete (destruct d1; auto)).

    apply @approx_star_open_trans with (b := if d1 then c0 else d0); auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [nobnd (pk2term pk1),
                                         nobnd (pk2term pk2),
                                         nobnd c0,
                                         nobnd d0]).

    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_if_step.
      repndors; exrepnd; subst;
      try (complete (csunf; simpl; dcwf h; simpl; unfold compute_step_comp; simpl; boolvar; tcsp));
      try (complete (csunf; simpl; allrw @pk2term_eq; dcwf h; simpl;
                     unfold compute_step_comp; simpl; allrw @get_param_from_cop_pk2can;
                     boolvar; tcsp;
                     allunfold @co_wf; allsimpl; allrw @get_param_from_cop_pk2can; ginv)).
    }

    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      allrw <- @pk2term_eq.
      apply reduce_to_prinargs_comp; auto.
      { repndors; exrepnd; subst; simpl; eauto 3 with slow. }
      unfold computes_to_value in h0; sp.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
    try omega; try (unfold isvalue_like; allsimpl; sp).
    make_red_val_like Hcv3 h1.
    apply Hi with (v := a2) in h1; auto.
    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [ nobnd (mk_exception a' e'),
                                          nobnd b0,
                                          nobnd c0,
                                          nobnd d0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply isprogram_compop_iff.
        eexists; eexists; eexists; eexists; dands; try reflexivity; auto;
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step; reflexivity. }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_exception_in_max_k_steps in Hcv4; repnd.
    applydup @reduces_atmost_preserves_program in Hcv2 as ispx; auto.
    assert (isvalue (pk2term pk)) as isvx by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv2; auto; try omega; [].
    apply @no_change_after_val_like with (k2:=k) in Hcv5; auto; try omega;
    try (unfold isvalue_like; allsimpl; tcsp);[].
    make_red_val_like Hcv2 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv5 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2_exc in h2; auto; prove_isprogram; exrepnd.
    allrw @pk2term_eq.
    apply howe_lemma2 in h1; auto; prove_isprogram; exrepnd.
    applydup @computes_to_value_preserves_program in h4; auto.
    applydup @preserve_program_exc2 in h2; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [ nobnd (oterm (Can (pk2can pk)) lbt'),
                                          nobnd (mk_exception a' e'),
                                          nobnd c0,
                                          nobnd d0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram;[|].
      { apply isprogram_compop_iff; eexists; eexists; eexists; eexists; dands; try reflexivity; auto.
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto;[].
        allrw @isprogram_pk2can; subst; GC.
        repndors; exrepnd; subst;
        allunfold @co_wf; allrw @get_param_from_cop_pk2can; ginv.
      }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduce_to_prinargs_comp; auto.
      allrw @isprogram_pk2can; subst; GC.
      repndors; exrepnd; subst;
      allunfold @co_wf; allrw @get_param_from_cop_pk2can;
      allsimpl; ginv; fold_terms; allrw <- @pk2term_eq; eauto 3 with slow.
    }
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

Lemma extensional_cantest {p} : forall a, extensional_op (@NCan p (NCanTest a)).
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
  allapply @isprogram_cantest_implies; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply no_change_after_val_like with (k2:=k) in Hcv3; auto; [].
  make_red_val_like Hcv3 h1.
  apply (Hi _ _ a2) in h1; auto; prove_isprogram;[].

  extensional_ind XX0 k hh.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv.

    { apply (Hi _ _ (if canonical_form_test_for a c1 then b0 else c0)) in hh;
        auto; prove_isprogram;
        try (complete (destruct (canonical_form_test_for a c1); auto));
        eauto 2 with slow.
      apply howe_lemma2 in h1; exrepnd; auto; prove_isprogram.

      apply @approx_star_open_trans with (b := if canonical_form_test_for a c1 then b0 else c0); auto.
      apply approx_implies_approx_open.
      apply @approx_trans with (b := oterm (NCan (NCanTest a)) [nobnd (oterm (Can c1) lbt'),nobnd b0,nobnd c0]).
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_if_step; reflexivity.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg; auto; destruct h0; auto.
    }

    { apply howe_lemma2_seq in h1; exrepnd; auto.
      apply (Hi _ _ c0) in hh; auto.
      eapply approx_star_open_trans;[exact hh|clear hh].
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|].
      apply reduces_to_if_step.
      csunf; simpl; auto.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in h1; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := oterm (NCan (NCanTest a)) [nobnd (mk_exception a' e'),nobnd b0,nobnd c0]).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

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

Lemma extensional_sleep {p} : extensional_op (@NCan p NSleep).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_sleep_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_sleep_implies in Hprt'; exrepnd; subst; cpx.
  allrw @fold_sleep.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_sleep_implies in Hcv; exrepnd; cpx.
  unfold extensional_op_ind in Hi.
  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv2; auto.
  apply Hi with (v := t0) in Hcv2; auto; clear Hi.

  dorn Hcv1; exrepnd; subst.

  - apply howe_lemma2 in Hcv2; auto; prove_isprogram; exrepnd.
    unfold approx_starbts, lblift_sub in Hcv2; simpl in Hcv2; repnd; cpx.
    allrw @fold_integer.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_sleep (mk_integer z)).
    { apply reduces_to_prinarg; auto.
      destruct Hcv1; auto. }
    { apply reduces_to_if_step; reflexivity. }

  - apply isexc_implies in Hcv3; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in Hcv2; auto; exrepnd.
    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_sleep (mk_exception a' e')).
    { apply reduces_to_prinarg; auto. }
    { apply reduces_to_if_step; reflexivity. }
Qed.

Lemma extensional_tuni {p} : extensional_op (@NCan p NTUni).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_tuni_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_tuni_implies in Hprt'; exrepnd; subst; cpx.
  allrw @fold_tuni.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_tuni_implies in Hcv; exrepnd; cpx.
  unfold extensional_op_ind in Hi.
  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv2; auto.
  apply Hi with (v := t0) in Hcv2; auto; clear Hi.

  destruct Hcv1 as [Hcv1|Hcv1]; exrepnd; subst.

  - apply howe_lemma2 in Hcv2; auto; prove_isprogram; exrepnd.
    unfold approx_starbts, lblift_sub in Hcv2; simpl in Hcv2; repnd; cpx.
    allrw @fold_integer.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_tuni (mk_integer (Z.of_nat n))).
    apply reduces_to_prinarg; auto.
    destruct Hcv1; auto.
    apply reduces_to_if_step.
    csunf; simpl.
    unfold compute_step_tuni; simpl.
    destruct (Z_le_gt_dec 0 (Z.of_nat n)); try omega.
    rw Znat.Nat2Z.id; sp.

  - apply isexc_implies in Hcv3; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in Hcv2; auto; exrepnd.
    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_tuni (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

Lemma extensional_minus {p} : extensional_op (@NCan p NMinus).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_minus_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_minus_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  fold_terms.
  allrw @fold_minus.

  apply computes_to_val_like_in_max_k_steps_minus_implies in Hcv; exrepnd; cpx.
  unfold extensional_op_ind in Hi.
  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv2; auto.
  apply Hi with (v := t0) in Hcv2; auto; clear Hi.

  destruct Hcv1 as [Hcv1|Hcv1]; exrepnd; subst.

  - apply howe_lemma2 in Hcv2; auto; prove_isprogram; exrepnd.
    unfold approx_starbts, lblift_sub in Hcv2; simpl in Hcv2; repnd; cpx.
    allrw @fold_integer.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_minus (mk_integer z)).
    apply reduces_to_prinarg; auto.
    destruct Hcv1; auto.
    apply reduces_to_if_step.
    simpl.
    unfold compute_step_minus; simpl; auto.

  - apply isexc_implies in Hcv3; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in Hcv2; auto; exrepnd.
    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_minus (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.

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



(* ====================================== *)



Definition approx_star_sk {o} lib op (sk1 sk2 : @sosub_kind o) :=
  approx_star_bterm lib op (sk2bterm sk1) (sk2bterm sk2).

Lemma approx_star_sk_if_approx_star_sosub_find {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk1
    -> sosub_find (combine vs sks2) sv = Some sk2
    -> approx_star_sk lib op sk1 sk2.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1, sks2; allsimpl; cpx.
  apply binrel_list_cons in aeq; repnd.
  destruct s, s0; boolvar; cpx.

  - provefalse.
    unfold approx_star_sk in aeq; simpl in aeq.
    inversion aeq as [nvs h]; exrepnd.
    inversion h1; inversion h2; subst.
    destruct n1; f_equal; omega.

  - provefalse.
    unfold approx_star_sk in aeq; simpl in aeq.
    inversion aeq as [nvs h]; exrepnd.
    inversion h1; inversion h2; subst.
    destruct n1; f_equal; omega.

  - apply (IHvs sks1 sks2 sk1 sk2 sv); auto.
Qed.

Lemma approx_star_sk_is_approx_star_bterm {o} :
  forall lib op (b1 b2 : @BTerm o),
    approx_star_bterm lib op b1 b2
    <=> approx_star_sk lib op (bterm2sk b1) (bterm2sk b2).
Proof.
  introv.
  unfold approx_star_sk; simpl.
  destruct b1, b2; simpl; sp.
Qed.

Lemma false_if_approx_star_sk_sosub_find {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk
    -> sosub_find (combine vs sks2) sv = None
    -> False.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  destruct s, s0; boolvar; cpx;
  apply binrel_list_cons in aeq; repnd.

  - unfold approx_star_sk in aeq; simpl in aeq;
    inversion aeq as [nvs h]; exrepnd;
    inversion h1; inversion h2; subst;
    destruct n1; f_equal; try omega.

  - eapply IHvs in f1; eauto.
Qed.

Lemma false_if_approx_star_sk_sosub_find2 {o} :
  forall lib op (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> sosub_find (combine vs sks1) sv = None
    -> sosub_find (combine vs sks2) sv = Some sk
    -> False.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  destruct s, s0; boolvar; cpx;
  apply binrel_list_cons in aeq; repnd.

  - unfold approx_star_sk in aeq; simpl in aeq;
    inversion aeq as [nvs h]; exrepnd;
    inversion h1; inversion h2; subst;
    destruct n1; f_equal; try omega.

  - eapply IHvs in f1; eauto.
Qed.

Lemma approx_star_apply_list {o} :
  forall lib ts1 ts2 (t1 t2 : @NTerm o),
    approx_star lib t1 t2
    -> bin_rel_nterm (approx_star lib) ts1 ts2
    -> approx_star lib (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; introv ap brel; destruct ts2; allsimpl; tcsp.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - apply binrel_list_cons in brel; repnd.
    apply IHts1; auto.
    apply approx_star_congruence; auto.
    unfold approx_starbts, lblift_sub; simpl; dands; auto.
    introv k.
    destruct n0.
    + unfold selectbt; simpl; auto.
      apply blift_sub_nobnd_congr; auto.
    + destruct n0; try omega.
      unfold selectbt; simpl; auto.
      apply blift_sub_nobnd_congr; auto.
Qed.

Lemma sosub_filter_if_approx_star_sk {o} :
  forall lib op vs (sks1 sks2 : list (@sosub_kind o)) (l : list sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk (approx_star_sk lib op) sks1 sks2
    -> {vs' : list NVar
        & {sks1' : list sosub_kind
        & {sks2' : list sosub_kind
           & sosub_filter (combine vs sks1) l = combine vs' sks1'
           # sosub_filter (combine vs sks2) l = combine vs' sks2'
           # bin_rel_sk (approx_star_sk lib op) sks1' sks2'
           # subset (combine sks1' sks2') (combine sks1 sks2)
           # subset vs' vs
           # subset sks1' sks1
           # subset sks2' sks2
           # length vs' = length sks1'
           # length vs' = length sks2'
           # sodom (combine vs' sks1') = remove_so_vars l (sodom (combine vs sks1))
           # sodom (combine vs' sks2') = remove_so_vars l (sodom (combine vs sks2)) }}}.
Proof.
  induction vs; destruct sks1, sks2; introv len1 len2 ap; allsimpl; cpx.
  - exists ([] : list NVar) ([] : list (@sosub_kind o)) ([] : list (@sosub_kind o));
      sp; rw remove_so_vars_nil_r; rw combine_nil; sp.
  - destruct s, s0; boolvar; tcsp.

    + apply binrel_list_cons in ap; repnd.
      pose proof (IHvs sks1 sks2 l len1 len2 ap0) as h; exrepd.
      exists vs' sks1' sks2'; dands; auto;
      try (complete (apply subset_cons1; auto));
      try (complete (rw remove_so_vars_cons_r; boolvar; tcsp)).

    + provefalse.
      apply binrel_list_cons in ap; repnd.
      inversion ap as [nvs h]; exrepnd; allsimpl.
      inversion h1; subst.
      inversion h2; subst.
      assert (length l1 = length l0) as x by omega.
      rw x in n1; sp.

    + provefalse.
      apply binrel_list_cons in ap; repnd.
      inversion ap as [nvs h]; exrepnd; allsimpl.
      inversion h1; subst.
      inversion h2; subst.
      assert (length l1 = length l0) as x by omega.
      rw x in l2; sp.

    + apply binrel_list_cons in ap; repnd.
      pose proof (IHvs sks1 sks2 l len1 len2 ap0) as h; exrepd.
      exists (a :: vs') (sosk l0 n :: sks1') (sosk l1 n0 :: sks2');
        simpl; dands; tcsp;
        try (complete (apply eq_cons; auto));
        try (complete (apply subset_cons2; auto));
        try (complete (rw remove_so_vars_cons_r; boolvar; tcsp; apply eq_cons; auto)).
      apply binrel_list_cons; sp.
Qed.

(*
Lemma sosub_aux_approx_star_congr {p} :
  forall lib opr (t : @SOTerm p) (vs : list NVar) (ts1 ts2 : list sosub_kind),
    let sub1 := combine vs ts1 in
    let sub2 := combine vs ts2 in
    wf_soterm t
    -> length vs = length ts1
    -> length vs = length ts2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t)
    (* These 2 disjoints we can always assume because they are ensured by sosub *)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> bin_rel_sk (approx_star_sk lib opr) ts1 ts2
    -> approx_star lib (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind1s t as [v ts ind|op lbt ind] Case; simpl;
  introv wf len1 len2 d1 d2 d3 d4 cov1 cov2 ask.

  - Case "sovar".
    remember (sosub_find (combine vs ts1) (v, length ts)) as o;
      destruct o; symmetry in Heqo;
      remember (sosub_find (combine vs ts2) (v, length ts)) as q;
      destruct q; symmetry in Heqq;
      try (destruct s); try (destruct s0).

    + pose proof (apply_bterm_approx_star_congr
                    lib opr (bterm l n) (bterm l0 n0)
                    (map (sosub_aux (combine vs ts1)) ts)
                    (map (sosub_aux (combine vs ts2)) ts)
                 ) as h.
      repeat (autodimp h hyp).

      * apply approx_star_sk_is_approx_star_bterm; simpl.
        eapply approx_star_sk_if_approx_star_sosub_find;
          [|idtac|exact ask|exact Heqo|exact Heqq]; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux (combine vs ts1) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux (combine vs ts2) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n1 ts default_soterm) as t.
        pose proof (nth_in _ n1 ts default_soterm i) as j.
        rw <- Heqt in j; clear Heqt.

        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub (combine vs ts1))
                         (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub (combine vs ts2))
                         (flat_map fovars ts))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        apply ind; auto.

        { rw disjoint_flat_map_r in d1; apply d1; auto. }

        { rw disjoint_flat_map_r in d2; apply d2; auto. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

      * allrw map_length; unfold num_bvars; simpl; auto.
        allapply @sosub_find_some; sp.

      * allrw map_length; unfold num_bvars; simpl; auto.

      * unfold apply_bterm in h; simpl in h.
        applydup @sosub_find_some in Heqo; repnd.
        applydup @sosub_find_some in Heqq; repnd.
        allrw @cover_so_vars_sovar; repnd.
        revert h.
        change_to_lsubst_aux4; auto; clear h;
        try (complete (allrw disjoint_cons_r; repnd;
                       rw flat_map_map; unfold compose;
                       eapply disjoint_bound_vars_prop3; eauto)).

    + eapply false_if_approx_star_sk_sosub_find in Heqo; eauto; sp.

    + eapply false_if_approx_star_sk_sosub_find2 in Heqo; eauto; sp.

    + apply approx_star_apply_list; auto.

      * apply approx_star_refl; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux (combine vs ts1) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux (combine vs ts2) default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n ts default_soterm) as t.
        pose proof (nth_in _ n ts default_soterm i) as j.
        rw <- Heqt in j; clear Heqt.

        rw disjoint_flat_map_r in d1.
        rw disjoint_flat_map_r in d2.
        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub (combine vs ts1))
                         (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub (combine vs ts2))
                         (flat_map fovars ts))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        apply ind; auto.

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

  - Case "soterm".
    allrw @wf_soterm_iff; repnd.

    apply approx_star_congruence;
      [|rw map_map; unfold compose; rw <- wf0;
        apply eq_maps; introv k; destruct x;
        unfold num_bvars; simpl; auto].

    unfold approx_starbts, lblift; allrw map_length; dands; auto.
    introv i.
    unfold selectbt.

    assert (@default_bt p = sosub_b_aux (combine vs ts1) default_sobterm)
      as e by auto.
    rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_bt p).
    assert (@default_bt p = sosub_b_aux (combine vs ts2) default_sobterm)
      as e by auto.
    rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_bt p).
    remember (nth n lbt default_sobterm) as bt.
    pose proof (nth_in _ n lbt default_sobterm i) as j.
    rw <- Heqbt in j; clear Heqbt.

    rw disjoint_flat_map_r in d1.
    rw disjoint_flat_map_r in d2.
    allrw disjoint_app_r; repnd.

    destruct bt; simpl.

    pose proof (sosub_filter_if_approx_star_sk lib vs ts1 ts2 (vars2sovars l)) as h.
    repeat (autodimp h hyp); exrepnd.

    rw h1; rw h2.

    unfold blift.
    exists l (sosub_aux (combine vs' sks1') s) (sosub_aux (combine vs' sks2') s).
    dands; auto.
    eapply ind; eauto.

    + applydup d1 in j as k; simpl in k.
      rw disjoint_app_r in k; repnd.
      rw @free_vars_sosub_combine; auto.
      rw @free_vars_sosub_combine in k; auto.
      rw disjoint_flat_map_l; introv z.
      rw disjoint_flat_map_l in k.
      apply h6 in z.
      applydup k in z; auto.

    + applydup d2 in j as k; simpl in k.
      rw disjoint_app_r in k; repnd.
      rw @free_vars_sosub_combine; auto.
      rw @free_vars_sosub_combine in k; auto.
      rw disjoint_flat_map_l; introv z.
      rw disjoint_flat_map_l in k.
      apply h7 in z.
      applydup k in z; auto.

    + rw disjoint_app_r; dands.

      * rw @bound_vars_sosub_combine; auto.
        rw @free_vars_sosub_combine; auto.
        rw @bound_vars_sosub_combine in d0; auto.
        rw @free_vars_sosub_combine in d0; auto.
        rw disjoint_flat_map_r; introv z.
        rw disjoint_flat_map_l; introv y.
        rw disjoint_flat_map_r in d0.
        applydup h6 in z.
        apply d0 in z0.
        rw disjoint_flat_map_l in z0.
        applydup h6 in y.
        apply z0 in y0; auto.

      * rw @bound_vars_sosub_combine; auto.
        rw disjoint_flat_map_r in d3.
        apply d3 in j; simpl in j; rw disjoint_app_r in j; repnd.
        rw @bound_vars_sosub_combine in j; auto.
        rw disjoint_flat_map_l in j.
        rw disjoint_flat_map_l; introv z.
        apply h6 in z.
        apply j in z; auto.

    + rw disjoint_app_r; dands.

      * rw @bound_vars_sosub_combine; auto.
        rw @free_vars_sosub_combine; auto.
        rw @bound_vars_sosub_combine in d5; auto.
        rw @free_vars_sosub_combine in d5; auto.
        rw disjoint_flat_map_r; introv z.
        rw disjoint_flat_map_l; introv y.
        rw disjoint_flat_map_r in d5.
        applydup h7 in z.
        apply d5 in z0.
        rw disjoint_flat_map_l in z0.
        applydup h7 in y.
        apply z0 in y0; auto.

      * rw @bound_vars_sosub_combine; auto.
        rw disjoint_flat_map_r in d4.
        apply d4 in j; simpl in j; rw disjoint_app_r in j; repnd.
        rw @bound_vars_sosub_combine in j; auto.
        rw disjoint_flat_map_l in j.
        rw disjoint_flat_map_l; introv z.
        apply h7 in z.
        apply j in z; auto.

    + unfold cover_so_vars.
      rw h10.
      rw filter_out_fo_vars_remove_fo_vars; auto.
      rw @cover_so_vars_soterm in cov1; eapply cov1; eauto.

    + unfold cover_so_vars.
      rw h0.
      rw filter_out_fo_vars_remove_fo_vars; auto.
      rw @cover_so_vars_soterm in cov2; eapply cov2; eauto.
Qed.
*)

Definition approx_star_sosub {o} lib op (sub1 sub2 : @SOSub o) :=
  bin_rel_sk (approx_star_sk lib op) (so_range sub1) (so_range sub2).

Lemma approx_star_sosub_implies_same_length {o} :
  forall lib op (sub1 sub2 : @SOSub o),
    approx_star_sosub lib op sub1 sub2 -> length sub1 = length sub2.
Proof.
  introv ap.
  unfold approx_star_sosub, bin_rel_sk, binrel_list in ap; repnd.
  allrw @length_so_range; auto.
Qed.

(*
Lemma sosub_aux_approx_star_congr2 {o} :
  forall lib (t : @SOTerm o) (sub1 sub2 : @SOSub o),
    wf_soterm t
    -> sodom sub1 = sodom sub2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> approx_star_sosub lib sub1 sub2
    -> approx_star lib (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  introv wf e disj1 disj2 disj3 disj4 cov1 cov2 ap.
  pose proof (sosub_aux_approx_star_congr
                lib t
                (so_dom sub1) (so_range sub1) (so_range sub2)) as h.

  allrw <- @sosub_as_combine; allsimpl.
  applydup @eq_sodoms_implies_eq_so_doms in e as e'.

  repeat (autodimp h hyp).
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw e'; rw @length_so_dom; rw @length_so_range; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e'; rw <- @sosub_as_combine; auto.
  - rw e' in h; rw <- @sosub_as_combine in h; auto.
Qed.
*)

Lemma alphaeq_sosub_kind_if_alphaeq_sosub_find2 {o} :
  forall (sub1 sub2 : @SOSub o) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    alphaeq_sosub sub1 sub2
    -> sosub_find sub1 sv = Some sk1
    -> sosub_find sub2 sv = Some sk2
    -> alphaeq_sk sk1 sk2.
Proof.
  introv aeq f1 f2.
  applydup @alphaeq_sosub_implies_eq_sodoms in aeq as eqdoms.
  applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
  apply (alphaeq_sosub_kind_if_alphaeq_sosub_find
           (so_dom sub1) (so_range sub1) (so_range sub2) _ _ sv); auto.
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw eqdoms'; rw @length_so_dom; rw @length_so_range; auto.
  - apply alphaeq_sosub_implies_alphaeq_sk; auto.
  - rw <- @sosub_as_combine; auto.
  - rw eqdoms'; rw <- @sosub_as_combine; auto.
Qed.

Lemma approx_star_sk_if_approx_star_sosub_find2 {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = Some sk1
    -> sosub_find sub2 sv = Some sk2
    -> approx_star_sk lib op sk1 sk2.
Proof.
  introv e ap f1 f2.
  applydup @approx_star_sosub_implies_same_length in ap.
  apply (approx_star_sk_if_approx_star_sosub_find
           lib op (so_dom sub1) (so_range sub1) (so_range sub2) _ _ sv); auto.

  - rw @length_so_dom; rw @length_so_range; auto.
  - rw @length_so_dom; rw @length_so_range; auto.
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma false_if_approx_star_sosub_find {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = Some sk
    -> sosub_find sub2 sv = None
    -> False.
Proof.
  introv e ap f1 f2.
  pose proof (false_if_approx_star_sk_sosub_find
                lib op (so_dom sub1) (so_range sub1) (so_range sub2)
                sk sv) as h.
  allrw @length_so_dom.
  allrw @length_so_range.
  applydup @approx_star_sosub_implies_same_length in ap.
  repeat (autodimp h hyp).
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma false_if_approx_star_sosub_find2 {o} :
  forall lib op (sub1 sub2 : @SOSub o) (sk : sosub_kind) (sv : sovar_sig),
    so_dom sub1 = so_dom sub2
    -> approx_star_sosub lib op sub1 sub2
    -> sosub_find sub1 sv = None
    -> sosub_find sub2 sv = Some sk
    -> False.
Proof.
  introv e ap f1 f2.
  pose proof (false_if_approx_star_sk_sosub_find2
                lib op (so_dom sub1) (so_range sub1) (so_range sub2)
                sk sv) as h.
  allrw @length_so_dom.
  allrw @length_so_range.
  applydup @approx_star_sosub_implies_same_length in ap.
  repeat (autodimp h hyp).
  - rw <- @sosub_as_combine; auto.
  - rw e; rw <- @sosub_as_combine; auto.
Qed.

Lemma eq_maps_combine :
  forall (A B C : tuniv)
         (f : A -> B) (g : C -> B)
         (la : list A) (lc : list C),
    length la = length lc
    -> (forall a c, LIn (a,c) (combine la lc) -> f a = g c)
    -> map f la = map g lc.
Proof.
  induction la; destruct lc; introv len imp; allsimpl; auto; cpx.
  f_equal; sp.
Qed.

Lemma num_bvars_sosub_b_aux {o} :
  forall (b : @SOBTerm o) sub,
    num_bvars (sosub_b_aux sub b) = num_sobvars b.
Proof.
  introv.
  destruct b; simpl; unfold num_bvars; simpl; auto.
Qed.

Lemma so_alphaeq_vs_implies_eq_num_sobvars {o} :
  forall (a b : @SOBTerm o) vs,
    so_alphaeqbt_vs vs a b
    -> num_sobvars a = num_sobvars b.
Proof.
  introv aeq; inversion aeq; subst; simpl; omega.
Qed.

Lemma approx_starbts_map {o} :
  forall lib A op (l1 l2 : list A) (f1 f2 : A -> @BTerm o),
    length l1 = length l2
    -> (forall a1 a2,
          LIn (a1,a2) (combine l1 l2)
          -> approx_star_bterm lib op (f1 a1) (f2 a2))
    -> approx_starbts lib op (map f1 l1) (map f2 l2).
Proof.
  induction l1; destruct l2; introv len imp; allsimpl; auto; cpx.
  - unfold approx_starbts, lblift_sub; simpl; sp.
  - rw @approx_starbts_cons; dands; auto.
Qed.

Lemma filter_out_fo_vars_swap_fo_vars :
  forall vs1 vs2 vs,
    filter_out_fo_vars (swap_fo_vars (mk_swapping vs1 vs2) vs)
    = filter_out_fo_vars vs.
Proof.
  induction vs; introv; simpl; auto.
  destruct a; destruct n0; simpl; auto.
  f_equal; auto.
Qed.

Lemma cover_so_vars_so_swap {o} :
  forall (t : @SOTerm o) sub vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> (cover_so_vars (so_swap (mk_swapping vs1 vs2) t) sub
        <=> cover_so_vars t sub).
Proof.
  introv norep disj.
  unfold cover_so_vars.
  rw @so_free_vars_so_swap; auto.
  rw filter_out_fo_vars_swap_fo_vars; sp.
Qed.

Lemma cover_so_vars_sosub_filter_vars2sovars {o} :
  forall (t : @SOTerm o) sub vs,
    cover_so_vars t (sosub_filter sub (vars2sovars vs))
    <=> cover_so_vars t sub.
Proof.
  introv.
  unfold cover_so_vars.
  rw @sodom_sosub_filter.
  rw filter_out_fo_vars_remove_fo_vars; sp.
Qed.

Lemma sosub_filter_if_not_in_dom {o} :
  forall t (sub : @SOSub o) vs,
    disjoint (sodom sub) vs
    -> sosub_aux (sosub_filter sub vs) t = sosub_aux sub t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv disj; allsimpl; auto.

  - Case "sovar".
    destruct (in_deq sovar_sig sovar_sig_dec (v,length ts) vs) as [i|i].

    + rw disjoint_sym in disj; applydup disj in i.
      remember (sosub_find (sosub_filter sub vs) (v,length ts)) as f1.
      remember (sosub_find sub (v,length ts)) as f2.
      symmetry in Heqf1; symmetry in Heqf2.
      destruct f1; destruct f2.

      * destruct s0.
        apply sosub_find_some in Heqf2; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf2 in Heqf0; sp.

      * destruct s.
        apply sosub_find_some in Heqf1; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf1 in Heqf0.
        rw @sodom_sosub_filter in Heqf0.
        rw in_remove_so_vars in Heqf0; sp.

      * destruct s.
        apply sosub_find_some in Heqf2; repnd.
        eapply in_sodom_if in Heqf0; eauto.
        rw Heqf2 in Heqf0; sp.

      * f_equal.
        apply eq_maps; introv k.
        apply ind; auto.
        rw disjoint_sym; auto.

    + rw @sosub_find_sosub_filter; auto.
      remember (sosub_find sub (v,length ts)) as f; symmetry in Heqf; destruct f.

      * destruct s.
        f_equal; f_equal.
        apply eq_maps; introv k.
        apply ind; auto.

      * f_equal.
        apply eq_maps; introv k.
        apply ind; auto.

  - Case "soterm".
    f_equal.
    apply eq_maps; introv i; destruct x as [l t]; simpl.
    f_equal.
    rw @sosub_filter_swap.
    eapply ind; eauto.
    rw @sodom_sosub_filter.
    introv a b.
    rw disjoint_sym in disj; apply disj in b.
    allrw in_remove_so_vars; sp.
Qed.

Lemma if_disjoint_sovars2vars :
  forall vs1 vs2,
    disjoint (sovars2vars vs1) (sovars2vars vs2)
    -> disjoint vs1 vs2.
Proof.
  introv disj a b.
  destruct t.
  assert (LIn n (sovars2vars vs1)) as h by (apply in_sovars2vars; eexists; eauto).
  apply disj in h.
  rw in_sovars2vars in h.
  destruct h; eexists; eauto.
Qed.

Lemma sovars2vars_vars2sovars :
  forall vs, sovars2vars (vars2sovars vs) = vs.
Proof.
  induction vs; simpl; allrw; sp.
Qed.

Lemma sovars2vars_sodom_is_so_dom {o} :
  forall (sub : @SOSub o), sovars2vars (sodom sub) = so_dom sub.
Proof.
  induction sub; simpl; auto.
  destruct a; destruct s; simpl; allrw; sp.
Qed.

Lemma in_0_vars2sovars :
  forall v vs, LIn (v, 0) (vars2sovars vs) <=> LIn v vs.
Proof.
  introv; rw in_map_iff; split; intro k; exrepnd; allunfold var2sovar; cpx.
  eexists; eauto.
Qed.

Lemma implies_disjoint_allvars {o} :
  forall (t : @NTerm o) vs,
    disjoint (free_vars t) vs
    -> disjoint (bound_vars t) vs
    -> disjoint (allvars t) vs.
Proof.
  introv d1 d2.
  apply disjoint_sym; apply disjoint_to_allvars_r.
  rw disjoint_app_r; dands; apply disjoint_sym; auto.
Qed.

Lemma sosub_filter_r {o} :
  forall (sub : @SOSub o) l1 l2,
    sosub_filter (sosub_filter sub l1) l2
    = sosub_filter sub (l1 ++ l2).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; simpl; boolvar; allrw in_app_iff; tcsp;
  allrw not_over_or; repnd; tcsp; allsimpl; boolvar; tcsp.
  rw IHsub; auto.
Qed.

Lemma vars2sovars_app :
  forall vs1 vs2,
    vars2sovars (vs1 ++ vs2) = vars2sovars vs1 ++ vars2sovars vs2.
Proof.
  introv; unfold vars2sovars; rw map_app; auto.
Qed.

Lemma sosub_aux_sosub_filter_so_swap {o} :
  forall (t : @SOTerm o) sub vs1 vs2 vs,
    disjoint vs1 (free_vars_sosub sub)
    -> disjoint vs1 (bound_vars_sosub sub)
    -> disjoint vs2 (free_vars_sosub sub)
    -> disjoint vs2 (bound_vars_sosub sub)
    -> disjoint vs2 (all_fo_vars t)
    -> disjoint vs1 vs2
    -> disjoint vs vs2
    -> no_repeats vs2
    -> cover_so_vars t sub
    -> subvars vs1 vs
    -> length vs1 = length vs2
    -> sosub_aux (sosub_filter sub (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs)))
                 (so_swap (mk_swapping vs1 vs2) t)
       = cswap (mk_swapping vs1 vs2)
               (sosub_aux (sosub_filter sub (vars2sovars vs)) t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  introv norep cov sv len; allsimpl; auto.

  - Case "sovar".
    destruct (in_deq sovar_sig sovar_sig_dec (v,length ts) (vars2sovars vs)) as [i|i].

    + rw in_map_iff in i; exrepnd; destruct a; allsimpl; allunfold var2sovar; cpx.
      destruct ts; allsimpl; cpx; GC; boolvar; cpx; GC; allsimpl.
      allrw disjoint_singleton_r.

      remember (sosub_find (sosub_filter sub (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs)))
                           (swapvar (mk_swapping vs1 vs2) (nvar n), 0)) as f1.
      symmetry in Heqf1; destruct f1.

      * destruct s; apply sosub_find_some in Heqf1; repnd.
        destruct l; allsimpl; cpx; GC.
        apply in_sosub_filter in Heqf0; repnd; allsimpl.
        destruct Heqf0.
        rw in_map_iff; unfold var2sovar.
        exists (swapvar (mk_swapping vs1 vs2) (nvar n)); dands; auto.
        apply in_swapbvars; eexists; eauto.

      * remember (sosub_find (sosub_filter sub (vars2sovars vs))
                             (nvar n, 0)) as f2.
        symmetry in Heqf2; destruct f2; simpl; auto.

        destruct s; apply sosub_find_some in Heqf2; repnd.
        destruct l; allsimpl; cpx; GC.
        apply in_sosub_filter in Heqf0; allsimpl; repnd.
        destruct Heqf0.
        rw in_map_iff; unfold var2sovar.
        exists (nvar n); sp.

    + rw @sosub_find_sosub_filter; auto.
      allrw @cover_so_vars_sovar; repnd.
      allrw disjoint_cons_r; repnd.

      boolvar.

      * destruct ts; allsimpl; cpx; GC.
        allrw in_0_vars2sovars.
        rw @sosub_find_sosub_filter;
          [|rw in_0_vars2sovars;auto; rw in_swapbvars; intro k; exrepnd;
            apply swapvars_eq in k0; subst; complete sp].

        destruct (in_deq NVar deq_nvar v vs1) as [j|j];
          [rw subvars_prop in sv; apply sv in j; complete sp|].
        rw swapvar_not_in;auto.

        remember (sosub_find sub (v,0)) as f;
          symmetry in Heqf; destruct f; allsimpl; auto.

        { destruct s; simpl.
          apply sosub_find_some in Heqf; repnd.
          destruct l; allsimpl; cpx; GC.
          allrw @lsubst_aux_nil.
          rw disjoint_flat_map_r in disj1; applydup disj1 in Heqf0 as h1.
          rw disjoint_flat_map_r in disj3; applydup disj3 in Heqf0 as h2.
          rw disjoint_flat_map_r in disj2; applydup disj2 in Heqf0 as h3.
          rw disjoint_flat_map_r in disj4; applydup disj4 in Heqf0 as h4.
          allsimpl.
          allrw remove_nvars_nil_l.
          rw @cswap_trivial; auto; apply implies_disjoint_allvars; eauto with slow. }

        { rw swapvar_not_in; auto. }

      * autodimp cov0 hyp;[destruct ts; allsimpl; complete cpx|].
        simpl; rw map_length.

        rw @sosub_find_sosub_filter;
          [|intro k; rw in_map_iff in k; exrepnd; allunfold var2sovar; cpx;
            destruct ts; allsimpl; complete cpx].

        remember (sosub_find sub (v, length ts)) as f;
          symmetry in Heqf; destruct f;[|apply sosub_find_none in Heqf; complete sp].
        destruct s; simpl.
        allrw map_map; unfold compose.
        rw @lsubst_aux_cswap_cswap; auto.
        applydup @sosub_find_some in Heqf; repnd.

        dup disj1 as d1; dup disj2 as d2; dup disj3 as d3; dup disj4 as d4.
        rw disjoint_flat_map_r in disj1.
        rw disjoint_flat_map_r in disj2.
        rw disjoint_flat_map_r in disj3.
        rw disjoint_flat_map_r in disj4.
        applydup disj1 in Heqf1 as h1.
        applydup disj2 in Heqf1 as h2.
        applydup disj3 in Heqf1 as h3.
        applydup disj4 in Heqf1 as h4.
        allsimpl.
        allrw disjoint_app_r; repnd.

        assert (disjoint vs1 (free_vars n0))
          as k1 by (introv a b; applydup h0 in a; applydup h1 in a;
                    allrw in_remove_nvars; sp).

        assert (disjoint vs2 (free_vars n0))
          as k2 by (introv a b; applydup h5 in a; applydup h3 in a;
                    allrw in_remove_nvars; sp).

        rw @cswap_trivial;
          try (complete (apply implies_disjoint_allvars; eauto with slow));[].

        rw @cswap_sub_combine.
        rw (swapbvars_trivial vs1 vs2 l); eauto with slow;[].

        f_equal; f_equal.
        allrw map_map; unfold compose.
        apply eq_maps; introv j.
        apply ind; auto.

        rw disjoint_flat_map_r in disj0; apply disj0; sp.

  - Case "soterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t].
    simpl.
    f_equal.
    allrw @sosub_filter_r.
    allrw <- vars2sovars_app.
    allrw <- swapbvars_app.

    rw disjoint_flat_map_r in disj5.
    applydup disj5 in i as j; simpl in j; rw disjoint_app_r in j; repnd.

    allrw @cover_so_vars_soterm.
    applydup cov in i as c.

    eapply ind; eauto.

    + rw disjoint_app_l; dands; eauto with slow.

    + apply subvars_app_weak_l; auto.
Qed.

Lemma subvars_swpbvars :
  forall vs vs1 vs2,
    subvars vs vs1
    -> disjoint vs1 vs2
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> subvars (swapbvars (mk_swapping vs1 vs2) vs) vs2.
Proof.
  introv sv disj norep len.
  rw subvars_prop; introv i.
  rw in_swapbvars in i; exrepnd; subst.
  apply swapvar_implies3; auto.
  rw subvars_prop in sv; apply sv; auto.
Qed.

Lemma btchange_alpha_cswap {o} :
  forall (t : @NTerm o) l1 l2,
    length l1 = length l2
    -> no_repeats l2
    -> disjoint l2 (allvars t)
    -> disjoint l1 l2
    -> alpha_eq_bterm (bterm l1 t) (bterm l2 (cswap (mk_swapping l1 l2) t)).
Proof.
  introv len norep disj1 disj2.
  apply alphaeqbt_eq.
  pose proof (fresh_vars
                (length l1)
                (l1 ++ l2 ++ allvars t ++ allvars (cswap (mk_swapping l1 l2) t)))
    as fv; exrepnd.

  apply (aeqbt [] lvn); auto; try omega.

  rw @cswap_cswap.
  rw mk_swapping_app; auto.
  allrw disjoint_app_r; repnd.
  rw @cswap_disj_chain; auto; try omega;
  allrw disjoint_app_r; dands; eauto with slow.
  apply alphaeq_refl.
Qed.

(*
Lemma approx_star_sk_trans {o} :
  forall lib (sk1 sk2 sk3 : @sosub_kind o),
    approx_star_sk lib sk1 sk2
    -> approx_star_sk lib sk2 sk3
    -> approx_star_sk lib sk1 sk3.
Proof.
  introv ap1 ap2.
  allunfold @approx_star_sk.
  destruct sk1, sk2, sk3; allsimpl.
  allunfold @approx_star_bterm.
  allunfold @blift; exrepnd.

  pose proof (fresh_vars
                (length l)
                (l
                   ++ lv0
                   ++ l0
                   ++ lv
                   ++ l1
                   ++ all_vars n
                   ++ all_vars n0
                   ++ all_vars n1
                   ++ all_vars nt0
                   ++ all_vars nt1
                   ++ all_vars nt2
                   ++ all_vars nt3)) as h; exrepnd.

  applydup @alphaeqbt_numbvars in ap5 as len1; unfold num_bvars in len1; simpl in len1.
  applydup @alphaeqbt_numbvars in ap4 as len2; unfold num_bvars in len2; simpl in len2.
  applydup @alphaeqbt_numbvars in ap3 as len3; unfold num_bvars in len3; simpl in len3.
  applydup @alphaeqbt_numbvars in ap0 as len4; unfold num_bvars in len4; simpl in len4.

  apply alphaeq_bterm3_if with (lva := []) in ap5.
  apply alphaeq_bterm3_if with (lva := []) in ap4.
  apply alphaeq_bterm3_if with (lva := []) in ap3.
  apply alphaeq_bterm3_if with (lva := []) in ap0.

  allrw disjoint_app_r; repnd.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap5; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap5.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap4; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap4.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap3; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap3.

  apply (alpha3bt_change_var _ _ _ _ lvn) in ap0; auto;
  try (complete (allrw disjoint_app_r; auto)); try omega.
  apply alpha_eq_if3 in ap0.

Abort.
*)

Lemma approx_star_sosub_cons {o} :
  forall lib op v1 v2 sk1 sk2 (sub1 sub2 : @SOSub o),
    approx_star_sosub lib op ((v1,sk1) :: sub1) ((v2,sk2) :: sub2)
    <=> (approx_star_sk lib op sk1 sk2 # approx_star_sosub lib op sub1 sub2).
Proof.
  introv.
  unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl.
  allrw @length_so_range.
  split; intro k; repnd; dands; auto; cpx.
  - pose proof (k 0) as h; autodimp h hyp; omega.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; omega.
  - introv i.
    destruct n; cpx.
Qed.

Lemma approx_star_sk_alphaeq_l {o} :
  forall lib op (sk1 sk2 sk3 : @sosub_kind o),
    approx_star_sk lib op sk1 sk2
    -> alphaeq_sk sk2 sk3
    -> approx_star_sk lib op sk1 sk3.
Proof.
  introv ap aeq.
  allunfold @approx_star_sk.
  allunfold @alphaeq_sk.
  allrw @alphaeqbt_eq.
  destruct sk1 as [l1 t1], sk2 as [l2 t2], sk3 as [l3 t3]; allsimpl.
  eapply approx_star_bterm_alpha_fun_r; eauto.
Qed.

Lemma approx_star_sk_alphaeq_r {o} :
  forall lib op (sk1 sk2 sk3 : @sosub_kind o),
    alphaeq_sk sk1 sk2
    -> approx_star_sk lib op sk2 sk3
    -> approx_star_sk lib op sk1 sk3.
Proof.
  introv aeq ap.
  allunfold @approx_star_sk.
  allunfold @alphaeq_sk.
  allrw @alphaeqbt_eq.
  destruct sk1 as [l1 t1], sk2 as [l2 t2], sk3 as [l3 t3]; allsimpl.
  eapply approx_star_bterm_alpha_fun_l; eauto.
Qed.

Lemma approx_star_sosub_alphaeq_l {o} :
  forall lib op (sub1 sub2 sub3 : @SOSub o),
    approx_star_sosub lib op sub1 sub2
    -> alphaeq_sosub sub2 sub3
    -> approx_star_sosub lib op sub1 sub3.
Proof.
  induction sub1; destruct sub2; destruct sub3; introv ap aeq; auto;
  try (complete (inversion ap; allsimpl; cpx));
  try (complete (inversion aeq)).

  destruct p; destruct p0; destruct a.
  inversion aeq; subst; clear aeq.
  apply @approx_star_sosub_cons in ap; repnd.
  apply @approx_star_sosub_cons.

  dands.

  - eapply approx_star_sk_alphaeq_l; eauto.

  - eapply IHsub1; eauto.
Qed.

Lemma approx_star_sosub_alphaeq_r {o} :
  forall lib op (sub1 sub2 sub3 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> approx_star_sosub lib op sub2 sub3
    -> approx_star_sosub lib op sub1 sub3.
Proof.
  induction sub1; destruct sub2; destruct sub3; introv aeq ap; auto;
  try (complete (inversion ap; allsimpl; cpx));
  try (complete (inversion aeq)).

  destruct p; destruct p0.
  inversion aeq; subst; clear aeq.
  allapply @approx_star_sosub_cons; repnd.
  apply @approx_star_sosub_cons; repnd.

  dands.

  - eapply approx_star_sk_alphaeq_r; eauto.

  - eapply IHsub1; eauto.
Qed.

Lemma so_alphaeq_vs_preserves_wf {o} :
  forall (t1 t2 : @SOTerm o) vs,
    so_alphaeq_vs vs t1 t2
    -> wf_soterm t1
    -> wf_soterm t2.
Proof.
  introv aeq wf.
  eapply wf_soterm_so_alphaeq; [|eauto].
  eapply so_alphaeq_exists; eauto.
Qed.

Lemma approx_starbts_implies_approx_star_sosub {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)) vars,
    approx_starbts lib op bs1 bs2
    -> approx_star_sosub lib op (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv ap; allsimpl; auto;
  try (complete (inversion ap; allsimpl; cpx)).
  - unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - destruct s; unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
  - rw @approx_starbts_cons in ap; repnd.
    destruct s; destruct a, b; simpl; boolvar; simpl; tcsp.
    + apply approx_star_sosub_cons; dands; auto.
    + inversion ap0 as [vs x]; exrepnd.
      inversion x2; subst.
      inversion x1; subst.
      provefalse.
      destruct n3; omega.
    + inversion ap0 as [vs x]; exrepnd.
      inversion x2; subst.
      inversion x1; subst.
      provefalse.
      destruct n3; omega.
    + unfold approx_star_sosub, bin_rel_sk, binrel_list; simpl; sp.
Qed.

Lemma sosub_aux_approx_star_congr_al {p} :
  forall lib (t1 t2 : @SOTerm p) (sub1 sub2 : SOSub) opr,
    wf_soterm t1
    -> wf_soterm t2
    -> so_alphaeq t1 t2
    -> sodom sub1 = sodom sub2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t1)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t2)
    (* These 2 disjoints we can always assume because they are ensured by sosub *)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t1)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t2)
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> opr <> NCan NFresh
    -> approx_star_sosub lib opr sub1 sub2
    -> approx_star lib (sosub_aux sub1 t1) (sosub_aux sub2 t2).
Proof.
  soterm_ind1s t1 as [v ts ind| |op lbt ind] Case; simpl;
  introv wf1 wf2 aeq eqdoms d1 d2 d3 d4 cov1 cov2; introv d ap.

  - Case "sovar".
    applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
    inversion aeq as [? ? ? len imp| |]; subst; clear aeq; allsimpl.
    remember (sosub_find sub1 (v, length ts)) as o;
      destruct o; symmetry in Heqo;
      remember (sosub_find sub2 (v, length ts2)) as q;
      destruct q; symmetry in Heqq;
      try (destruct s); try (destruct s0).

    + pose proof (apply_bterm_approx_star_congr
                    lib opr (bterm l n) (bterm l0 n0)
                    (map (sosub_aux sub1) ts)
                    (map (sosub_aux sub2) ts2)
                 ) as h.
      repeat (autodimp h hyp); try (complete (intro xxx; ginv)).

      * apply approx_star_sk_is_approx_star_bterm; simpl.
        rw <- len in Heqq.
        eapply approx_star_sk_if_approx_star_sosub_find2;
          [exact eqdoms'|exact ap|exact Heqo|exact Heqq].

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux sub1 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux sub2 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n1 ts default_soterm) as t1.
        pose proof (nth_in _ n1 ts default_soterm i) as j1.
        remember (nth n1 ts2 default_soterm) as t2.
        dup i as i'; rw len in i'.
        pose proof (nth_in _ n1 ts2 default_soterm i') as j2.
        pose proof (imp t1 t2) as a;
          autodimp a hyp;[subst; apply in_nth_combine; complete auto|].
        rw <- Heqt1 in j1; clear Heqt1.
        rw <- Heqt2 in j2; clear Heqt2.

        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub sub1) (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub sub2) (flat_map fovars ts2))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        eapply ind; eauto.

        { rw disjoint_flat_map_r in d1; apply d1; auto. }

        { rw disjoint_flat_map_r in d2; apply d2; auto. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

      * allrw map_length; unfold num_bvars; simpl; auto.
        allapply @sosub_find_some; sp.

      * allrw map_length; unfold num_bvars; simpl; auto.

      * unfold apply_bterm in h; simpl in h.
        applydup @sosub_find_some in Heqo; repnd.
        applydup @sosub_find_some in Heqq; repnd.
        allrw @cover_so_vars_sovar; repnd.
        revert h.
        change_to_lsubst_aux4; auto; clear h;
        try (complete (allrw disjoint_cons_r; repnd;
                       rw flat_map_map; unfold compose;
                       eapply disjoint_bound_vars_prop3; eauto)).

    + rw len in Heqo.
      eapply false_if_approx_star_sosub_find in Heqo; eauto; sp.

    + rw len in Heqo.
      eapply false_if_approx_star_sosub_find2 in Heqo; eauto; sp.

    + apply approx_star_apply_list; auto.

      * apply approx_star_refl; auto.

      * unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
        introv i.

        assert (@default_nterm p = sosub_aux sub1 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        assert (@default_nterm p = sosub_aux sub2 default_soterm)
          as e by auto.
        rw e; rw map_nth; simpl; clear e; fold (@mk_axiom p); fold (@default_nterm p).
        remember (nth n ts default_soterm) as t1.
        remember (nth n ts2 default_soterm) as t2.
        dup i as i'; rw len in i'.
        pose proof (nth_in _ n ts default_soterm i) as j1.
        pose proof (nth_in _ n ts2 default_soterm i') as j2.
        pose proof (imp t1 t2) as a;
          autodimp a hyp;[subst; apply in_nth_combine; complete auto|].
        rw <- Heqt1 in j1; clear Heqt1.
        rw <- Heqt2 in j2; clear Heqt2.

        rw disjoint_flat_map_r in d1.
        rw disjoint_flat_map_r in d2.
        allrw disjoint_app_r; repnd.

        assert (disjoint (bound_vars_sosub sub1) (flat_map fovars ts))
          as disj1 by (boolvar; allrw disjoint_cons_r; sp).

        assert (disjoint (bound_vars_sosub sub2) (flat_map fovars ts2))
          as disj2 by (boolvar; allrw disjoint_cons_r; sp).

        allrw @wf_sovar.

        eapply ind; eauto.

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj1; sp. }

        { rw disjoint_app_r; dands; auto.
          rw disjoint_flat_map_r in disj2; sp. }

        { rw @cover_so_vars_sovar in cov1; sp. }

        { rw @cover_so_vars_sovar in cov2; sp. }

  - Case "soseq".
    inversion aeq as [ | ? ? F | ]; clear aeq; subst; allsimpl; tcsp.
    eapply apss;[introv; apply alphaeq_eq;apply F|].
    apply approx_open_refl.
    apply nt_wf_eq; auto.

  - Case "soterm".
    applydup @eq_sodoms_implies_eq_so_doms in eqdoms as eqdoms'.
    inversion aeq as [| |? ? ? len imp]; subst; clear aeq; allsimpl.
    allrw disjoint_app_r; repnd.

    allrw @wf_soterm_iff; repnd.
    allrw @cover_so_vars_soterm.

    apply approx_star_congruence;
      [|rw map_map; unfold compose; rw <- wf0;
        apply eq_maps_combine; auto; introv i;
        apply in_combine_swap in i; auto;
        apply imp in i;
        rw @num_bvars_sosub_b_aux;
        apply so_alphaeq_vs_implies_eq_num_sobvars in i; auto].

    apply approx_starbts_map; auto.
    introv i.
    applydup imp in i as a.

    destruct a1 as [l1 t1].
    destruct a2 as [l2 t2].

    applydup in_combine in i; repnd.
    applydup wf1 in i1.
    applydup wf2 in i0.

    simpl.
    apply (so_alphaeqbt_vs_implies_more
            _ _ _ (free_vars_sosub sub1
                                   ++ so_dom sub1
                                   ++ so_dom sub2
                                   ++ free_vars_sosub sub2
                                   ++ bound_vars_sosub sub1
                                   ++ bound_vars_sosub sub2
                                   ++ allvars (sosub_aux (sosub_filter sub1 (vars2sovars l1)) t1)
                                   ++ allvars (sosub_aux (sosub_filter sub2 (vars2sovars l2)) t2)
          )) in a; auto.
    inversion a as [? ? ? u1 u2 len1 len2 disj norep ae]; subst; allsimpl; clear a.
    apply so_alphaeq_vs_iff in ae.
    allrw disjoint_app_r; repnd.

    unfold approx_star_bterm, blift_sub.

    exists vs
           (sosub_aux sub1 (so_swap (mk_swapping l1 vs) t1))
           (sosub_aux sub2 (so_swap (mk_swapping l2 vs) t2)).

    dands; auto.

    + pose proof (ind t1 (so_swap (mk_swapping l1 vs) t1) l1) as h; clear ind.
      rw @sosize_so_swap in h; auto.
      repeat (autodimp h hyp).
      pose proof (h (so_swap (mk_swapping l2 vs) t2) sub1 sub2 opr) as k; clear h.
      allrw <- @wf_soterm_so_swap.
      repeat (autodimp k hyp).

      { rw @fo_bound_var_so_swap.
        rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
        allrw disjoint_app_r; repnd.
        apply disjoint_swapbvars; eauto with slow. }

      { rw @fo_bound_var_so_swap.
        rw disjoint_flat_map_r in d2; applydup d2 in i0 as k; simpl in k.
        allrw disjoint_app_r; repnd.
        apply disjoint_swapbvars; eauto with slow. }

      { rw @fovars_so_swap.
        rw disjoint_app_r; dands; auto.
        apply disjoint_swapbvars; eauto 3 with slow.
        { rw disjoint_flat_map_r in d3; applydup d3 in i1 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
        { rw disjoint_flat_map_r in d3; applydup d3 in i1 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
      }

      { rw @fovars_so_swap.
        rw disjoint_app_r; dands; auto.
        apply disjoint_swapbvars; eauto 3 with slow.
        { rw disjoint_flat_map_r in d4; applydup d4 in i0 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
        { rw disjoint_flat_map_r in d4; applydup d4 in i0 as k; simpl in k.
          allrw disjoint_app_r; repnd; auto. }
      }

      { apply cover_so_vars_so_swap; eauto with slow. }

      { apply cover_so_vars_so_swap; eauto with slow. }

      destruct (dec_op_eq_fresh op) as [df|df]; tcsp.

      {
        right.
        pose proof (exists_nrut_sub
                      vs
                      (get_utokens (sosub_aux sub1 (so_swap (mk_swapping l1 vs) t1))
                                   ++
                                   get_utokens (sosub_aux sub2 (so_swap (mk_swapping l2 vs) t2))))
          as exnrut; exrepnd.
        exists sub; dands; auto.
        apply lsubst_approx_star_congr3; eauto with slow.
      }

    + rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
      rw disjoint_flat_map_r in d2; applydup d2 in i0 as j; simpl in j.
      rw disjoint_flat_map_r in d3; applydup d3 in i1 as m; simpl in m.
      rw disjoint_flat_map_r in d4; applydup d4 in i0 as n; simpl in n.
      allrw disjoint_app_r; repnd; auto.

      pose proof (subvars_swpbvars l1 l1 vs) as sv;
        repeat (autodimp sv hyp); eauto 3 with slow;[].

      pose proof (sosub_filter_if_not_in_dom
                    (so_swap (mk_swapping l1 vs) t1)
                    sub1
                    (vars2sovars (swapbvars (mk_swapping l1 vs) l1))) as h.
      autodimp h hyp;
        [apply if_disjoint_sovars2vars;
          rw sovars2vars_vars2sovars;
          rw @sovars2vars_sodom_is_so_dom; eauto with slow|].
      rw <- h; clear h.

      pose proof (sosub_aux_sosub_filter_so_swap
                    t1 sub1 l1 vs l1) as h;
        repeat (autodimp h hyp); eauto 3 with slow;[].
      rw h; clear h.

      pose proof (btchange_alpha_cswap
                    (sosub_aux (sosub_filter sub1 (vars2sovars l1)) t1)
                    l1 vs) as e; repeat (autodimp e hyp); eauto 3 with slow.

    + rw disjoint_flat_map_r in d1; applydup d1 in i1 as k; simpl in k.
      rw disjoint_flat_map_r in d2; applydup d2 in i0 as j; simpl in j.
      rw disjoint_flat_map_r in d3; applydup d3 in i1 as m; simpl in m.
      rw disjoint_flat_map_r in d4; applydup d4 in i0 as n; simpl in n.
      allrw disjoint_app_r; repnd; auto.

      pose proof (subvars_swpbvars l2 l2 vs) as sv;
        repeat (autodimp sv hyp); eauto 3 with slow;[].

      pose proof (sosub_filter_if_not_in_dom
                    (so_swap (mk_swapping l2 vs) t2)
                    sub2
                    (vars2sovars (swapbvars (mk_swapping l2 vs) l2))) as h.
      autodimp h hyp;
        [apply if_disjoint_sovars2vars;
          rw sovars2vars_vars2sovars;
          rw @sovars2vars_sodom_is_so_dom; eauto with slow|].
      rw <- h; clear h.

      pose proof (sosub_aux_sosub_filter_so_swap
                    t2 sub2 l2 vs l2) as h;
        repeat (autodimp h hyp); eauto 3 with slow;[].
      rw h; clear h.

      pose proof (btchange_alpha_cswap
                    (sosub_aux (sosub_filter sub2 (vars2sovars l2)) t2)
                    l2 vs) as e; repeat (autodimp e hyp); eauto 3 with slow.
Qed.

Lemma sosub_approx_star_congr {p} :
  forall (lib : library)
         (opr : Opid)
         (t : @SOTerm p)
         (sub1 sub2 : SOSub),
    wf_soterm t
    -> sodom sub1 = sodom sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> opr <> NCan NFresh
    -> approx_star_sosub lib opr sub1 sub2
    -> approx_star lib (sosub sub1 t) (sosub sub2 t).
Proof.
  introv wf len cov1 cov2 d ap.
  pose proof (fovars_subvars_all_fo_vars t) as sv.

  pose proof (unfold_sosub sub1 t) as h; exrepnd.
  rw h1; clear h1.

  pose proof (unfold_sosub sub2 t) as k; exrepnd.
  rw k1; clear k1.

  applydup @alphaeq_sosub_implies_eq_sodoms in h0 as eqdoms1.
  applydup @alphaeq_sosub_implies_eq_sodoms in k0 as eqdoms2.
  pose proof (fovars_subvars_all_fo_vars t') as sv1.
  pose proof (fovars_subvars_all_fo_vars t'0) as sv2.
  pose proof (cover_so_vars_if_so_alphaeq t t' sub1 cov1 h2) as cov3; auto.
  pose proof (cover_so_vars_if_alphaeq_sosub t' sub1 sub' cov3 h0) as cov4; auto.
  pose proof (cover_so_vars_if_so_alphaeq t t'0 sub2 cov2 k2) as cov5; auto.
  pose proof (cover_so_vars_if_alphaeq_sosub t'0 sub2 sub'0 cov5 k0) as cov6; auto.

  eapply sosub_aux_approx_star_congr_al; eauto 3 with slow.

  - apply so_alphaeq_vs_preserves_wf in h2; auto.

  - apply so_alphaeq_vs_preserves_wf in k2; auto.

  - allrw <-; auto.

  - rw disjoint_app_r; dands; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.

  - eapply approx_star_sosub_alphaeq_r;[apply alphaeq_sosub_sym;exact h0|].
    eapply approx_star_sosub_alphaeq_l;[|exact k0];auto.
Qed.

Lemma mk_instance_approx_star_congr {p} :
  forall (lib : library)
         (opr : @Opid p)
         (t : @SOTerm p)
         (vars : list sovar_sig)
         (bs1 bs2 : list BTerm),
    wf_soterm t
    -> socovered t vars
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> opr <> NCan NFresh
    -> approx_starbts lib opr bs1 bs2
    -> approx_star lib (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv wf cov m1 m2 d ap.
  unfold mk_instance.
  eapply sosub_approx_star_congr; eauto.

  - rw <- @mk_abs_subst_some_prop2; auto.
    rw <- @mk_abs_subst_some_prop2; auto.

  - apply socovered_implies_cover_so_vars; auto.

  - apply socovered_implies_cover_so_vars; auto.

  - apply approx_starbts_implies_approx_star_sosub; auto.
Qed.

Lemma nuprl_extensional_abs {p} :
  forall x : opabs, @extensional_op p (Abs x).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  allfold (approx_starbts lib).
  apply computes_to_val_like_in_max_k_steps_S in Hcv; exrepnd.
  csunf Hcv1; allsimpl.
  apply compute_step_lib_success in Hcv1; exrepnd; subst.
  dup Hcv2 as fe1.
  pose proof (approx_starbts_numvars lib (Abs x) lbt lbt' Has) as eqnum.
  apply @found_entry_change_bs with (bs2 := lbt') in Hcv2; auto.
  rename Hcv2 into fe2.

  unfold extensional_op_ind in Hi.

  apply Hi with (v := mk_instance vars lbt' rhs) in Hcv0; auto;
  [ | complete (eapply isprogram_subst_lib; eauto;
                apply isprogram_ot_iff in Hprt; repnd; auto)
    | complete (eapply isprogram_subst_lib; eauto;
                apply isprogram_ot_iff in Hprt'; repnd; auto)
    | ]; clear Hi.

  - apply @approx_star_open_trans with (b := mk_instance vars lbt' rhs); auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_if_step; simpl.
    eapply compute_step_lib_success_change_bs; eauto.

  - unfold correct_abs in correct;repnd.
    eapply mk_instance_approx_star_congr; eauto; try (complete (intro xxx; ginv)).

    + apply found_entry_implies_matching_entry in fe1.
      unfold matching_entry in fe1; sp.

    + apply found_entry_implies_matching_entry in fe2.
      unfold matching_entry in fe2; sp.
Qed.

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

Lemma isprog_vars_iff_isprogram_bt {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t <=> isprogram_bt (bterm vs t).
Proof.
  introv.
  rw @isprog_vars_eq.
  unfold isprogram_bt; simpl.
  rw @bt_wf_iff.
  rw @closed_bt_bterm; sp.
Qed.

Lemma isprog_vars_implies_isprogram_bt {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> isprogram_bt (bterm vs t).
Proof.
  introv isp.
  apply isprog_vars_iff_isprogram_bt; auto.
Qed.
Hint Resolve isprog_vars_implies_isprogram_bt : slow.

Lemma alpha_eq_bterm_implies_eq_length {o} :
  forall vs1 vs2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm vs1 t1) (bterm vs2 t2)
    -> length vs1 = length vs2.
Proof.
  introv aeq.
  inversion aeq; subst; auto.
Qed.

Lemma isprogram_lsubst_aux_implies {o} :
  forall (t : @NTerm o) sub,
    disjoint_bv_sub t sub
    -> isprogram (lsubst_aux t sub)
    -> isprogram_bt (bterm (dom_sub sub) t).
Proof.
  introv d isp.
  apply isprog_vars_iff_isprogram_bt.
  apply isprog_vars_eq.
  destruct isp as [c w].
  apply lsubst_aux_nt_wf in w; dands; auto.
  rw subvars_prop; introv i.
  unfold closed in c.
  rw <- null_iff_nil in c.
  unfold null in c.
  destruct (in_deq _ deq_nvar x (dom_sub sub)) as [j|j]; auto.
  provefalse.
  pose proof (c x) as h; destruct h.
  pose proof (eqvars_free_vars_disjoint_aux2 t sub d) as h; auto.
  rw eqvars_prop in h; apply h; clear h.
  rw in_app_iff; rw in_remove_nvars; sp.
Qed.

Lemma isprogram_lsubst_implies {o} :
  forall (t : @NTerm o) sub,
    isprogram (lsubst t sub)
    -> isprogram_bt (bterm (dom_sub sub) t).
Proof.
  introv isp.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0 in isp.
  apply isprogram_lsubst_aux_implies in isp; auto.
  - allunfold @isprogram_bt.
    allunfold @closed_bt; allsimpl.
    applydup @alphaeq_preserves_free_vars in h1 as fv.
    rw fv; repnd; dands; auto.
    allrw @bt_wf_iff.
    apply alphaeq_preserves_wf in h1; apply h1; auto.
  - unfold disjoint_bv_sub, sub_range_sat; introv i j k.
    apply h2 in k; destruct k.
    apply in_sub_free_vars_iff.
    exists v t0; dands; auto.
Qed.

Lemma isprogram_subst_implies {o} :
    forall (t : @NTerm o) (v : NVar) (a : NTerm),
      isprogram (subst t v a)
      -> isprogram_bt (bterm [v] t).
Proof.
  introv isp.
  apply isprogram_lsubst_implies in isp; allsimpl; auto.
Qed.

Definition get_op {o} (t : @NTerm o) : Opid :=
  match t with
    | vterm _ => Exc
    | sterm _ => Exc
    | oterm op _ => op
  end.

Inductive same_value_like {o} : @NTerm o -> @NTerm o -> Type :=
| svl_c : forall c bs1 bs2, same_value_like (oterm (Can c) bs1) (oterm (Can c) bs2)
| svl_e : forall bs1 bs2, same_value_like (oterm Exc bs1) (oterm Exc bs2)
| svl_s :
    forall f1 f2,
      (forall n, alpha_eq (f1 n) (f2 n))
      -> same_value_like (sterm f1) (sterm f2).
Hint Constructors same_value_like.

Lemma approx_starbts_nil {o} :
  forall lib (op : @Opid o), approx_starbts lib op [] [].
Proof.
  introv; unfold approx_starbts, lblift_sub; simpl; dands; tcsp.
Qed.
Hint Resolve approx_starbts_nil : slow.

Lemma howe_lemma2_implies_same_value_like {o} :
  forall lib (t u : @NTerm o),
    isprogram t
    -> isprogram u
    -> isvalue_like t
    -> approx_star lib t u
    -> {v : NTerm
        & same_value_like t v
        # approx_starbts lib (get_op t) (get_bterms t) (get_bterms v)
        # reduces_to lib u v}.
Proof.
  introv ispt ispu isv ap.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst.

    + pose proof (howe_lemma2 lib c bterms u) as h; simpl in h.
      repeat (autodimp h hyp).
      exrepnd.
      exists (oterm (Can c) lbt'); dands; eauto.
      unfold computes_to_value in h0; repnd; auto.

    + apply howe_lemma2_seq in ap; auto; exrepnd.
      exists (sterm f'); dands; simpl; eauto 3 with slow; tcsp.

  - apply isexc_implies2 in isv; exrepnd; subst.
    applydup @isprogram_exception_implies in ispt; exrepnd; subst.
    pose proof (howe_lemma2_exc lib a t u) as h; simpl in h.
    repeat (autodimp h hyp).
    exrepnd.
    exists (oterm Exc [bterm [] a', bterm [] e']); simpl; dands; auto.
    unfold approx_starbts, lblift_sub; simpl; dands; auto.
    introv k; repeat (destruct n; cpx).
    + unfold selectbt; simpl; eauto with slow.
    + unfold selectbt; simpl; eauto with slow.
Qed.

Lemma same_value_like_alpha_eq_r {o} :
  forall (t u v : @NTerm o),
    same_value_like t u
    -> alpha_eq u v
    -> same_value_like t v.
Proof.
  introv svl aeq.
  inversion svl as [| |? ? imp1]; clear svl; subst;
  inversion aeq as [|? ? imp2|]; clear aeq; subst; auto.
  constructor; introv; eauto 3 with slow.
Qed.

Lemma same_value_like_alpha_eq_l {o} :
  forall (t u v : @NTerm o),
    same_value_like t u
    -> alpha_eq t v
    -> same_value_like v u.
Proof.
  introv svl aeq.
  inversion svl as [| |? ? imp1]; clear svl; subst;
  inversion aeq as [|? ? imp2|]; clear aeq; subst; auto.
  constructor; introv; eauto 3 with slow.
Qed.

Lemma approx_starbts_get_bterms_alpha_eq {o} :
  forall lib op (t u v : @NTerm o),
    approx_starbts lib op (get_bterms t) (get_bterms u)
    -> alpha_eq u v
    -> approx_starbts lib op (get_bterms t) (get_bterms v).
Proof.
  introv ap aeq.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl; auto;
  try (complete (inversion aeq; subst; allsimpl; tcsp)).
  - unfold approx_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_starbts, lblift_sub; simpl; sp.
  - unfold approx_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_starbts, lblift_sub; simpl; sp.
  - inversion aeq as [|?|? ? ? len imp]; subst; simpl.
    allunfold @approx_starbts.
    allunfold @lblift_sub; repnd; dands; auto; try omega.
    introv i.
    pose proof (ap n) as h1; autodimp h1 hyp.
    pose proof (imp n) as h2; autodimp h2 hyp; try omega.
    eapply approx_star_bterm_alpha_fun_r; eauto.
Qed.

(*
Lemma approx_star_congruence_same_value_like {o} :
  forall lib (t u : @NTerm o),
    isprogram t
    -> isprogram u
    -> same_value_like t u
    -> approx_starbts lib (get_op t) (get_bterms t) (get_bterms u)
    -> approx_star lib t u.
Proof.
  introv ispt ispu svl ap.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl;
  try (complete (apply isprogram_vterm in ispt; sp));
  try (complete (apply isprogram_vterm in ispu; sp));
  try (complete (inversion svl)).
  - apply (apss _ _ _ f2); eauto 3 with slow.
  - inversion svl; subst; apply approx_star_congruence3; auto.
Qed.
*)

Lemma closed_axiom {o} :
  @closed o mk_axiom.
Proof. sp. Qed.
Hint Resolve closed_axiom : slow.

Lemma alpha_eq_subst_utoken_not_in_implies2 {o} :
  forall (t1 t2 : @NTerm o) v a,
    !LIn a (get_utokens t1)
    -> !LIn a (get_utokens t2)
    -> alpha_eq (subst t1 v (mk_utoken a)) (subst t2 v (mk_utoken a))
    -> alpha_eq t1 t2.
Proof.
  introv ni1 ni2 aeq.
  pose proof (change_bvars_alpha_wspec [v] t1) as k1.
  pose proof (change_bvars_alpha_wspec [v] t2) as k2.
  exrepnd.
  allrw disjoint_singleton_l.
  pose proof (lsubst_alpha_congr2 ntcv0 t1 [(v,mk_utoken a)]) as p1.
  pose proof (lsubst_alpha_congr2 ntcv t2 [(v,mk_utoken a)]) as p2.
  autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
  allrw @fold_subst.
  assert (alpha_eq (subst ntcv0 v (mk_utoken a)) (subst ntcv v (mk_utoken a))) as h' by eauto with slow.
  apply alpha_eq_subst_utoken_not_in_implies in h'; eauto with slow.
  { intro j; destruct ni1; apply alphaeq_preserves_utokens in k3; rw k3; auto. }
  { intro j; destruct ni2; apply alphaeq_preserves_utokens in k0; rw k0; auto. }
Qed.

Lemma isprogram_pushdown_fresh {o} :
  forall v (t : @NTerm o),
    isprogram (pushdown_fresh v t) <=> isprog_vars [v] t.
Proof.
  introv; split; intro k.
  - destruct k as [c w].
    rw @isprog_vars_eq.
    apply nt_wf_pushdown_fresh in w; dands; auto.
    unfold closed in c.
    rw @free_vars_pushdown_fresh in c.
    rw subvars_prop; introv i.
    rw <- null_iff_nil in c.
    rw null_remove_nvars in c; apply c in i; sp.
  - rw @isprog_vars_eq in k; repnd.
    split; allrw @nt_wf_pushdown_fresh; auto.
    unfold closed; rw @free_vars_pushdown_fresh.
    rw <- null_iff_nil.
    rw null_remove_nvars; introv i.
    rw subvars_prop in k0; apply k0; auto.
Qed.

Lemma same_value_like_implies_same_op {o} :
  forall op1 op2 (bs1 bs2 : list (@BTerm o)),
    same_value_like (oterm op1 bs1) (oterm op2 bs2)
    -> op1 = op2.
Proof.
  introv s; inversion s; auto.
Qed.

Lemma fresh_id_approx_any {o} :
  forall lib (t : @NTerm o) x,
    isprogram t
    -> approx lib (mk_fresh x (mk_var x)) t.
Proof.
  introv Hpr.
  apply approx_assume_hasvalue; auto.
  { apply isprogram_fresh; apply isprog_vars_var. }

  introv Hv.
  unfold hasvalue_like in Hv; exrepnd.
  apply (not_fresh_id_reduces_to_is_value_like _ _ x) in Hv1; tcsp.
Qed.

Lemma change_bvars_alpha_norep {o} :
  forall (t : @NTerm o) (lv : list NVar),
    {u : NTerm
     $ disjoint lv (bound_vars u)
     # alpha_eq t u
     # no_repeats (bound_vars u)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv.

  - Case "vterm".
    exists (@mk_var o v); simpl; dands; auto.

  - Case "sterm".
    exists (sterm f); simpl; dands; eauto 3 with slow.

  - Case "oterm".

    assert (forall lv, {bs' : list BTerm
            $ disjoint lv (bound_vars_bterms bs')
            # alpha_eq_bterms bs bs'
            # no_repeats (bound_vars_bterms bs') }) as ibs.
    { clear lv; induction bs; introv; allsimpl.
      - exists ([] : list (@BTerm o)); simpl; dands; eauto with slow.
      - autodimp IHbs hyp.
        { introv i s; eapply ind; eauto. }
        pose proof (IHbs lv) as ibs; clear IHbs; exrepnd.
        destruct a as [l t].

        pose proof (fresh_vars (length l)
                               (lv ++ l
                                   ++ all_vars t
                                   ++ bound_vars_bterms bs'))
             as fvs; exrepnd.
        allrw disjoint_app_r; exrepnd.

        pose proof (ind t (lsubst t (var_ren l lvn)) l) as ih; clear ind; repeat (autodimp ih hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }

        pose proof (ih (lv ++ lvn ++ bound_vars_bterms bs')) as ht; clear ih.
        exrepnd.
        allrw disjoint_app_l; repnd.

        exists (bterm lvn u :: bs'); simpl.
        allrw no_repeats_app.
        allrw disjoint_app_l; allrw disjoint_app_r.
        dands; eauto 3 with slow.
        apply alpha_eq_bterms_cons; dands; auto.
        eapply alpha_eq_bterm_trans;[|apply alpha_eq_bterm_congr;exact ht2].
        apply alpha_bterm_change; auto.
        allrw disjoint_app_l; dands; eauto with slow.
    }

    pose proof (ibs lv) as h; clear ibs; exrepnd.
    exists (oterm op bs'); simpl; dands; auto.
    apply alpha_eq_oterm_combine; auto.
Qed.

Lemma blift_sub_diff {o} :
  forall vs lib op (b1 b2 : @BTerm o),
    blift_sub op (approx_star lib) b1 b2
    -> {lv : list NVar
        $ {nt1,nt2 : NTerm
        $ (
            (op <> NCan NFresh # approx_star lib nt1 nt2)
            [+]
            {sub : Sub
             & op = NCan NFresh
             # approx_star lib (lsubst nt1 sub) (lsubst nt2 sub)
             # nrut_sub (get_utokens nt1 ++ get_utokens nt2) sub
             # lv = dom_sub sub}
          )
        # alpha_eq_bterm b1 (bterm lv nt1)
        # alpha_eq_bterm b2 (bterm lv nt2)
        # disjoint vs lv
        # disjoint vs (bound_vars nt1)
        # disjoint vs (bound_vars nt2)
        # disjoint lv (bound_vars nt1)
        # disjoint lv (bound_vars nt2)
        # no_repeats lv
        # no_repeats (bound_vars nt1)
        # no_repeats (bound_vars nt2) }}.
Proof.
  introv bl.
  unfold blift_sub in bl; exrepnd.

  pose proof (alpha_bterm_pair_change b1 b2 lv nt1 nt2 vs) as h.
  repeat (autodimp h hyp); exrepnd.
  allrw disjoint_app_r; allrw disjoint_app_l; repnd.

  pose proof (change_bvars_alpha_norep nt1n (vs ++ lvn)) as ch1; exrepnd.
  assert (alpha_eq nt1 u) as h2' by eauto with slow.
  assert (alpha_eq_bterm b1 (bterm lvn (lsubst u (var_ren lv lvn)))) as h4'.
  { eapply alpha_eq_bterm_trans;[exact h4|].
    apply alpha_eq_bterm_congr.
    apply lsubst_alpha_congr2; auto. }
  allrw disjoint_app_l; repnd.
  rename ch3 into h9'.
  rename ch1 into h13'.
  clear dependent nt1n.
  rename h2' into h2; rename h4' into h4; rename h9' into h9; rename h13' into h13.
  rename u into nt1n.

  pose proof (change_bvars_alpha_norep nt2n (vs ++ lvn)) as ch'1; exrepnd.
  assert (alpha_eq nt2 u) as h3' by eauto with slow.
  assert (alpha_eq_bterm b2 (bterm lvn (lsubst u (var_ren lv lvn)))) as h5'.
  { eapply alpha_eq_bterm_trans;[exact h5|].
    apply alpha_eq_bterm_congr.
    apply lsubst_alpha_congr2; auto. }
  allrw disjoint_app_l; repnd.
  rename ch'3 into h0'.
  rename ch'1 into h7'.
  clear dependent nt2n.
  rename h3' into h3; rename h5' into h5; rename h7' into h7; rename h0' into h0.
  rename u into nt2n.

  exists lvn (lsubst nt1n (var_ren lv lvn)) (lsubst nt2n (var_ren lv lvn)).
  dands; eauto 3 with slow; try (complete (rw @boundvars_lsubst_vars; auto)).

  repndors; exrepnd.

  - left; dands; auto.
    apply approx_star_lsubst_vars; eauto 3 with slow.

  - right.
    exists (combine lvn (range sub)); dands; auto.

    + pose proof (lsubst_nest_same_alpha2 nt1n lv lvn (range sub)) as nest1.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest1 hyp); try omega; eauto 3 with slow.
      { subst; allrw @length_dom; auto. }
      { apply alphaeq_preserves_free_vars in h2; rw <- h2.
        apply disjoint_remove_nvars_weak_r; auto. }
      eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact nest1].

      pose proof (lsubst_nest_same_alpha2 nt2n lv lvn (range sub)) as nest2.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest2 hyp); try omega; eauto 3 with slow.
      { subst; allrw @length_dom; auto. }
      { apply alphaeq_preserves_free_vars in h3; rw <- h3.
        apply disjoint_remove_nvars_weak_r; auto. }
      eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact nest2].

      subst.
      rw <- @sub_eta; auto.

      apply (lsubst_alpha_congr2 _ _ sub) in h2.
      apply (lsubst_alpha_congr2 _ _ sub) in h3.
      eauto with slow.

    + repeat (rw @get_utokens_lsubst_allvars; eauto with slow).
      apply alphaeq_preserves_utokens in h2.
      apply alphaeq_preserves_utokens in h3.
      rw <- h2; rw <- h3.
      eapply nrut_sub_change_sub_same_range;[|exact bl5].
      rw @range_combine; auto.
      rw @length_range; auto.
      subst; allrw @length_dom; auto.

    + rw @dom_sub_combine; auto.
      rw @length_range; auto.
      subst; allrw @length_dom; auto.
Qed.

Lemma bt_wf_mk_fresh_bterm_if {o} :
  forall (b : @BTerm o) v,
    bt_wf b
    -> bt_wf (mk_fresh_bterm v b).
Proof.
  introv wf.
  destruct b as [l t]; allsimpl.
  allrw @bt_wf_iff.
  apply nt_wf_fresh; auto.
Qed.

Lemma alpha_eq_bterm_ren_1side {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (bound_vars t1)
    -> disjoint l1 (bound_vars t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l1 (lsubst t2 (var_ren l2 l1))).
Proof.
  introv disj1 disj2 aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.
  apply (lsubst_alpha_congr2 _ _ (var_ren lv l1)) in a.
  allrw disjoint_app_r; repnd.

  pose proof (lsubst_nest_vars_same t1 l1 lv l1) as h1.
  allrw disjoint_app_l.
  repeat (autodimp h1 hyp); dands; eauto 3 with slow.
  rw h1 in a.

  pose proof (lsubst_nest_vars_same t2 l2 lv l1) as h2.
  allrw disjoint_app_l.
  repeat (autodimp h2 hyp); dands; try omega; eauto 3 with slow.
  rw h2 in a.

  pose proof (lsubst_trivial_alpha t1 l1) as h.
  eauto with slow.
Qed.

Lemma alpha_eq_bterm_ren_1side2 {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (bound_vars t1)
    -> disjoint l1 (bound_vars t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq t1 (lsubst t2 (var_ren l2 l1)).
Proof.
  introv disj1 disj2 aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.
  apply (lsubst_alpha_congr2 _ _ (var_ren lv l1)) in a.
  allrw disjoint_app_r; repnd.

  pose proof (lsubst_nest_vars_same t1 l1 lv l1) as h1.
  allrw disjoint_app_l.
  repeat (autodimp h1 hyp); dands; eauto 3 with slow.
  rw h1 in a.

  pose proof (lsubst_nest_vars_same t2 l2 lv l1) as h2.
  allrw disjoint_app_l.
  repeat (autodimp h2 hyp); dands; try omega; eauto 3 with slow.
  rw h2 in a.

  pose proof (lsubst_trivial_alpha t1 l1) as h.
  eauto with slow.
Qed.

Lemma alpha_eq_lsubst_aux_pull_out_token {o} :
  forall (t : @NTerm o) l sub t',
    disjoint (dom_sub sub) (bound_vars t)
    -> disjoint (dom_sub sub) (bound_vars t')
    -> disjoint (bound_vars t) (bound_vars t')
    -> no_repeats (bound_vars t)
    -> nrut_sub l sub
    -> subset (get_utokens t') l
    -> no_repeats (dom_sub sub)
    -> wf_term t
    -> alpha_eq t (lsubst_aux t' sub)
    -> {u : NTerm $ t = lsubst_aux u sub # disjoint (get_utokens u) (get_utokens_sub sub)}.
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case;
  introv disj1 disj2 disj3 norep nrut ss nrs wf aeq;
  allsimpl; GC.

  - Case "vterm".
    destruct t' as [z|f|op' bs']; allsimpl;
    try (complete (inversion aeq)).

    remember (sub_find sub z) as sf; symmetry in Heqsf; destruct sf.

    + apply sub_find_some in Heqsf.
      eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst; inversion aeq.
    + inversion aeq; subst.
      exists (@mk_var o z); simpl; boolvar; tcsp.
      rw Heqsf; auto.

  - Case "sterm".
    exists (sterm f); simpl; dands; auto.

  - Case "oterm".
    destruct t' as [z|f|op' bs']; allsimpl; try (complete (inversion aeq)).

    + remember (sub_find sub z) as sf; symmetry in Heqsf; destruct sf;
      try (complete (inversion aeq)).

      apply sub_find_some in Heqsf.
      eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst; inversion aeq; subst.
      allsimpl; cpx; allsimpl; fold_terms.

      pose proof (in_nrut_sub_or l a sub) as ora.
      repeat (autodimp ora hyp); repndors; exrepnd.

      { exists (@mk_var o v); simpl; allrw; dands; auto. }

      { exists (mk_utoken a); simpl; auto.
        rw disjoint_singleton_l; dands; auto. }

    + allrw @alpha_eq_oterm_combine2; repnd; subst.
      allrw map_length.

      rw @wf_oterm_iff in wf; repnd.

      assert {bs'' : list BTerm
              & bs = lsubst_bterms_aux bs'' sub
              # disjoint (get_utokens_bs bs'') (get_utokens_sub sub)} as hbs.
      { clear wf0.
        revert dependent bs'.
        revert dependent bs.
        induction bs as [|b bs]; introv ind disj1 norep wf disj2 disj3 ss len imp; allsimpl; cpx; GC.

        - exists ([] : list (@BTerm o)); simpl; auto.

        - destruct bs' as [|b' bs']; allsimpl; cpx.
          allrw in_app_iff; allrw not_over_or; repnd.
          allrw no_repeats_app; repnd.
          allrw disjoint_app_r; allrw disjoint_app_l; repnd.
          repeat (autodimp IHbs hyp).
          { introv i j k; eapply ind; eauto. }
          pose proof (IHbs bs') as ih; clear IHbs.
          repeat (autodimp ih IHbs); exrepnd.
          { allrw subset_app; repnd; dands; auto. }
          pose proof (imp b (lsubst_bterm_aux b' sub)) as h.
          repeat (autodimp h hyp).
          destruct b as [l1 t1].
          destruct b' as [l2 t2].
          allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          allrw disjoint_app_l; repnd.
          allrw no_repeats_app; repnd.
          allrw disjoint_app_r; allrw disjoint_app_l; repnd.
          applydup @alpha_eq_bterm_lenbvars in h.

          apply alpha_eq_bterm_ren_1side2 in h; auto;
          [|introv i j; apply subset_bound_vars_lsubst_aux in j; allsimpl;
            allrw in_app_iff; repndors; tcsp;
            [apply disj8 in i; sp|];
            rw (sub_bound_vars_nrut_sub (sub_filter sub l2) l) in j; allsimpl; tcsp;
            complete (eauto with slow)].
          pose proof (ind t1 l1) as k; clear ind; autodimp k hyp.

          rw @lsubst_lsubst_aux in h;
            [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
               rw @sub_free_vars_var_ren; auto;
               introv i j; apply subset_bound_vars_lsubst_aux in i; allsimpl;
               allrw in_app_iff; applydup disj8 in j; repndors; tcsp;
               apply subset_sub_bound_vars_sub_filter in i;
               erewrite sub_bound_vars_nrut_sub in i; eauto].

          rw (sub_filter_disjoint1 sub) in h; eauto 3 with slow.

          pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                        t2 sub (var_ren l2 l1)) as e.
          allsimpl; rw @sub_free_vars_var_ren in e; auto.
          rw (sub_bound_vars_nrut_sub sub l) in e; eauto 3 with slow.
          rw (sub_free_vars_nrut_sub sub l) in e; eauto 3 with slow.
          rw @cl_lsubst_aux_sub_trivial in e; eauto 3 with slow.
          repeat (autodimp e hyp); eauto with slow.
          rw <-  e in h; clear e.

          pose proof (k l sub (lsubst_aux t2 (sub_filter (var_ren l2 l1) (dom_sub sub))))
            as ih; clear k.
          repeat (autodimp ih hyp); eauto 3 with slow.
          { introv i j; apply subset_bound_vars_lsubst_aux in j.
            rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
            allrw app_nil_r; apply disj7 in i; sp. }
          { introv i j; apply subset_bound_vars_lsubst_aux in j.
            rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
            allrw app_nil_r; apply disj5 in i; sp. }
          { allrw subset_app; repnd; rw @get_utokens_lsubst_aux_allvars; eauto 3 with slow. }
          { pose proof (wf (bterm l1 t1)) as w; autodimp w hyp. }

          exrepnd.
          exists (bterm l1 u :: bs''); simpl.
          allrw disjoint_app_l; dands; eauto 3 with slow.
          f_equal; auto.
          f_equal; auto.
          rw (sub_filter_disjoint1 sub); eauto 3 with slow.
      }

      exrepnd.

      remember (get_utok op') as guo; symmetry in Heqguo; destruct guo.

      { apply get_utok_some in Heqguo; subst; allsimpl.
        destruct bs''; allsimpl; cpx; GC; fold_terms.
        allrw subset_cons_l; repnd; allsimpl.
        exists (mk_utoken g); simpl; fold_terms; rw disjoint_singleton_l; dands; auto.
        unfold nrut_sub in nrut; repnd.
        apply nrut in ss0; sp.
      }

      { exists (oterm op' bs''); simpl; subst.
        allrw subset_app; repnd.
        allrw disjoint_app_l; dands; eauto 3 with slow.
        unfold lsubst_bterms_aux; auto.
        destruct op'; allsimpl; tcsp.
        destruct c; allsimpl; tcsp.
      }
Qed.

Lemma alpha_eq_subst_bterm_aux_pull_out_token {o} :
  forall b v a l (t : @NTerm o),
    !LIn v l
    -> !LIn v (bound_vars t)
    -> disjoint l (bound_vars t)
    -> no_repeats (bound_vars t)
    -> !LIn a (get_utokens_b b)
    -> wf_term t
    -> alpha_eq_bterm (subst_bterm_aux b v (mk_utoken a)) (bterm l t)
    -> {u : NTerm & t = subst u v (mk_utoken a) # !LIn a (get_utokens u)}.
Proof.
  introv ni1 ni2 disj1 norep niab wf aeq.

  pose proof (ex_change_bvars_bterm_alpha (v :: l ++ bound_vars t) b) as ch; exrepnd.
  allrw disjoint_cons_l; allrw disjoint_app_l; repnd.
  pose proof (lsubst_aux_alphabt_congr_cl b bt' [(v,mk_utoken a)] [(v,mk_utoken a)]) as aeqb.
  repeat (autodimp aeqb hyp); eauto with slow.
  eapply alpha_eq_bterm_trans in aeq;[|apply alpha_eq_bterm_sym; exact aeqb].
  assert (!LIn a (get_utokens_b bt')) as niabt'.
  { apply alpha_eq_bterm_preserves_utokens in ch0; rw <- ch0; auto. }
  clear dependent b; rename bt' into b.
  rename ch3 into disj2; rename ch2 into disj3; rename ch1 into ni3; rename niabt' into niab.

  destruct b as [l1 u1]; allsimpl.
  allrw disjoint_app_r; repnd.
  allunfold @subst_bterm_aux; allsimpl; boolvar.
  - allrw @lsubst_aux_nil.
    exists t.
    applydup @alpha_eq_bterm_preserves_utokens in aeq as eu; allsimpl; rw <- eu.
    apply alpha_eq_bterm_preserves_free_vars in aeq; allsimpl.
    rw @cl_subst_trivial; eauto with slow.
    introv i.
    assert (LIn v (remove_nvars l (free_vars t))) as j.
    { rw in_remove_nvars; sp. }
    rw <- aeq in j.
    rw in_remove_nvars in j; sp.
  - (* change the l1 into l when inverting aeq *)
    apply alpha_eq_bterm_sym in aeq.
    applydup @alpha_eq_bterm_lenbvars in aeq.
    apply alpha_eq_bterm_ren_1side2 in aeq; auto;
    [|introv i j; apply subset_bound_vars_lsubst_aux in j; allsimpl;
      allrw app_nil_r; apply disj2 in i; sp].
    rw @lsubst_lsubst_aux in aeq;
      [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
         rw @sub_free_vars_var_ren; auto;
         introv i j; apply subset_bound_vars_lsubst_aux in i; allsimpl;
         allrw app_nil_r; apply disj2 in j; sp].

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj u1 [(v,mk_utoken a)] (var_ren l1 l)) as h.
    allsimpl.
    rw @sub_free_vars_var_ren in h; auto.
    allrw disjoint_singleton_l; fold_terms.
    repeat (autodimp h hyp); eauto 3 with slow.
    rw <-  h in aeq; clear h.

    pose proof (alpha_eq_lsubst_aux_pull_out_token
                  t (get_utokens u1) [(v,mk_utoken a)]
                  (lsubst_aux u1 (sub_filter (var_ren l1 l) [v]))) as h.
    allsimpl; allrw disjoint_singleton_l.
    repeat (autodimp h hyp); eauto 3 with slow.

    { intro i; apply subset_bound_vars_lsubst_aux in i; allrw in_app_iff.
      rw @sub_bound_vars_allvars_sub in i; eauto 3 with slow.
      allsimpl; repndors; tcsp. }

    { introv i j; apply subset_bound_vars_lsubst_aux in j; allrw in_app_iff.
      rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
      allsimpl; repndors; tcsp.
      apply disj3 in i; sp. }

    { apply nrut_sub_cons; eexists; simpl; dands; eauto; tcsp; eauto with slow. }

    { rw @get_utokens_lsubst_aux_allvars; eauto with slow. }

    exrepnd; allsimpl.
    unfold get_utokens_sub in h0; allsimpl; allrw disjoint_singleton_r.
    exists u.
    unfsubst; dands; auto.
Qed.

Lemma alpha_eq_bterm_ren_1side3 {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (all_vars t2)
    -> length l1 = length l2
    -> no_repeats l1
    -> alpha_eq t1 (lsubst t2 (var_ren l2 l1))
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2).
Proof.
  introv disj1 len norep aeq.
  pose proof (fresh_vars (length l1) (l1 ++ l2
                                         ++ all_vars t1
                                         ++ all_vars t2))
    as fvs; exrepnd; allrw disjoint_app_r; repnd.
  apply (al_bterm _ _ lvn); allrw disjoint_app_r; auto.
  apply (lsubst_alpha_congr2 _ _ (var_ren l1 lvn)) in aeq.
  pose proof (lsubst_nest_vars_same t2 l2 l1 lvn) as h.
  repeat (autodimp h hyp); allrw disjoint_app_l; dands; auto.
  rw h in aeq; eauto with slow.
Qed.

Definition maybe_new_var_b {o} (v : NVar) (b : @BTerm o) :=
  match b with
    | bterm l t => maybe_new_var v l t
  end.

Lemma in_nrut_sub_eq {o} :
  forall (sub: @Sub o) v1 v2 t l,
    nrut_sub l sub
    -> LIn (v1, t) sub
    -> LIn (v2, t) sub
    -> v1 = v2.
Proof.
  induction sub; introv nrut ni1 ni2; allsimpl; tcsp.
  destruct a as [v u].
  allrw @nrut_sub_cons; exrepnd; subst.
  repndors; subst; tcsp; cpx.
  - destruct nrut2; rw lin_flat_map.
    apply in_sub_eta in ni1; repnd.
    eexists; dands; eauto; simpl; tcsp.
  - destruct nrut2; rw lin_flat_map.
    apply in_sub_eta in ni2; repnd.
    eexists; dands; eauto; simpl; tcsp.
  - eapply IHsub; eauto.
Qed.

Lemma eqset_preserves_null {T} :
  forall (s1 s2 : list T),
    eqset s1 s2
    -> null s1
    -> null s2.
Proof.
  introv eqs n i.
  apply eqs in i.
  apply n in i; sp.
Qed.

Lemma null_get_utokens_sub_keep_first_free_vars_eq {o} :
  forall l (t : @NTerm o) sub,
    nrut_sub l sub
    -> null (get_utokens_sub (sub_keep_first sub (free_vars t)))
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv nrut nu; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.
    unfold get_utokens_sub in nu.
    allrw @null_flat_map.
    applydup @sub_find_some in Heqsf.
    pose proof (nu n) as h; clear nu.
    eapply in_nrut_sub in nrut; eauto; exrepnd; subst; allsimpl.
    autodimp h hyp.

    + apply in_range_iff; exists v.
      apply in_sub_keep_first; simpl; tcsp.

    + pose proof (h a) as q; allsimpl; destruct q; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x as [vs t]; allsimpl.
    f_equal.
    eapply ind;[eauto| |]; eauto 3 with slow.
    introv j.
    allrw @in_get_utokens_sub; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allrw @sub_find_sub_filter_eq; boolvar; ginv.
    destruct (nu x).
    apply in_get_utokens_sub.
    exists v t0; dands; auto.
    apply in_sub_keep_first; dands; auto.
    apply lin_flat_map.
    eexists; dands; eauto.
    simpl; rw in_remove_nvars; sp.
Qed.

Lemma alpha_eq_lsubst_aux_nrut_sub_implies {o} :
  forall (t1 t2 : @NTerm o) sub l,
    nrut_sub l sub
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> disjoint (dom_sub sub) (bound_vars t1)
    -> disjoint (dom_sub sub) (bound_vars t2)
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub)
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv nrut ss1 ss2 disj1 disj2 aeq; allsimpl.

  - Case "vterm".
    remember (sub_find sub v1) as sf; symmetry in Heqsf; destruct sf.

    + apply sub_find_some in Heqsf.
      dup Heqsf as i.
      eapply in_nrut_sub in i; eauto; exrepnd; subst.
      destruct t2 as [v2|f2|op2 bs2]; allsimpl;
      try (complete (inversion aeq)).

      * remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

        { apply sub_find_some in Heqsf'.
          dup Heqsf' as j.
          eapply in_nrut_sub in j; eauto; exrepnd; subst.
          inversion aeq; subst; allsimpl; GC.
          apply (in_nrut_sub_eq sub v1 v2 (mk_utoken a0) l) in nrut; auto; subst; auto. }

        { inversion aeq. }

      * inversion aeq; subst; allsimpl; cpx; destruct bs2; allsimpl; cpx; GC; fold_terms.
        allrw singleton_subset; tcsp.

    + apply sub_find_none2 in Heqsf.
      destruct t2 as [v2|f2|op2 bs2]; allsimpl;
      try (complete (inversion aeq)).

      remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

      { apply sub_find_some in Heqsf'.
        dup Heqsf' as j.
        eapply in_nrut_sub in j; eauto; exrepnd; subst.
        inversion aeq. }

      { inversion aeq; subst; auto. }

  - Case "sterm".
    applydup @alphaeq_preserves_utokens in aeq; allsimpl.
    symmetry in aeq0; apply null_iff_nil in aeq0.
    eapply eqset_preserves_null in aeq0;[|apply get_utokens_lsubst_aux].
    allrw @null_app; repnd.
    erewrite null_get_utokens_sub_keep_first_free_vars_eq in aeq; eauto.

  - Case "oterm".
    allrw subset_app; repnd.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion aeq)).

    + remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

      { apply sub_find_some in Heqsf'.
        dup Heqsf' as j.
        eapply in_nrut_sub in j; eauto; exrepnd; subst.
        inversion aeq; subst; allsimpl; destruct bs1; allsimpl; cpx; GC; fold_terms.
        allrw singleton_subset; tcsp. }

      { inversion aeq. }

    + apply alpha_eq_oterm_combine2 in aeq; allrw map_length; repnd; subst.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      pose proof (aeq (lsubst_bterm_aux b1 sub) (lsubst_bterm_aux b2 sub)) as aeqb; clear aeq.
      rw <- @map_combine in aeqb.
      rw in_map_iff in aeqb.
      autodimp aeqb hyp.
      { eexists; dands; eauto. }
      applydup in_combine in i; repnd; disj_flat_map.
      destruct b1 as [l1 t1]; destruct b2 as [l2 t2]; allsimpl.
      allrw disjoint_app_r; repnd.
      allrw subset_app; repnd.

      repeat (rw @sub_filter_disjoint1 in aeqb; eauto 3 with slow).

      pose proof (fresh_vars
                    (length l1)
                    (all_vars (lsubst_aux t1 sub)
                              ++ all_vars (lsubst_aux t2 sub)
                              ++ dom_sub sub
                              ++ bound_vars t1
                              ++ bound_vars t2
                              ++ free_vars t1
                              ++ free_vars t2))
        as fvs; exrepnd; allrw disjoint_app_r; repnd.

      pose proof (alphabt_change_var_aux
                    (lsubst_aux t1 sub) (lsubst_aux t2 sub) l1 l2) lvn
        as a.
      allrw disjoint_app_r; repeat (autodimp a hyp); dands; eauto 3 with slow.
      repnd.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t1 sub (var_ren l1 lvn)) as e1.
      rw @sub_free_vars_var_ren in e1; auto.
      rw @cl_lsubst_aux_sub_trivial in e1; eauto 3 with slow.
      erewrite sub_bound_vars_nrut_sub in e1; eauto 3 with slow.
      erewrite sub_free_vars_nrut_sub in e1; eauto 3 with slow.
      rw @sub_filter_disjoint1 in e1;[|rw @dom_sub_var_ren; eauto with slow]; auto.
      repeat (autodimp e1 hyp); eauto 3 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t2 sub (var_ren l2 lvn)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try omega.
      rw @cl_lsubst_aux_sub_trivial in e2; eauto 3 with slow.
      erewrite sub_bound_vars_nrut_sub in e2; eauto 3 with slow.
      erewrite sub_free_vars_nrut_sub in e2; eauto 3 with slow.
      rw @sub_filter_disjoint1 in e2;[|rw @dom_sub_var_ren; eauto with slow]; auto; try omega.
      repeat (autodimp e2 hyp); eauto 3 with slow.

      rw <- e1 in a0; rw <- e2 in a0; clear e1 e2.

      pose proof (ind1 t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as q; clear ind1.
      repeat (autodimp q hyp).
      { rw @lsubst_aux_allvars_preserves_osize2; eauto 2 with slow. }
      pose proof (q (lsubst_aux t2 (var_ren l2 lvn)) sub l) as ih; clear q.
      repeat (rw @get_utokens_lsubst_aux_allvars in ih; eauto 3 with slow).
      repeat (rw @boundvars_lsubst_aux_vars in ih; auto; try omega).
      repeat (autodimp ih hyp); eauto 3 with slow.
      { introv z1; apply ss1; rw lin_flat_map; eexists; dands; eauto. }
      { introv z1; apply ss2; rw lin_flat_map; eexists; dands; eauto. }
      apply (al_bterm _ _ lvn); allrw disjoint_app_r; dands; auto.

      repeat (rw @lsubst_lsubst_aux); auto;
      rw <- @sub_free_vars_is_flat_map_free_vars_range;
      rw @computation2.sub_free_vars_var_ren; eauto 3 with slow; try omega.
Qed.

Lemma alpha_eq_bterm_mk_fresh_bterm_berm {o} :
  forall (b : @BTerm o) v a l t,
    disjoint l (all_vars_bterm b)
    -> disjoint l (bound_vars t)
    -> !LIn v l
    -> !LIn (maybe_new_var_b v b) l
    -> no_repeats l
    -> !LIn a (get_utokens t)
    -> !LIn a (get_utokens_b b)
    -> alpha_eq_bterm (subst_bterm_aux b v (mk_utoken a))
                      (bterm l (subst t v (mk_utoken a)))
    -> alpha_eq_bterm (mk_fresh_bterm v b) (bterm l (mk_fresh v t)).
Proof.
  introv disj1 disj2 ni1 ni2 norep nia1 nia2 aeqb.
  destruct b as [l' t'].
  unfold mk_fresh_bterm.
  apply alpha_eq_bterm_sym.
  allsimpl; allrw disjoint_app_r; repnd.
  applydup @alphaeqbt_numbvars in aeqb as len.
  unfold num_bvars in len; allsimpl.

  apply alpha_eq_bterm_sym in aeqb.
  unfold subst_bterm_aux in aeqb; allsimpl.
  apply alpha_eq_bterm_ren_1side2 in aeqb;
    [|unfold subst; rw @cl_lsubst_lsubst_aux; eauto 3 with slow;
      rw (@bound_vars_lsubst_aux_nrut_sub o t [(v,mk_utoken a)] []);
      eauto 3 with slow;
      apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp
     |boolvar; allrw @lsubst_aux_nil; auto;
      rw (@bound_vars_lsubst_aux_nrut_sub o t' [(v,mk_utoken a)] []);
      eauto 3 with slow;
      apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp].

  apply alpha_eq_bterm_ren_1side3; auto.
  { unfold all_vars; simpl; allrw app_nil_r.
    allrw disjoint_app_r; allrw disjoint_cons_r; dands; auto.
    apply disjoint_remove_nvars_weak_r; auto. }

  rw @lsubst_lsubst_aux; simpl; fold_terms;
  [|rw app_nil_r; rw <- @sub_free_vars_is_flat_map_free_vars_range;
    rw @sub_free_vars_var_ren; auto;
    apply disjoint_cons_l; dands; complete (eauto with slow)].

  allunfold @maybe_new_var.
  boolvar.

  - allrw @lsubst_aux_nil.
    assert (!LIn v (free_vars t)) as nivt.
    { intro i; apply alphaeq_preserves_utokens in aeqb.
      rw (get_utokens_lsubst_allvars t') in aeqb; eauto 3 with slow.
      rw <- aeqb in nia2; destruct nia2.
      apply get_utokens_lsubst; rw in_app_iff; sp; simpl.
      boolvar; tcsp. }
    rw @cl_subst_trivial in aeqb; eauto 3 with slow.
    rw @lsubst_aux_sub_filter_aux; simpl;
    [|introv i j; repndors; tcsp; subst;
      rw @dom_sub_var_ren; auto;
      apply newvar_prop in i; complete sp].

    dup aeqb as aeq.
    apply (implies_alpha_eq_mk_fresh v) in aeqb.
    rw <- @lsubst_lsubst_aux;
      [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
         rw @sub_free_vars_var_ren; complete (eauto with slow)].
    eapply alpha_eq_trans;[exact aeqb|].

    pose proof (ex_fresh_var (all_vars (lsubst t' (var_ren l' l)))) as fv; exrepnd.
    apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; allrw not_over_or; repnd; tcsp.
    repeat (rw (lsubst_trivial3 (lsubst t' (var_ren l' l)))); auto.

    { introv i; apply in_var_ren in i; allsimpl; exrepnd; repndors; tcsp; subst; allsimpl.
      rw disjoint_singleton_l; dands; auto.
      intro j.
      pose proof (eqvars_free_vars_disjoint t' (var_ren l' l)) as e.
      rw eqvars_prop in e; apply e in j; clear e.
      rw @dom_sub_var_ren in j; auto.
      rw in_app_iff in j; rw in_remove_nvars in j; repndors; exrepnd; tcsp.
      - apply newvar_prop in j0; sp.
      - apply in_sub_free_vars in j; exrepnd.
        apply in_sub_keep_first in j0; repnd.
        apply sub_find_some in j2.
        apply in_var_ren in j2; exrepnd; subst; allsimpl; repndors; tcsp; subst; tcsp.
    }

    { introv i; apply in_var_ren in i; allsimpl; exrepnd; repndors; tcsp; subst; allsimpl.
      rw disjoint_singleton_l; dands; auto.
      intro j.
      pose proof (eqvars_free_vars_disjoint t' (var_ren l' l)) as e.
      rw eqvars_prop in e; apply e in j; clear e.
      rw @dom_sub_var_ren in j; auto.
      rw in_app_iff in j; rw in_remove_nvars in j; repndors; exrepnd; tcsp.
      apply in_sub_free_vars in j; exrepnd.
      apply in_sub_keep_first in j0; repnd.
      apply sub_find_some in j2.
      apply in_var_ren in j2; exrepnd; subst; allsimpl; repndors; tcsp; subst; tcsp.
    }

  - rw @lsubst_lsubst_aux in aeqb;
    [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_var_ren; try (complete (eauto 3 with slow));
       rw (@bound_vars_lsubst_aux_nrut_sub o t' [(v,mk_utoken a)] []);
       eauto 3 with slow;
       apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp].

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                  t' [(v,mk_utoken a)] (var_ren l' l)) as e; allsimpl.
    allrw disjoint_singleton_l.
    rw @sub_free_vars_var_ren in e; try (complete (eauto 3 with slow)).
    repeat (autodimp e hyp); eauto 2 with slow; fold_terms.
    rw <- e in aeqb; clear e.
    apply implies_alpha_eq_mk_fresh.
    remember (lsubst_aux t' (sub_filter (var_ren l' l) [v])) as t''.
    unfold subst in aeqb; rw @cl_lsubst_lsubst_aux in aeqb; eauto 2 with slow.

    assert (!LIn a (get_utokens t'')) as niat''.
    { subst; intro i.
      apply get_utokens_lsubst_aux in i; allrw in_app_iff; repndors; tcsp.
      rw @get_utokens_sub_allvars_sub in i; allsimpl; eauto with slow.
    }

    clear Heqt''.

    pose proof (change_bvars_alpha_wspec [v] t) as aeqt; exrepnd.
    pose proof (change_bvars_alpha_wspec [v] t'') as aeqt'; exrepnd.
    allrw disjoint_singleton_l.

    assert (alpha_eq (lsubst_aux t [(v, mk_utoken a)])
                     (lsubst_aux ntcv [(v, mk_utoken a)])) as aeq1.
    { apply computation2.lsubst_aux_alpha_congr_same_cl_sub; eauto 3 with slow. }

    assert (alpha_eq (lsubst_aux t'' [(v, mk_utoken a)])
                     (lsubst_aux ntcv0 [(v, mk_utoken a)])) as aeq2.
    { apply computation2.lsubst_aux_alpha_congr_same_cl_sub; eauto 3 with slow. }

    assert (alpha_eq (lsubst_aux ntcv [(v, mk_utoken a)])
                     (lsubst_aux ntcv0 [(v, mk_utoken a)])) as aeq3.
    { eapply alpha_eq_trans;[apply alpha_eq_sym; exact aeq1|].
      eapply alpha_eq_trans;[exact aeqb|].
      eauto with slow. }
    clear aeq1 aeq2.

    assert (alpha_eq ntcv ntcv0) as aeq;[|eauto 4 with slow];[].

    apply (alpha_eq_lsubst_aux_nrut_sub_implies
             _ _ _ (get_utokens ntcv ++ get_utokens ntcv0)) in aeq3;
      simpl; eauto 3 with slow; allrw disjoint_singleton_l; auto.

    apply alphaeq_preserves_utokens in aeqt0.
    apply alphaeq_preserves_utokens in aeqt'0.
    rw aeqt0 in nia1.
    rw aeqt'0 in niat''.
    apply nrut_sub_cons; eexists; dands; simpl; eauto; tcsp; eauto 3 with slow.
    rw in_app_iff; tcsp.
Qed.

Lemma alpha_eq_bterm_preserves_isprog_vars {o} :
  forall l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> isprog_vars l1 t1
    -> isprog_vars l2 t2.
Proof.
  introv aeq isp.
  allrw @isprog_vars_eq; repnd.
  applydup @alphaeqbt_preserves_nt_wf in aeq as w.
  rw w; dands; auto.
  apply alphaeqbt_preserves_fvars in aeq; allsimpl.
  rw eqvars_prop in aeq.
  allrw subvars_prop.
  introv i.
  destruct (in_deq _ deq_nvar x l2) as [d|d]; auto.
  assert (LIn x (remove_nvars l2 (free_vars t2))) as j.
  { rw in_remove_nvars; sp. }
  apply aeq in j.
  rw in_remove_nvars in j; repnd.
  apply isp0 in j0; sp.
Qed.

Lemma approx_starbts_get_bterms_alpha_eq_l {o} :
  forall lib op (t u v : @NTerm o),
    approx_starbts lib op (get_bterms t) (get_bterms u)
    -> alpha_eq t v
    -> approx_starbts lib op (get_bterms v) (get_bterms u).
Proof.
  introv ap aeq.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl; auto;
  try (complete (inversion aeq; subst; allsimpl; auto)).
  - unfold approx_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_starbts, lblift_sub; simpl; sp.
  - unfold approx_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_starbts, lblift_sub; simpl; sp.
  - inversion aeq as [|?|? ? ? len imp]; subst; simpl.
    allunfold @approx_starbts.
    allunfold @lblift_sub; repnd; dands; auto; try omega.
    introv i.
    pose proof (ap n) as h1; autodimp h1 hyp; try omega.
    pose proof (imp n) as h2; autodimp h2 hyp; try omega.
    eapply approx_star_bterm_alpha_fun_l;[apply alpha_eq_bterm_sym; exact h2|]; auto.
Qed.

Lemma subst_sterm {o} :
  forall (f : @ntseq o) v t,
    subst (sterm f) v t = sterm f.
Proof.
  introv; unfold subst; autorewrite with slow; auto.
Qed.
Hint Rewrite @subst_sterm : slow.

Lemma same_value_like_sterm_implies_approx_star {o} :
  forall lib (f1 f2 : @ntseq o),
    nt_wf (sterm f2)
    -> same_value_like (sterm f1) (sterm f2)
    -> approx_star lib (sterm f1) (sterm f2).
Proof.
  introv wf svl.
  inversion svl; subst; clear svl.
  econstructor; eauto.
  apply approx_open_refl; auto.
Qed.
Hint Resolve same_value_like_sterm_implies_approx_star : slow.

Lemma approx_star_pushdown_fresh_if_subst {o} :
  forall lib (t1 t2 : @NTerm o) v1 v2 a,
    !LIn a (get_utokens t1)
    -> !LIn a (get_utokens t2)
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> same_value_like (subst t1 v1 (mk_utoken a)) (subst t2 v2 (mk_utoken a))
    -> approx_starbts lib (get_op t1) (get_bterms (subst t1 v1 (mk_utoken a))) (get_bterms (subst t2 v2 (mk_utoken a)))
    -> approx_star lib (pushdown_fresh v1 t1) (pushdown_fresh v2 t2).
Proof.
  introv ni1 ni2 isp1 isp2 svl ap.

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

  applydup @alpha_eq_bterm_preserves_utokens in aeqbt1 as ut1; allsimpl.
  rw ut1 in ni1.
  applydup @alpha_eq_bterm_preserves_utokens in aeqbt2 as ut2; allsimpl.
  rw ut2 in ni2.

  pose proof (lsubst_alpha_congr4 [v1] [v] t1 nt1 [(v1,mk_utoken a)] [(v,mk_utoken a)]) as c1.
  allsimpl.
  repeat (autodimp c1 hyp); eauto 3 with slow.

  pose proof (lsubst_alpha_congr4 [v2] [v] t2 nt2 [(v2,mk_utoken a)] [(v,mk_utoken a)]) as c2.
  allsimpl.
  repeat (autodimp c2 hyp); eauto 3 with slow.

  allrw @fold_subst.

  eapply same_value_like_alpha_eq_r in svl;[|exact c2].
  eapply same_value_like_alpha_eq_l in svl;[|exact c1].

  eapply alpha_eq_bterm_preserves_isprog_vars in isp1;[|exact aeqbt1].
  eapply alpha_eq_bterm_preserves_isprog_vars in isp2;[|exact aeqbt2].

  assert (get_op t1 = get_op nt1) as go.
  { subst; rw @lsubst_lsubst_aux; allrw <- @sub_free_vars_is_flat_map_free_vars_range;
    allsimpl; allrw disjoint_singleton_r; auto.
    destruct t1; simpl; boolvar; simpl; tcsp. }
  rw go in ap.

  eapply approx_starbts_get_bterms_alpha_eq in ap;[|exact c2].
  eapply approx_starbts_get_bterms_alpha_eq_l in ap;[|exact c1].

  applydup @implies_alpha_eq_pushdown_fresh in aeqbt1 as apf1.
  applydup @implies_alpha_eq_pushdown_fresh in aeqbt2 as apf2.

  eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact apf1].
  eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact apf2].

  clear dependent t1.
  clear dependent t2.
  rename nt1 into t1.
  rename nt2 into t2.

  repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.
  destruct t1 as [x|f|op bs]; allsimpl; tcsp; GC.

  - boolvar.

    + apply approx_open_implies_approx_star.
      apply approx_implies_approx_open.
      apply (approx_trans _ _ (mk_fresh x (mk_var x))).

      * apply reduces_to_implies_approx2.
        { apply isprogram_fresh.
          apply isprog_vars_var. }
        apply reduces_to_if_step.
        csunf; simpl; boolvar; auto.

      * apply fresh_id_approx_any.
        apply isprogram_pushdown_fresh; auto.

    + inversion svl.

  - autorewrite with slow in *.
    destruct t2 as [v2|f2|op bs]; allsimpl; boolvar; allsimpl;
    try (complete (inversion svl)); eauto 4 with slow.

  - allsimpl.
    destruct t2 as [x|f|op' bs']; allsimpl; GC; try (complete (inversion svl)).

    + boolvar; try (complete (inversion svl)).
      inversion svl; subst; allsimpl.
      allrw not_over_or; sp.

    + applydup @same_value_like_implies_same_op in svl; subst.

      assert (length bs = length bs') as e.
      {  unfold approx_starbts, lblift_sub in ap; repnd; allrw map_length.
         unfold mk_fresh_bterms; allrw map_length; auto. }

      apply (apso _ _ _ _ (mk_fresh_bterms v bs')); auto;
      try (apply approx_open_refl);
      [unfold mk_fresh_bterms; allrw map_length; auto
       |idtac
       |apply isprog_vars_eq in isp2; repnd;
       allrw @nt_wf_oterm_iff; repnd;
       rw <- isp3;
       unfold mk_fresh_bterms; allrw map_map; unfold compose; dands;
       [ apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto|];
       introv i; allrw in_map_iff; exrepnd; subst;
       apply isp2 in i1; apply bt_wf_mk_fresh_bterm_if; complete auto].

      unfold lblift_sub, mk_fresh_bterms; dands; allrw map_length; auto.
      introv i.
      repeat (rw @selectbt_map; auto; try omega).
      unfold approx_starbts, lblift_sub in ap; repnd; allrw map_length; GC.
      pose proof (ap n i) as k; clear ap.
      repeat (rw @selectbt_map in k; auto; try omega).
      allunfold @selectbt.

      pose proof (in_nth_combine _ _ bs bs' n default_bt default_bt) as h.
      repeat (autodimp h hyp).
      remember (nth n bs default_bt)  as b1; clear Heqb1.
      remember (nth n bs' default_bt) as b2; clear Heqb2.
      allrw in_app_iff; allrw not_over_or; repnd.
      applydup in_combine in h; repnd.
      assert (!LIn a (get_utokens_b b1)) as niab1.
      { introv q; destruct ni1; rw lin_flat_map; eexists; dands; eauto. }
      assert (!LIn a (get_utokens_b b2)) as niab2.
      { introv q; destruct ni2; rw lin_flat_map; eexists; dands; eauto. }

(* new stuff *)

      apply (blift_sub_diff (v :: maybe_new_var_b v b1
                               :: maybe_new_var_b v b2
                               :: all_vars_bterm b1
                               ++ all_vars_bterm b2)) in k; exrepnd.
      allrw disjoint_cons_r; allrw disjoint_cons_l; allrw disjoint_app_r; allrw disjoint_app_l; repnd.

      assert (wf_term nt1) as wfnt1.
      { repndors; exrepnd.
        - allapply @approx_star_relates_only_wf; repnd; eauto 2 with slow.
        - allapply @approx_star_relates_only_wf; repnd.
          allapply @lsubst_nt_wf; eauto with slow. }

      assert (wf_term nt2) as wfnt2.
      { repndors; exrepnd.
        - allapply @approx_star_relates_only_wf; repnd; eauto 2 with slow.
        - allapply @approx_star_relates_only_wf; repnd.
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
      { introv i1 i2; apply k7 in i1; destruct i1.
        unfsubst.
        rw (bound_vars_lsubst_aux_nrut_sub nt1 [(v,mk_utoken a)] []); auto.
        apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp. }

      assert (disjoint lv (bound_vars nt2)) as disjlvnt2.
      { introv i1 i2; apply k8 in i1; destruct i1.
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
        [|apply approx_open_refl; allrw <- @nt_wf_eq;
          allapply @lsubst_nt_wf; apply nt_wf_fresh; auto].
        unfold lblift_sub; simpl; dands; auto; introv q; destruct n0; cpx.
        unfold selectbt; simpl.
        unfold blift_sub.

        exists [v] nt1 nt2; dands; auto.
        right.
        exists [(v,mk_utoken a)]; simpl; dands; auto.
        apply nrut_sub_cons; simpl; eexists; dands; eauto with slow; tcsp.
        rw in_app_iff; sp.

      * exrepnd.

        pose proof (exists_nrut_sub
                      (dom_sub sub)
                      (a :: get_utokens (subst nt1 v (mk_utoken a))
                         ++ get_utokens (subst nt2 v (mk_utoken a))))
          as ens; exrepnd.

        pose proof (approx_star_change_nrut_sub
                      lib
                      (subst nt1 v (mk_utoken a))
                      (subst nt2 v (mk_utoken a))
                      sub
                      (get_utokens (subst nt1 v (mk_utoken a)) ++ get_utokens (subst nt2 v (mk_utoken a)))
                      sub0
                      (a :: get_utokens (subst nt1 v (mk_utoken a)) ++ get_utokens (subst nt2 v (mk_utoken a))))
          as aps; repeat (autodimp aps hyp); eauto 3 with slow.

        exists sub0; dands; auto; simpl; allrw app_nil_r;
        try (complete (subst; auto));
        [|eapply nrut_sub_subset;[|exact ens1]; apply subset_cons1;
          apply subset_app_lr; introv z;
          apply get_utokens_subst; boolvar; simpl;
          repeat (rw app_nil_r); repeat (rw in_app_iff); complete sp].
        repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow); simpl; fold_terms.
        apply (apso _ _ _ _ [bterm [v] (lsubst_aux nt2 (sub_filter sub0 [v]))]); allsimpl; auto; fold_terms;
        [|apply approx_open_refl; allrw <- @nt_wf_eq;
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
        apply nrut_sub_cons; simpl; eexists; dands; eauto with slow; tcsp.
        rw in_app_iff; rw not_over_or; dands; intro z;
        apply get_utokens_lsubst_aux_subset in z; rw in_app_iff in z; repndors; tcsp;
        apply get_utokens_sub_filter_subset in z; tcsp.
Qed.

Lemma alpha_eq_lsubst_nrut_sub_implies {o} :
  forall (t1 t2 : @NTerm o) sub l,
    nrut_sub l sub
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> alpha_eq (lsubst t1 sub) (lsubst t2 sub)
    -> alpha_eq t1 t2.
Proof.
  introv nrut ss1 ss2 aeq.

  pose proof (unfold_lsubst sub t1) as p; destruct p as [t1']; repnd.
  pose proof (unfold_lsubst sub t2) as q; destruct q as [t2']; repnd.
  rw p in aeq; rw p2 in aeq.

  pose proof (change_bvars_alpha_wspec (dom_sub sub) t1') as h; destruct h as [t1'']; repnd.
  pose proof (change_bvars_alpha_wspec (dom_sub sub) t2') as k; destruct k as [t2'']; repnd.
  dup p5 as a1.
  apply (computation2.lsubst_aux_alpha_congr_same_cl_sub _ _ sub) in a1; eauto 2 with slow.
  dup p7 as a2.
  apply (computation2.lsubst_aux_alpha_congr_same_cl_sub _ _ sub) in a2; eauto 2 with slow.

  assert (alpha_eq (lsubst_aux t1'' sub) (lsubst_aux t2'' sub)) as aeq2 by eauto 4 with slow.

  pose proof (alpha_eq_lsubst_aux_nrut_sub_implies t1'' t2'' sub l) as a.
  repeat (autodimp a hyp).
  - apply alphaeq_preserves_utokens in p5; rw <- p5.
    apply alphaeq_preserves_utokens in p0; rw <- p0; auto.
  - apply alphaeq_preserves_utokens in p7; rw <- p7.
    apply alphaeq_preserves_utokens in p3; rw <- p3; auto.
  - assert (alpha_eq t1 t1'') as aeq11 by eauto with slow.
    assert (alpha_eq t2 t2'') as aeq22 by eauto with slow.
    eauto with slow.
Qed.

Lemma reduces_in_atmost_k_steps_mk_fresh_id {o} :
  forall (lib : @library o) v k u,
    reduces_in_atmost_k_steps lib (mk_fresh v (vterm v)) u k
    -> u = mk_fresh v (vterm v).
Proof.
  induction k; introv r.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; allsimpl; boolvar; ginv.
    apply IHk in r0; auto.
Qed.

Lemma reduces_in_atmost_k_steps_mk_fresh_id2 {o} :
  forall (lib : @library o) v k,
    reduces_in_atmost_k_steps lib (mk_fresh v (vterm v)) (mk_fresh v (vterm v)) k.
Proof.
  induction k; introv.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    exists (@mk_fresh o v (vterm v)); dands; auto.
    csunf; simpl; boolvar; auto.
Qed.

Lemma isprog_vars_implies_nt_wf {o} :
  forall (t : @NTerm o) l, isprog_vars l t -> nt_wf t.
Proof.
  introv isp.
  rw @isprog_vars_eq in isp; sp.
Qed.
Hint Resolve isprog_vars_implies_nt_wf : slow.

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

  assert (isvalue_like (subst u v (mk_utoken (get_fresh_atom t)))) as isv.
  { apply isvalue_like_subst; auto. }
  assert (isvalue_like x) as isvx.
  { apply alpha_eq_sym in Hcv5; apply alpha_eq_preserves_isvalue_like in Hcv5; auto. }

  remember (get_fresh_atom t) as ua.
  apply isprogram_fresh in Hprt'.
  pose proof (fresh_atom p (get_utokens (mk_pair t tr))) as fa.
  destruct fa as [ua' fa]; allsimpl; allrw app_nil_r.
  allrw in_app_iff; allrw not_over_or; repnd.
  pose proof (get_fresh_atom_prop t) as gfu; rw <- Hequa in gfu.

  apply no_change_after_val_like with (k2 := k) in Hcv4; auto.
  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k t x [(v,mk_utoken ua)] [(v,mk_utoken ua')]) as comp.
  repeat (autodimp comp hyp); eauto 2 with slow.
  { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; auto. }
  { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; auto. }
  exrepnd; allrw @fold_subst.
  unfold get_utokens_sub in comp2; simpl in comp2; allrw disjoint_singleton_l.

  assert (isprogram (subst w0 v (mk_utoken ua))) as ispsw0.
  { apply alphaeq_preserves_program in comp0; apply comp0; auto. }
  assert (isprogram s) as isps.
  { apply alpha_eq_sym in comp1; apply alphaeq_preserves_program in comp1; apply comp1.
    apply isprogram_subst_if_bt; eauto 2 with slow.
    apply isprogram_subst_implies in ispsw0; auto. }

  assert (!LIn ua (get_utokens u)) as niu.
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
    { intro j; destruct niu; apply alphaeq_preserves_utokens in k3; rw k3; auto. }
    { intro j; destruct comp2; apply alphaeq_preserves_utokens in k0; rw k0; auto. }
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
                  (get_utokens nt1 ++ get_utokens nt2)
                  [(v',mk_utoken ua')]
                  (get_utokens nt1 ++ get_utokens nt2)) as q.
    allsimpl; repeat (autodimp q hyp); eauto 3 with slow.
    apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp.
    apply alpha_eq_bterm_preserves_utokens in Has0bt2.
    apply alpha_eq_bterm_preserves_utokens in Has0bt0.
    allsimpl; rw <- Has0bt2; rw <- Has0bt0; rw in_app_iff; sp.
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
  repeat (autodimp comp' hyp); eauto 2 with slow;
    try (unfold get_utokens_sub; simpl; apply disjoint_singleton_l; complete sp).
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

  assert (!LIn ua' (get_utokens u)) as niua'u.
  { intro i; apply Hcv6 in i; sp. }

  assert (get_op (subst u v (mk_utoken ua')) = get_op u) as gopu.
  { unfsubst; unfold isvalue_like in Hcv0; repndors.
    - apply iscan_implies in Hcv0; repndors; exrepnd; subst; simpl; auto.
    - apply isexc_implies2 in Hcv0; exrepnd; subst; simpl; auto. }

  rw gopu in ap3.

  pose proof (approx_star_pushdown_fresh_if_subst lib u w1 v vr ua') as apspf.
  repeat (autodimp apspf hyp).

  eapply approx_star_open_trans;[exact apspf|].

  apply approx_implies_approx_open.

  remember (get_fresh_atom tr) as a.

  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k0 tr v0 [(vr,mk_utoken ua')] [(vr,mk_utoken a)]) as r.
  allsimpl; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
  allsimpl; allrw disjoint_singleton_l.
  repeat (autodimp r hyp); eauto 3 with slow.
  { apply nr_ut_sub_cons; eauto with slow; intro xx; subst; apply get_fresh_atom_prop. }
  { subst; apply get_fresh_atom_prop. }
  exrepnd.

  allrw @fold_subst.
  pose proof (alpha_eq_lsubst_nrut_sub_implies
                w1 w2 [(vr,mk_utoken ua')]
                (get_utokens w1 ++ get_utokens w2)) as aeqws.
  repeat (autodimp aeqws hyp); eauto 3 with slow.
  { apply nrut_sub_cons; simpl; eexists; dands; eauto with slow; tcsp; rw in_app_iff; sp. }

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

  assert (!LIn a (get_utokens w1)) as niaw1.
  { intro xx.
    apply alphaeq_preserves_utokens in aeqws; rw aeqws in xx; apply r4 in xx.
    subst; apply get_fresh_atom_prop in xx; tcsp. }

  pose proof (simple_alphaeq_subst_utokens_subst w1 vr a niaw1) as aeq3.

  assert (alpha_eq z w1) as aeq4 by eauto 3 with slow.

  apply (approx_trans _ _ (mk_fresh vr z));
    [|apply reduces_to_implies_approx_eauto; auto;
      apply isprogram_fresh; complete auto].

  eapply approx_alpha_rw_r_aux;
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
    - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
      destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
    - destruct u as [z11|f11|op11 bs11]; allsimpl; boolvar; tcsp; ginv.
      destruct w1 as [z22|f22|op22 bs22]; allsimpl; boolvar; GC; tcsp; ginv; eauto 3 with slow.
  }

  pose proof (compute_step_fresh_if_isvalue_like lib vr w1 isvlw1) as comp.
  apply reduces_to_implies_approx_eauto;
    [apply isprogram_fresh; complete auto|].
  apply reduces_to_if_step; auto.
Qed.

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
    destruct t as [z|f|op bts]; ginv;[].
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

Lemma extensional_parallel {p} : extensional_op (@NCan p NParallel).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  apply computes_to_val_like_in_max_k_steps_parallel_implies2 in Hcv; exrepnd; ginv.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  destruct lbt'; allsimpl; cpx.
  pose proof (Has 0) as h; autodimp h hyp; try omega.
  unfold selectbt in h; allsimpl.
  unfold blift_sub in h; exrepnd; destruct h1 as [h1|h1]; exrepnd; ginv.
  allapply @alpha_eq_bterm_nobnd; exrepnd; allunfold @nobnd; ginv.
  destruct b as [l t].
  apply alpha_eq_bterm_sym in h0; allapply @alpha_eq_bterm_nobnd; exrepnd; allunfold @nobnd; ginv.
  apply isprogram_parallel_implies in Hprt; exrepnd; ginv; allsimpl; cpx.
  apply isprogram_parallel_implies in Hprt'; exrepnd; ginv.

  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv3; auto.
  applydup @alphaeq_preserves_program in h2 as isp1.
  applydup @alphaeq_preserves_program in h4 as isp2.
  applydup isp1 in Hprt'2.
  applydup isp2 in Hprt2.

  pose proof (Hi a0 x nt2) as q.
  repeat (autodimp q hyp).
  { eauto 3 with slow. }

  assert (approx_star lib x a1) as apr by eauto 3 with slow.

  repndors; exrepnd; subst; allsimpl.

  - apply howe_lemma2 in apr; auto; exrepnd.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply (reduces_to_trans _ _ (mk_parallel (oterm (Can c) lbt') b0)).
    { apply reduces_to_prinarg; auto; destruct apr0; auto. }
    { apply reduces_to_if_step; reflexivity. }

  - apply isexc_implies in Hcv2; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in apr; auto; exrepnd.
    apply (approx_star_open_trans _ _ (mk_exception a' e')).
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply (reduces_to_trans _ _ (mk_parallel (mk_exception a' e') b0)).
    { apply reduces_to_prinarg; auto. }
    { apply reduces_to_if_step; reflexivity. }
Qed.

Theorem nuprl_extensional {p} : forall op, @extensional_op p op.
  (* begin show *)
Proof.
  intro op. destruct op.
  - apply nuprl_extensional_can.
  - dopid_noncan n Case.
    + Case "NApply";    apply extensional_apply.
    + Case "NEApply";   apply extensional_eapply.
(*    + Case "NApseq";    apply extensional_apseq.*)
    + Case "NFix";      apply extensional_fix.
    + Case "NSpread";   apply extensional_spread.
    + Case "NDsup";     apply extensional_dsup.
    + Case "NDecide";   apply extensional_decide.
    + Case "NCbv";      apply extensional_cbv.
    + Case "NSleep";    apply extensional_sleep.
    + Case "NTUni";     apply extensional_tuni.
    + Case "NMinus";    apply extensional_minus.
    + Case "NFresh";    apply extensional_fresh.
    + Case "NTryCatch"; apply extensional_trycatch.
    + Case "NParallel"; apply extensional_parallel.
    + Case "NCompOp";   apply extensional_ncomp.
    + Case "NArithOp";  apply extensional_arith.
    + Case "NCanTest";  apply extensional_cantest.
  - apply nuprl_extensional_exc.
  - apply nuprl_extensional_abs.
Qed.

(* end show *)

(** %\noindent \\*% As we mentioned above, Howe
    abstracted the  extensionality condition above out
    of the proof of the following lemma.
    Hence its proof follows directly
    from the lemma [nuprl_extensional].

*)
Lemma howe_lemma3 {p} : forall lib (a a' b : @NTerm p),
  isprogram a
  -> isprogram a'
  -> isprogram b
  -> computes_to_val_like lib a a'
  -> approx_star lib a b
  -> approx_star lib a' b.
Proof.
  introv Hpra Hpra' Hprb Hc Hs.
  repnud Hc; exrepnd.
  revert a a' b Hpra Hpra' Hprb Hc0 Hs.
  induction k as [| k Hind]; introv Hpra Hpra' Hprb comp ap.

  - unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
    simpl in comp0; inversion comp0; subst; auto.

  - destruct a as [|f|o lba]; [inversion Hpra as [c w]; inversion c| |].

    + apply howe_lemma2_seq in ap; auto; exrepnd.
      apply computes_to_val_like_in_max_k_steps_if_isvalue_like in comp;
        eauto 2 with slow; subst.
      econstructor;[eauto|].
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx1; auto.

    + pose proof (@nuprl_extensional p) as Hex.
      applydup @approx_star_otd in ap; auto; []; exrepnd.
      unfold extensional_op in Hex.
      apply Hex with (lbt' := lbt') in comp; auto.
      eapply approx_star_open_trans; eauto.
Qed.

Lemma howe_lemma3_val {p} :
  forall lib (a a' b : @NTerm p),
    isprogram a
    -> isprogram a'
    -> isprogram b
    -> computes_to_value lib a a'
    -> approx_star lib a b
    -> approx_star lib a' b.
Proof.
  introv ispa ispa' ispb comp ap.
  apply @howe_lemma3 with (a := a); auto.
  apply computes_to_value_implies_val_like; auto.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma computes_to_marker_implies_val_like {p} :
  forall lib (a : @NTerm p) m,
    computes_to_marker lib a m
    -> computes_to_val_like lib a (mk_marker m).
Proof.
  introv comp.
  unfold computes_to_val_like, computes_to_val_like_in_max_k_steps.
  unfold computes_to_marker, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  right.
  constructor.
Qed.
*)

Lemma howe_lemma3_exc {p} :
  forall lib en (a a' b : @NTerm p),
    isprogram en
    -> isprogram a
    -> isprogram a'
    -> isprogram b
    -> computes_to_exception lib en a a'
    -> approx_star lib a b
    -> approx_star lib (mk_exception en a') b.
Proof.
  introv ispa ispa' ispb comp ap.
  apply @howe_lemma3 with (a := a); auto.
  apply isprogram_exception; auto.
  apply computes_to_exception_implies_val_like; auto.
Qed.

Lemma computes_to_seq_implies_computes_to_val_like {o} :
  forall lib (a : @NTerm o) f,
    (a =s>(lib) f)
    -> computes_to_val_like lib a (sterm f).
Proof.
  introv comp.
  unfold computes_to_seq, reduces_to in comp; exrepnd.
  unfold computes_to_val_like.
  exists k.
  unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_seq_implies_computes_to_val_like : slow.

Lemma howe_lemma3_seq {o} :
  forall lib (a b : @NTerm o) f,
    isprogram a
    -> isprogram b
    -> isprogram (sterm f)
    -> (a =s>(lib) f)
    -> approx_star lib a b
    -> approx_star lib (sterm f) b.
Proof.
  introv ispa ispa' ispb comp ap.
  apply @howe_lemma3 with (a := a); eauto 3 with slow.
Qed.

(*
Lemma howe_lemma3_mrk {p} :
  forall lib (a b : @NTerm p) m,
    isprogram a
    -> isprogram b
    -> computes_to_marker lib a m
    -> approx_star lib a b
    -> approx_star lib (mk_marker m) b.
Proof.
  introv ispa ispb comp ap.
  apply @howe_lemma3 with (a := a); auto; [apply isprogram_marker|].
  apply computes_to_marker_implies_val_like; auto.
Qed.
*)

(* begin hide *)

Lemma alphaeq_preserves_wf_r_eauto {p} :
  forall t1 t2 : @NTerm p, alpha_eq t1 t2 -> nt_wf t1 -> nt_wf t2.
Proof.
  introv Hal Hw. apply alphaeq_preserves_wf in Hal.
  destruct Hal.
  auto.
Qed.

Lemma alphaeqbt_preserves_prog_r_eauto {p} :
  forall t1 t2 : @BTerm p, alpha_eq_bterm t1 t2 -> isprogram_bt t1 -> isprogram_bt t2.
Proof.
  introv Hal Hw. allunfold @isprogram_bt. allunfold @closed_bt. exrepnd. dands.
  - apply alphaeqbt_preserves_fvars in Hal. rw Hw0 in Hal.
    apply eq_vars_nil in Hal; sp.
  - apply alphaeqbt_preserves_wf in Hal; destruct Hal.  sp.
Qed.

Hint Resolve alphaeqbt_preserves_prog_r_eauto : slow.

Lemma isprogam_bt_nt_wf_eauto {p} :
  forall (lv : list NVar) (nt : @NTerm p), isprogram_bt (bterm lv nt) -> nt_wf nt.
Proof.
  introv Hb.
  repnud Hb.
  apply bt_wf_iff in Hb; sp.
Qed.

Theorem howetheorem1_aux {p}:
  forall lib,
    (fun a b => @approx_star p lib a b # isprogram a # isprogram b)
    =2> (approx lib).
Proof.
  intro lib.
  apply approx_acc.
  introv Cb Cih. intros a b Has.
  exrepnd.
  constructor.
  unfold close_comput.
  dands; spcf.

  - introv hcv.
    applydup @preserve_program in hcv; sp;[].
    apply @howe_lemma3_val with (b:=b) in hcv; sp;[].
    apply howe_lemma2 in hcv;exrepnd; spc;[].
    exists lbt'; dands;sp.
    unfold approx_starbts in hcv2.
    allunfold @lblift_sub.
    exrepnd.
    split; spcf.
    introv Hlt.
    applydup hcv2 in Hlt.
    unfold blift.
    invertsna Hlt0 Hbas.
    exrepnd; repndors; exrepnd; ginv.
    exists x nt1 nt2.
    dands; sp.
    unfold olift.
    applydup @preserve_program in hcv1;spcf;[].
    applydup @isprogram_ot_iff in hcv4.
    applydup @isprogram_ot_iff in hcv0.
    exrepnd. clear hcv8 hcv7.
    Hint Resolve selectbt_in alphaeq_preserves_wf_r_eauto isprogam_bt_nt_wf_eauto : slow.
    assert (n < length lbt') as X99 by omega.
    dands; spcf; try (apply isprogam_bt_nt_wf_eauto with (lv:=x); eauto with slow);[].
    introv Hw Hpa Hpb.
    right.
    apply Cih;sp.
    apply lsubst_approx_star_congr3;sp.

  - introv comp.
    applydup @preserve_program_exc2 in comp; sp;[].
    apply @howe_lemma3_exc with (b:=b) in comp; sp;[].
    apply howe_lemma2_exc in comp; auto;
    try (apply isprogram_exception; auto); exrepnd;[].
    applydup @preserve_program_exc2 in comp3; auto; repnd.
    exists a' e'; dands; auto; tcsp.

  - introv comp.
    applydup @reduces_to_preserves_program in comp; auto.
    eapply howe_lemma3_seq in Has0; eauto.
    apply howe_lemma2_seq in Has0; auto; exrepnd.
    eexists; dands; eauto.
Qed.

(* end hide *)

(** %\noindent \\*%
    Now Howe uses a simple coindiuctive argument to show that
    [approx_star] implies [approx] on closed terms.

 *)
Theorem howetheorem1 {p} :
  forall lib a b,
    @approx_star p lib a b
    -> isprogram a
    -> isprogram b
    -> approx lib a b.
Proof.
  intros. apply howetheorem1_aux;sp.
Qed.

(** %\noindent \\*%
    There are many useful Corollaries of the above theorem.

 *)
Corollary approx_star_implies_approx_open {p} :
  forall lib (t1 t2 : @NTerm p), approx_star lib t1 t2 -> approx_open lib t1 t2.
Proof.
  introv Has.
  applydup @approx_star_relates_only_wf in Has. repnd.
  unfold approx_open, olift. dands; spcf. introv Hw Hpa Hpb.
  apply howetheorem1;sp.
  apply lsubst_approx_star_congr3;sp.
Qed.

Corollary approx_star_iff_approx_open {p} :
  forall lib (t1 t2 : @NTerm p), approx_star lib t1 t2 <=> approx_open lib t1 t2.
Proof.
  split; introv hyp.
  - apply approx_star_implies_approx_open;sp.
  - apply approx_open_implies_approx_star;sp.
Qed.

Lemma le_blift_sub {p} :
  forall op (R1 R2 : bin_rel (@NTerm p)),
    le_bin_rel R1 R2 -> le_bin_rel (blift_sub op R1) (blift_sub op R2).
Proof.
  unfold le_bin_rel.
  intros R1 R2 Hle a b Hrel.
  allunfold @blift_sub.
  sp.
  - exists lv nt1 nt2; split; eauto.
  - exists lv nt1 nt2; split; eauto.
    subst; right; exists sub; subst; split; eauto.
Defined.
Hint Resolve le_blift_sub : slow.

Lemma le_blift_sub2 {p} :
  forall op (R1 R2 : bin_rel (@NTerm p)),
    (le_bin_rel R1 R2)
    -> forall a b, (blift_sub op R1 a b) -> (blift_sub op R2 a b).
Proof.
  intros op R1 R2 n H.
  fold (@le_bin_rel (BTerm ) (blift_sub op R1) (blift_sub op R2)).
  apply le_blift_sub.
  auto.
Defined.
Hint Resolve le_blift_sub2 : slow.

Lemma le_lblift_sub {p} :
  forall op (R1 R2 : bin_rel (@NTerm p)),
    (le_bin_rel R1 R2)
    -> le_bin_rel (lblift_sub op R1) (lblift_sub op R2).
Proof.
  unfold lblift_sub; sp.
  unfold le_bin_rel; sp.
  generalize (X0 n); sp.
  apply @le_blift_sub2 with (R1 := R1); sp.
Defined.

Lemma le_lblift_sub2 {p} :
  forall op (R1 R2 : bin_rel (@NTerm p)),
    (le_bin_rel R1 R2)
    -> forall a b, (lblift_sub op R1 a b) -> (lblift_sub op R2 a b).
Proof.
  intros op R1 R2 H.
  fold (@le_bin_rel (list BTerm) (lblift_sub op R1) (lblift_sub op R2)).
  apply le_lblift_sub. auto.
Defined.

Corollary approx_open_congruence_sub {p} :
  forall lib (o : Opid) (lbt1 lbt2 : list (@BTerm p)),
    lblift_sub o (approx_open lib) lbt1 lbt2
    -> nt_wf (oterm o lbt2)
    -> approx_open lib (oterm o lbt1) (oterm o lbt2).
Proof.
  introv Haps Hnt.
  apply (le_lblift_sub2 _ _ _ (approx_open_implies_approx_star lib)) in Haps.
  apply approx_star_implies_approx_open.
  apply approx_star_congruence2; sp.
Qed.

Corollary approx_open_congruence {p} :
  forall lib (o : Opid) (lbt1 lbt2 : list (@BTerm p)),
    lblift (approx_open lib) lbt1 lbt2
    -> nt_wf (oterm o lbt2)
    -> approx_open lib (oterm o lbt1) (oterm o lbt2).
Proof.
  introv Haps Hnt.
  apply (le_lblift2 _ _ (approx_open_implies_approx_star lib)) in Haps.
  apply approx_star_implies_approx_open.
  apply approx_star_congruence2; sp.

  unfold approx_starbts, lblift_sub.
  unfold lblift in Haps; repnd; dands; auto.
  introv i; applydup Haps in i as b.
  unfold blift in b; unfold blift_sub; exrepnd.
  exists lv nt1 nt2; dands; auto.
  destruct (dec_op_eq_fresh o) as [d|d]; tcsp.
  right.

  pose proof (exists_nrut_sub
                lv
                (get_utokens nt1 ++ get_utokens nt2))
    as exnrut; exrepnd.
  exists sub; dands; auto.
  apply lsubst_approx_star_congr3; eauto with slow.
Qed.

Corollary approx_congruence_sub {p} : forall lib o lbt1 lbt2,
  lblift_sub o (approx_open lib) lbt1 lbt2
  -> @isprogram p (oterm o lbt1)
  -> isprogram (oterm o lbt2)
  -> approx lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps H1p H2p.
   apply approx_open_approx;sp.
   apply approx_open_congruence_sub;sp.
   eauto with slow.
Qed.

Corollary approx_congruence {p} : forall lib o lbt1 lbt2,
  lblift (approx_open lib) lbt1 lbt2
  -> @isprogram p (oterm o lbt1)
  -> isprogram (oterm o lbt2)
  -> approx lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps H1p H2p.
   apply approx_open_approx;sp.
   apply approx_open_congruence;sp.
   eauto with slow.
Qed.

(* begin hide *)

Ltac prove_approx_lblift :=
  unfold lblift; simpl; dands;[spc|];
  let Hlt := fresh "XXHlt" in
  let n := fresh "XXn" in
  intros n Hlt;
    ( let rnum := (get_lt_rhs  Hlt) in
      fail_if_not_number rnum; (*fail if not a normal form*)
      repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
    ).

Ltac prove_approx_lblift_sub :=
  unfold lblift_sub; simpl; dands;[spc|];
  let Hlt := fresh "XXHlt" in
  let n := fresh "XXn" in
  intros n Hlt;
    ( let rnum := (get_lt_rhs  Hlt) in
      fail_if_not_number rnum; (*fail if not a normal form*)
      repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
    ).

Ltac prove_approx :=
  unfold_all_mk;
  match goal with
    | [ |- approx _ ?t ?t] => apply approx_refl
    | [ |- approx_open _ ?t ?t] => apply approx_open_refl
    | [ |- approx_open _ ?t1 ?t2] => apply approx_implies_approx_open
    | [ |- approx _ (oterm ?o _) (oterm ?o _)] => apply approx_congruence
    | [ |- isprogram _] => repeat(decomp_progh); show_hyps; repeat(decomp_progc); sp
    (* blift *)
    | [ |- lblift (olift approx) _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ ] => prove_approx_lblift
    | [ |- lblift (approx_open _) _ _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ _ _ ] => prove_approx_lblift
    | [ |- blift (olift approx) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    | [ |- blift (approx_open _) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    (* lblift *)
    | [ |- lblift_sub _ (olift approx) _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (approx_open _) _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ _ _ ] => prove_approx_lblift_sub
    | [ |- blift_sub _ (olift approx) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    | [ |- blift_sub _ (approx_open _) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
  end.

Lemma le_bin_rel_approx1_eauto {p} :
  forall lib, le_bin_rel (approx lib) (@approx_star p lib).
Proof.
  introv Has.
  eauto with slow.
  apply approx_star_iff_approx_open.
  apply approx_implies_approx_open.
  auto.
Qed.

Lemma le_bin_rel_approx2_eauto {p} :
  forall lib, le_bin_rel (@approx p lib) (indep_bin_rel isprogram isprogram).
Proof.
  introv Has. unfolds_base.
  apply approx_relates_only_progs in Has;sp.
Qed.

(* end hide *)

Corollary lsubst_approx_congr {p} : forall lib t1 t2 sub1 sub2,
  sub_range_rel (@approx p lib) sub1 sub2
  -> approx_open lib t1 t2
  -> isprogram (lsubst t1 sub1)
  -> isprogram (lsubst t2 sub2)
  -> approx lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv Hsr Hao H1p H2p.
  apply (le_sub_range_rel _ _  (le_bin_rel_approx1_eauto lib)) in Hsr.
  apply howetheorem1; auto.
  apply approx_open_implies_approx_star in Hao.
  apply lsubst_approx_star_congr2; auto.
Qed.

(* begin hide *)

Lemma approxbtd_change3 {p} : forall lib bt1 bt2 (lvn: list NVar),
  approx_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
  -> approx_open lib (apply_bterm bt1 (map vterm lvn))
                 (apply_bterm bt2 (map (@vterm p) lvn)).
Proof.
  introv Hao Hnr Hlen Hdis.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  applydup @blift_numbvars in Hao.
  apply @approxbtd_change with (lvn:=lvn) in Hao; auto;[].
  exrepnd.
  unfold apply_bterm. allsimpl.
  allrw @fold_var_ren.
  allunfold @num_bvars. allsimpl.
  apply apply_bterm_alpha_congr2 with (lnt := map vterm lvn)  in Hao3; spcls; try congruence;[].
  apply apply_bterm_alpha_congr2 with (lnt := map vterm lvn)  in Hao4; spcls;
    unfold num_bvars; simpl;  try congruence;[].
  allunfold @apply_bterm.
  allsimpl.
  allrw (@fold_var_ren).
  pose proof (lsubst_trivial_alpha nt2' lvn)  as zz.
  pose proof (lsubst_trivial_alpha nt1' lvn)  as zzz.
  assert (alpha_eq nt1' (lsubst nt1 (var_ren lv1 lvn))) as r1 by eauto with slow.
  assert (alpha_eq nt2' (lsubst nt2 (var_ren lv2 lvn))) as r2 by eauto with slow.
  clear zzz zz Hao0 Hdis Hlen Hnr Hao2 Hao4 Hao3.
  eapply approx_open_alpha_rw_lr in Hao1; eauto with slow.
Qed.

Lemma implies_approx_fix {p} :
  forall lib a b,
    @approx p lib a b
    -> approx lib (mk_fix a) (mk_fix b).
Proof.
  introv ap.
  applydup @approx_relates_only_progs in ap.
  repnd.
  repeat (prove_approx);sp.
Qed.

(*
Lemma implies_approx_apseq {p} :
  forall lib f a b,
    @approx p lib a b
    -> approx lib (mk_apseq f a) (mk_apseq f b).
Proof.
  introv ap.
  applydup @approx_relates_only_progs in ap.
  repnd.
  repeat (prove_approx);sp.
Qed.
*)

Lemma implies_approx_apply {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_apply f a) (mk_apply g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma if_computes_to_marker_apply {p} :
  forall lib (f a : @NTerm p) m,
    isprogram f
    -> isprogram a
    -> computes_to_marker lib (mk_apply f a) m
    -> {v : NVar & {b : NTerm & reduces_to lib f (mk_lam v b)}}.
Proof.
  introv.
  unfold computes_to_marker, reduces_to.
  introv ispf ispa comp; exrepnd.
  revert f a ispf ispa comp0.
  induction k; simpl; introv ispf ispa comp.

  - inversion comp; subst; GC.

  - apply reduces_in_atmost_k_steps_S in comp; exrepnd.
    simpl in comp1.
    destruct f; try (complete (inversion comp1)).
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      csunf comp1; allsimpl.
      apply compute_step_apply_success in comp1; exrepnd; subst; cpx; GC.
      exists v b 0; sp.

    + Case "NCan".
      unfold mk_apply, nobnd in comp1; rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.
      exrepnd.

      exists v b (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists n; sp.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply reduces_atmost_exc in comp0; ginv.

    + Case "Abs".
      unfold mk_apply, nobnd in comp1; rw @compute_step_ncan_abs in comp1.
      remember (compute_step_lib lib abs l); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @isprogram_compute_step_lib in Heqc; auto.
      apply IHk in comp0; auto; exrepnd.

      exists v b (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists n; sp.
Qed.
*)

Lemma hasvalue_like_implies_or {o} :
  forall lib (t : @NTerm o),
    isprogram t
    -> hasvalue_like lib t
    -> hasvalue lib t
       [+] raises_exception lib t.
Proof.
  introv isp hv.
  unfold hasvalue_like in hv; exrepnd.
  applydup @reduces_to_preserves_program in hv1; auto.
  dorn hv0.
  - left.
    exists v.
    unfold computes_to_value; dands; auto.
  - right.
    apply isexc_implies in hv0; exrepnd; subst; auto.
    exists a e; auto.
Qed.

Lemma fix_unfold_approx_fix {p} : forall lib f,
  @isprogram p f
  -> approx lib (mk_apply f (mk_fix f)) (mk_fix f).
Proof.
  introv Hpr.
  apply approx_assume_hasvalue;
  try match goal with [|- isprogram _] => eauto with slow; fail end.
  introv Hv.

  apply hasvalue_like_implies_or in Hv;
    [|apply isprogram_apply; auto; apply isprogram_fix; complete auto].

  dorn Hv.

  - unfold hasvalue in Hv; exrepnd.
    applydup @if_computes_to_value_apply in Hv0; auto;
    allrw @isprog_eq; auto; try (apply isprogram_fix; auto).
    repndors; exrepnd.

    { clear Hv1.
      applydup @computes_to_value_preserves_program in Hv2; auto.
      apply @approx_trans with (b := mk_fix (mk_lam v b)).

      + apply @approx_trans with (b := mk_apply (mk_lam v b) (mk_fix (mk_lam v b))); auto.

        * apply implies_approx_apply.
          apply reduces_to_implies_approx2; auto.
          destruct Hv2; auto.
          apply implies_approx_fix.
          apply reduces_to_implies_approx2; auto.
          destruct Hv2; auto.

        * apply reduces_to_implies_approx1; auto.
          apply isprogram_fix; auto.
          apply reduces_to_if_step; reflexivity.

      + apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        destruct Hv2; auto.
    }

    { apply @approx_trans with (b := mk_fix (mk_nseq s)).

      + apply @approx_trans with (b := mk_apply (mk_nseq s) (mk_fix (mk_nseq s))); auto.

        * apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }

        * apply reduces_to_implies_approx1; auto; prove_isprogram.
          apply reduces_to_if_step; reflexivity.

      + apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        destruct Hv1; auto.
    }

    { apply @approx_trans with (b := mk_fix (mk_ntseq s)).

      + apply @approx_trans with (b := mk_apply (mk_ntseq s) (mk_fix (mk_ntseq s))); auto.

        * apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }

        * apply reduces_to_implies_approx1; auto; prove_isprogram.
          apply reduces_to_if_step; reflexivity.

      + apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        destruct Hv1; auto.
    }

  - repnud Hv; exrepnd.
    applydup @isprogram_fix in Hpr.
    apply if_computes_to_exception_apply in Hv1; auto.
    repndors; exrepnd.

    + applydup @reduces_to_preserves_program in Hv1; auto.
      apply @approx_trans with (b := mk_fix (mk_lam v b)).

      * apply @approx_trans with (b := mk_apply (mk_lam v b) (mk_fix (mk_lam v b))); auto.

        apply implies_approx_apply.
        apply reduces_to_implies_approx2; auto.
        apply implies_approx_fix.
        apply reduces_to_implies_approx2; auto.

        apply reduces_to_implies_approx1; auto.
        apply isprogram_fix; auto.
        apply reduces_to_if_step; reflexivity.

      * apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram; auto.

    + apply @approx_trans with (b := mk_fix (mk_nseq s)).

      * apply @approx_trans with (b := mk_apply (mk_nseq s) (mk_fix (mk_nseq s))); auto.

        { apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto. }
        }

        { apply reduces_to_implies_approx1; auto.
          { apply isprogram_fix; eauto 3 with slow. }
          { apply reduces_to_if_step; reflexivity. }
        }

      * apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram; auto.

    + apply @approx_trans with (b := mk_fix (mk_ntseq s)).

      * apply @approx_trans with (b := mk_apply (mk_ntseq s) (mk_fix (mk_ntseq s))); auto.

        { apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto. }
        }

        { apply reduces_to_implies_approx1; auto.
          { apply isprogram_fix; eauto 3 with slow. }
          { apply reduces_to_if_step; reflexivity. }
        }

      * apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram; auto.

    + applydup @preserve_program_exc2 in Hv1; repnd; auto.
      apply approx_trans with (b := mk_apply (mk_exception a e) (mk_fix f)).

      * apply implies_approx_apply; auto; try (apply approx_refl; auto).
        apply computes_to_exception_implies_approx; auto.

      * applydup (isprogram_exception a)  in Hv0; auto.
        apply approx_trans with (b := mk_fix (mk_exception a e)).

        apply approx_trans with (b := mk_exception a e).

        apply reduces_to_implies_approx2; auto.
        apply isprogram_apply; auto.
        apply reduces_to_if_step; reflexivity.

        apply reduces_to_implies_approx1; auto.
        apply isprogram_fix; auto.
        apply reduces_to_if_step; reflexivity.

        apply implies_approx_fix.
        apply reduces_to_implies_approx1; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
