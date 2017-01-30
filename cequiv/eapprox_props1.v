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


Require Export approx_props1.
Require Export eapprox.
(* import esqle *)
Require Import sqle.


Lemma ex_approx_open_simpler_equiv_r {o} :
  forall lib ex (a c : @NTerm o) r,
    respects_alpha_r (ex_approx_aux lib ex r \2/ r)
    -> respects_alpha_l (ex_approx_aux lib ex r \2/ r)
    -> (simpl_olift (ex_approx_aux lib ex r \2/ r) a c
        <=> olift (ex_approx_aux lib ex r \2/ r) a c).
Proof.
  introv rr rl.
  split.

  - intro Hos.
    repnud Hos.
    unfold olift.
    dands;auto.
    introv Hwfs Hispa Hispc.
    pose proof (lsubst_trim2_alpha1 _ _ _ Hispc Hispa) as Xtrim.
    pose proof (lsubst_trim2_alpha2 _ _ _ Hwfs Hispc Hispa) as Xprog.
    allsimpl. repnd. rename Xtrim into Xtrima.
    rename Xtrim0 into Xtrimc.
    revert Hispa Hispc. alpharw Xtrima. alpharw Xtrimc.
    introv Hispa Hispc.
    pose proof (Hos (sub_keep_first sub (free_vars c ++ free_vars a))) as h.
    repeat (autodimp h hyp).
    unfold respects2_r in rr.
    unfold respects2_l in rl.
    pose proof (rr (lsubst a (sub_keep_first sub (free_vars c ++ free_vars a)))
                   (lsubst c (sub_keep_first sub (free_vars c ++ free_vars a)))
                   (lsubst c sub))
         as h1.
    autodimp h1 hyp; eauto 2 with slow.
    apply h1 in h; clear h1.
    pose proof (rl (lsubst a (sub_keep_first sub (free_vars c ++ free_vars a)))
                   (lsubst c sub)
                   (lsubst a sub))
         as h1.
    autodimp h1 hyp; eauto 2 with slow.

  - intro Hos.
    repnud Hos.
    unfold olift in Hos; unfold simpl_olift; repnd; dands; auto.
    introv ps isp1 isp2.
    pose proof (Hos sub) as h.
    repeat (autodimp h hyp); eauto with slow.
Qed.

Definition ex_approx_or_bts {o} lib ex (r : bin_rel (@NTerm o)) :=
  lblift (olift (ex_approx_aux lib ex r \2/ r)).

Lemma ex_approx_or_bts_alpha_eq_bterms_l {o} :
  forall lib ex (bs1 bs2 bs3 : list (@BTerm o)) r,
    alpha_eq_bterms bs1 bs2
    -> ex_approx_or_bts lib ex r bs1 bs3
    -> ex_approx_or_bts lib ex r bs2 bs3.
Proof.
  introv aeq apr.
  allunfold @ex_approx_or_bts.
  allunfold @lblift; repnd.
  allunfold @alpha_eq_bterms; repnd.
  dands; tcsp.
  introv i.
  rw <- aeq0 in i; applydup apr in i.

  assert (alpha_eq_bterm (selectbt bs1 n) (selectbt bs2 n)) as a.
  { apply aeq.
    unfold selectbt.
    apply in_nth_combine; auto. }

  eapply blift_alpha_fun_l; eauto with slow.
Qed.

Lemma ex_approx_or_bts_alpha_eq_bterms_r {o} :
  forall lib ex (bs1 bs2 bs3 : list (@BTerm o)) r,
    alpha_eq_bterms bs2 bs3
    -> ex_approx_or_bts lib ex r bs1 bs3
    -> ex_approx_or_bts lib ex r bs1 bs2.
Proof.
  introv aeq apr.
  allunfold @ex_approx_or_bts.
  allunfold @lblift; repnd.
  allunfold @alpha_eq_bterms; repnd.
  dands; tcsp; try omega.
  introv i.
  applydup apr in i.

  assert (alpha_eq_bterm (selectbt bs2 n) (selectbt bs3 n)) as a.
  { apply aeq.
    unfold selectbt.
    apply in_nth_combine; auto; try omega. }

  eapply blift_alpha_fun_r; eauto with slow.
Qed.

Lemma respects_alpha_r_ex_approx_aux {o} :
  forall lib ex (r : bin_rel (@NTerm o)),
    respects_alpha_r r
    -> respects_alpha_r (ex_approx_aux lib ex r).
Proof.
  introv resp; introv aeq apr.
  revert resp a b b' aeq apr.

  pose proof
       (ex_approx_acc
          lib
          ex
          (fun a b => {c : NTerm
                       $ respects_alpha_r r
                       # alpha_eq c b
                       # ex_approx_aux lib ex r a c})
          r) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> ?B |- _ ] =>
      assert B as h;
        [|introv resp aeq apr; eapply h; exists b; dands; auto; fail]
  end.

  apply HH; clear HH.
  introv hb hr h; exrepnd; subst.
  rename h1 into resp.
  rename h2 into aeq.
  rename h0 into apr.

  inversion apr as [cl].
  constructor.
  rename x0 into a.
  rename c into b.
  rename x1 into c.
  allunfold @ex_close_comput; repnd; dands; tcsp.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear cl3 cl.
    introv comp.
    apply cl2 in comp.
    exrepnd.
    eapply compute_to_value_alpha in comp1; eauto 3 with slow; exrepnd.
    applydup @alpha_eq_oterm_implies_combine in comp2; exrepnd; subst.
    exists bs'; dands; auto.
    allunfold @lblift; repnd; dands; auto; try omega.
    introv i.
    applydup comp0 in i.
    allunfold @blift; exrepnd.
    pose proof (comp4 (selectbt tr_subterms n) (selectbt bs' n)) as h.
    autodimp h hyp.
    { unfold selectbt; apply in_nth_combine; auto; try omega. }

    exists lv nt1 nt2; dands; eauto 3 with slow.

    allunfold @olift; repnd; dands; auto.
    introv wfs isp1 isp2.
    pose proof (i0 sub wfs isp1 isp2) as k; clear i0.
    repndors; tcsp.
    right; apply hr.
    exists (lsubst nt2 sub); dands; auto.

  - clear cl2 cl.
    introv comp.
    apply cl3 in comp.
    repndors; tcsp.

    {
      left; right.
      apply hr.
      exists ex; dands; auto.
    }

    exrepnd.
    right.
    eapply compute_to_exception_alpha in comp0; eauto 3 with slow; exrepnd.
    exists a'0 t2'; dands; auto.

    + clear comp1.
      repndors; tcsp.

      * right.
        apply hr.
        exists a'; dands; auto.

      * right.
        apply hb; auto.
        eapply resp; eauto.

    + clear comp2.
      repndors; tcsp.

      * right.
        apply hr.
        exists e'; dands; auto.

      * right.
        apply hb; auto.
        eapply resp; eauto.

(*
  - clear cl2 cl3.
    introv comp.
    apply cl in comp.
    eapply compute_to_marker_alpha in comp; eauto.
*)

  - introv comp.
    apply cl4 in comp; exrepnd.
    eapply computes_to_seq_alpha in comp1; eauto 3 with slow; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0.
    pose proof (comp2 n) as q; clear comp2.

    repndors; tcsp; right.

    + apply hr.
      eexists; dands; eauto.

    + apply hb.
      eapply resp; eauto.
Qed.
Hint Resolve respects_alpha_r_ex_approx_aux : slow.

Lemma respects_alpha_l_ex_approx_aux {o} :
  forall lib ex (r : bin_rel (@NTerm o)),
    respects_alpha_l r
    -> respects_alpha_l (ex_approx_aux lib ex r).
Proof.
  introv resp aeq apr.
  apply alpha_eq_sym in aeq.
  revert resp a b a' aeq apr.

  pose proof
       (ex_approx_acc
          lib
          ex
          (fun a b => {c : NTerm
                       $ respects_alpha_l r
                       # alpha_eq a c
                       # ex_approx_aux lib ex r c b})
          r) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> ?B |- _ ] =>
      assert B as h;
        [|introv resp aeq apr; eapply h; exists a; dands; auto; fail]
  end.

  apply HH; clear HH.
  introv hb hr h; exrepnd; subst.
  rename h1 into resp.
  rename h2 into aeq.
  rename h0 into apr.

  inversion apr as [cl].
  constructor.
  rename x0 into a.
  rename c into b.
  rename x1 into c.
  allunfold @ex_close_comput; repnd; dands; tcsp.

  - apply alphaeq_preserves_program in aeq; apply aeq; auto.

  - clear cl3 cl.
    introv comp.
    eapply compute_to_value_alpha in comp;[| |exact aeq]; eauto 3 with slow.
    exrepnd.
    apply @alpha_eq_oterm_implies_combine in comp0; exrepnd; subst.
    apply cl2 in comp1; clear cl2.
    exrepnd.
    exists tr_subterms; dands; auto.
    allunfold @lblift; repnd; dands; auto; try omega.
    introv i.
    rw comp3 in i.
    applydup comp0 in i; clear comp0.
    allunfold @blift; exrepnd.
    pose proof (comp2 (selectbt tl_subterms n) (selectbt bs' n)) as h.
    autodimp h hyp.
    { unfold selectbt; apply in_nth_combine; auto; try omega. }

    exists lv nt1 nt2; dands; eauto 3 with slow.

    allunfold @olift; repnd; dands; auto.
    introv wfs isp1 isp2.
    pose proof (i0 sub wfs isp1 isp2) as k; clear i0.
    repndors; tcsp.
    right; apply hr.
    exists (lsubst nt1 sub); dands; auto.

  - clear cl2 cl.
    introv comp.
    eapply compute_to_exception_alpha in comp; eauto 3 with slow; exrepnd.
    apply cl3 in comp0.
    repndors; tcsp.

    {
      left; right.
      apply hr.
      exists a'; dands; auto.
    }

    {
      left; right.
      apply hb.
      eapply resp;[|eauto].
      apply alpha_eq_sym; auto.
    }

    exrepnd.
    right.
    exists a'0 e'; dands; auto.

    + clear comp0.
      repndors; tcsp.

      * right.
        apply hr.
        exists a'; dands; auto.

      * right.
        apply hb; auto.
        eapply resp;[apply alpha_eq_sym; eauto|]; auto.

    + clear comp4.
      repndors; tcsp.

      * right.
        apply hr.
        exists t2'; dands; auto.

      * right.
        apply hb; auto.
        eapply resp;[apply alpha_eq_sym; eauto|]; auto.

(*
  - clear cl2 cl3.
    introv comp.
    apply (compute_to_marker_alpha _ _ b) in comp; auto.
*)

  - introv comp.
    eapply computes_to_seq_alpha in comp;[| | eauto]; eauto 3 with slow; exrepnd.
    apply cl4 in comp1; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0.
    pose proof (comp2 n) as q; clear comp2.

    repndors; tcsp; right.

    + apply hr.
      eexists; dands; eauto.

    + apply hb.
      apply alpha_eq_sym in h.
      eapply resp; eauto.
Qed.
Hint Resolve respects_alpha_l_ex_approx_aux : slow.

(*
(* TO FIX!! *)
Theorem ex_approx_acc_resp {p} :
  forall (lib : library)
         (ex : NTerm)
         (l r0 : bin_rel (@NTerm p))
         (resp_l_l : respects_alpha_l l)
         (resp_r_l : respects_alpha_r l)
         (resp_l_r0 : respects_alpha_l r0)
         (resp_r_r0 : respects_alpha_r r0)
         (OBG : forall (r: bin_rel NTerm)
                       (INC: r0 =2> r)
                       (CIH: l =2> r)
                       (resp_r : respects_alpha_r r)
                       (resp_l : respects_alpha_l r),
                  l =2> ex_approx_aux lib ex r),
    l =2> ex_approx_aux lib ex r0.
Proof.
  intros.
  assert (SIM: ex_approx_aux lib ex (r0 \2/ l) x0 x1) by eauto 6 with slow.
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna e Hcl; repnd.
  unfold ex_close_comput.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    repndors; tcsp.
    left.
    apply CIH; apply OBG; eauto 3 with slow.

  - introv Hcomp.
    apply Hcl3 in Hcomp.

    repndors; tcsp.

    {
      left; left.
      apply OBG; auto.

XXXXXXXXXXXXXXXX
    }

    ; exrepnd.
    exists a' e'; dands; auto; repndors; auto; tcsp;
    try (complete (left; apply CIH; apply OBG; tcsp; eauto 3 with slow)).

  - introv comp.
    apply Hcl4 in comp; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0; repndors; tcsp.
    left.
    apply CIH; apply OBG; tcsp; eauto 3 with slow.
Qed.
*)

Lemma approx_change_utoks {o} :
  forall lib (t1 t2 : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
    -> approx lib t1 t2
    -> approx lib (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  introv nr1 nr2 d1 d2 apr.
  allrw @approx_sqle.
  allunfold @sqle.
  intro m.
  pose proof (apr m) as h; clear apr.
  revert t1 t2 ren nr1 nr2 d1 d2 h.

  induction m; introv norep1 norep2 disj1 disj2 apr.

  {
    inversion apr; subst.
    constructor; eauto with slow.
  }

  constructor.
  (*inversion apr as [? ? ? cl]; subst; clear apr.*)
  inversion apr as [|? ? ? cl]; clear apr; subst.
  allunfold @close_comput; repnd; dands; tcsp; eauto with slow; introv comp.

  - clear cl3 cl.
    dup comp as comp1.
    apply (computes_to_value_ren_utokens _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    eauto 3 with slow;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; auto.

    rw @ren_utokens_can in comp1.

    dup comp1 as comp2.
    apply cl2 in comp2; exrepnd.
    dup comp2 as comp22.
    apply (computes_to_value_ren_utokens _ _ _ ren) in comp2; eauto 3 with slow;[].
    rw @ren_utokens_can in comp2.

    assert (match
               get_utok_c
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             with
               | Some a => NUTok (ren_atom ren a)
               | None =>
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             end = c) as e.
    { destruct c; allsimpl; tcsp.
      rw @inv_ren_atom2; auto.
      apply computes_to_value_preserves_utokens in comp; allsimpl; eauto 3 with slow.
      rw subset_cons_l in comp; repnd.
      intro i.
      rw @get_utokens_ren_utokens in comp3.
      rw in_map_iff in comp3; exrepnd; subst.
      rw in_diff in i; repnd.
      destruct (ren_atom_or ren a) as [d|d]; tcsp.
      rw d in i0.
      apply in_dom_in_range in i0; auto.
    }
    rw e in comp2; clear e.

    eexists; dands;[exact comp2|].
    unfold lblift; unfold lblift in comp0.
    allrw map_length; repnd; dands; auto.
    introv i.
    applydup comp0 in i.
    unfold blift; unfold blift in i0.
    exrepnd.
    repeat (onerw @selectbt_map; auto; try omega).
    remember (selectbt tl_subterms n) as b1.
    remember (selectbt tr_subterms n) as b2.

    applydup @computes_to_value_preserves_utokens in comp as ss1; eauto 3 with slow.
    eapply (subset_trans _ (get_utokens_b b1)) in ss1;
      [|simpl; apply subset_app_l;
        introv k; rw lin_flat_map; exists b1;
        dands; auto; subst; apply selectbt_in;
        complete auto].
    apply (subset_map_map (ren_atom (inv_utok_ren ren))) in ss1.
    rw <- @get_utokens_b_ren_utokens_b in ss1.
    rw <- @get_utokens_ren_utokens in ss1.
    rw @inv_ren_utokens in ss1; auto.
    applydup @alpha_eq_bterm_preserves_utokens in i2 as put1; allsimpl.
    rw put1 in ss1; clear put1.

    applydup @computes_to_value_preserves_utokens in comp22 as ss2; allsimpl; eauto 3 with slow.
    eapply (subset_trans _ (get_utokens_b b2)) in ss2;
      [|simpl; apply subset_app_l;
        introv k; rw lin_flat_map; exists b2;
        dands; auto; subst; apply selectbt_in; complete omega].
    applydup @alpha_eq_bterm_preserves_utokens in i1 as put2; allsimpl.
    rw put2 in ss2; clear put2.

    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i1.
    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i2.

    assert (disjoint (dom_utok_ren ren)
                     (diff (get_patom_deq o)
                           (range_utok_ren ren)
                           (get_utokens_b b1))) as d.
    {
      apply computes_to_value_preserves_utokens in comp; allsimpl; eauto 3 with slow.
      allrw subset_app; repnd.
      assert (LIn b1 tl_subterms) as itl.
      { subst b1; unfold selectbt; apply nth_in; auto. }
      rw subset_flat_map in comp; apply comp in itl; clear comp.
      rw <- disjoint_diff_l.
      eapply subset_disjoint_r;[|exact itl].
      rw @get_utokens_ren_utokens.
      rw disjoint_diff_l.
      apply disjoint_dom_diff_range_map_ren_atom.
    }

    rw @inv_ren_utokens_b2 in i2; auto.
    allsimpl.
    exists lv (ren_utokens ren nt1) (ren_utokens ren nt2); dands; auto.

    unfold olift; unfold olift in i0; repnd.
    dands.
    { apply nt_wf_ren_utokens; auto. }
    { apply nt_wf_ren_utokens; auto. }
    introv wfs isp1 isp2.

    pose proof (ex_ren_utokens_sub
                  sub
                  ren
                  (get_utokens nt1 ++ get_utokens nt2)) as exren.
    autodimp exren hyp; exrepnd.

    pose proof (i0 sub') as h.
    repeat (autodimp h hyp).
    { subst; apply wf_sub_ren_utokens_sub_iff in wfs; auto. }
    { subst; apply isprogram_lsubst_iff in isp1; repnd.
      apply isprogram_lsubst_iff.
      rw @nt_wf_ren_utokens_iff in isp0; dands; auto.
      introv j.
      rw @free_vars_ren_utokens in isp1.
      apply isp1 in j; exrepnd.
      allrw @sub_find_ren_utokens_sub.
      remember (sub_find sub' v) as sf; symmetry in Heqsf; destruct sf; ginv.
      eexists; dands; eauto.
      - apply nt_wf_ren_utokens_iff in j2; auto.
      - unfold closed in j0; rw @free_vars_ren_utokens in j0; auto. }
    { subst; apply isprogram_lsubst_iff in isp2; repnd.
      apply isprogram_lsubst_iff.
      rw @nt_wf_ren_utokens_iff in isp0; dands; auto.
      introv j.
      rw @free_vars_ren_utokens in isp2.
      apply isp2 in j; exrepnd.
      allrw @sub_find_ren_utokens_sub.
      remember (sub_find sub' v) as sf; symmetry in Heqsf; destruct sf; ginv.
      eexists; dands; eauto.
      - apply nt_wf_ren_utokens_iff in j2; auto.
      - unfold closed in j0; rw @free_vars_ren_utokens in j0; auto. }

    pose proof (IHm (lsubst nt1 sub') (lsubst nt2 sub') (ren ++ ren')) as sqn.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw disjoint_app_l.
    allrw disjoint_app_r.
    repnd.
    repeat (autodimp sqn hyp); dands; eauto 3 with slow.

    { introv a b; applydup disj1 in a.
      allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
      apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
      apply in_get_utokens_sub in b0; exrepnd.
      apply in_sub_keep_first in b4; repnd.
      pose proof (exren1 t) as hh.
      repeat (autodimp hh hyp).
      rw lin_flat_map; apply sub_find_some in b5; apply in_sub_eta in b5; repnd.
      eexists; dands; eauto.
    }

    { eapply subset_disjoint;[exact exren4|].
      apply disjoint_app_l; dands.
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
    }

    { introv a b; applydup disj2 in a.
      allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
      apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
      apply in_get_utokens_sub in b0; exrepnd.
      apply in_sub_keep_first in b4; repnd.
      pose proof (exren1 t) as hh.
      repeat (autodimp hh hyp).
      rw lin_flat_map; apply sub_find_some in b5; apply in_sub_eta in b5; repnd.
      eexists; dands; eauto.
    }

    { eapply subset_disjoint;[exact exren4|].
      apply disjoint_app_l; dands.
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
    }

    { repeat (rw @lsubst_ren_utokens in sqn).
      rw exren0 in sqn.
      repeat (rw @ren_utokens_app_weak_l in sqn; eauto 2 with slow).
    }

  - clear cl2 cl.
    dup comp as comp1.

    apply (computes_to_exception_ren_utokens _ _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    eauto 3 with slow;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; auto.

    dup comp1 as comp2.
    apply cl3 in comp2; exrepnd.
    dup comp0 as comp00.
    apply (computes_to_exception_ren_utokens _ _ _ _ ren) in comp0; eauto 3 with slow.

    eexists; eexists; dands;[exact comp0|idtac|].

    {
      pose proof (IHm (ren_utokens (inv_utok_ren ren) a) a' ren) as h.
      repeat (autodimp h hyp).

      { apply computes_to_exception_preserves_utokens in comp1; repnd; eauto 3 with slow.
        introv i j; allrw in_diff; repnd.
        apply comp4 in j0.
        apply disj1 in i; allrw in_diff; sp.
      }

      { apply computes_to_exception_preserves_utokens in comp00; repnd; eauto 3 with slow.
        introv i j; allrw in_diff; repnd.
        apply comp01 in j0.
        apply disj2 in i; allrw in_diff; sp.
      }

      rw @inv_ren_utokens2 in h; auto.
      apply computes_to_exception_preserves_utokens in comp; repnd; eauto 3 with slow.
      introv i j.
      rw @get_utokens_ren_utokens in comp4.
      apply (disjoint_dom_diff_range_map_ren_atom (get_utokens t1)) in i; destruct i.
      allrw in_diff; repnd; dands; auto.
    }

    {
      pose proof (IHm (ren_utokens (inv_utok_ren ren) e) e' ren) as h.
      repeat (autodimp h hyp).

      { apply computes_to_exception_preserves_utokens in comp1; repnd; eauto 3 with slow.
        introv i j; allrw in_diff; repnd.
        apply comp1 in j0.
        apply disj1 in i; allrw in_diff; sp.
      }

      { apply computes_to_exception_preserves_utokens in comp00; repnd; eauto 3 with slow.
        introv i j; allrw in_diff; repnd.
        apply comp00 in j0.
        apply disj2 in i; allrw in_diff; sp.
      }

      rw @inv_ren_utokens2 in h; auto.
      apply computes_to_exception_preserves_utokens in comp; repnd; eauto 3 with slow.
      introv i j.
      rw @get_utokens_ren_utokens in comp.
      apply (disjoint_dom_diff_range_map_ren_atom (get_utokens t1)) in i; destruct i.
      allrw in_diff; repnd; dands; auto.
    }

(*
  - clear cl2 cl2.
    dup comp as comp1.

    apply (computes_to_marker_ren_utokens _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    auto;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; auto.

    dup comp1 as comp2.
    apply cl in comp2; exrepnd.
    dup comp2 as comp22.
    apply (computes_to_marker_ren_utokens _ _ _ ren) in comp2; auto.
*)

  - dup comp as comp1.

    apply (reduces_to_ren_utokens _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    eauto 3 with slow;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; allsimpl; auto.

    dup comp1 as comp2.
    apply cl4 in comp2; exrepnd.
    dup comp0 as comp00.
    apply (reduces_to_ren_utokens _ _ _ ren) in comp2; eauto 3 with slow; allsimpl.

    eexists; dands; eauto.
Qed.

(*
XXXXXXXXXXXXXXX

Lemma approx_change_utoks {o} :
  forall lib (t1 t2 : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
    -> approx lib t1 t2
    -> approx lib (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  intro lib.

(*
  cofix IND.

  introv nr1 nr2 disj1 disj2 apr.
*)

  pose proof
       (approx_acc
          lib
          (fun a b => {t1,t2 : NTerm
                       $ {ren : utok_ren
                       $ approx lib t1 t2
                       # no_repeats (range_utok_ren ren)
                       # no_repeats (dom_utok_ren ren)
                       # disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
                       # disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
                       # a = ren_utokens ren t1
                       # b = ren_utokens ren t2}})
          (@bot2 o)) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> ?B |- _ ] =>
      assert B as h;
        [|introv nr1 nr2 d1 d2 k; eapply h;
          eexists;eexists;eexists;dands;eauto;fail]
  end.

  apply HH; clear HH.
  introv hb hr h; exrepnd; subst.
  rename h1 into apr.
  rename h2 into norep1.
  rename h3 into norep2.
  rename h4 into disj1.
  rename h5 into disj2.


  constructor.
  (*inversion apr as [? ? ? cl]; subst; clear apr.*)
  inversion apr as [cl]; clear apr.
  allunfold @close_comput; repnd; dands; tcsp; eauto with slow; introv comp.

  - clear cl3 cl.
    dup comp as comp1.
    apply (computes_to_value_ren_utokens _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    auto;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; auto.

    rw @ren_utokens_can in comp1.

    dup comp1 as comp2.
    apply cl2 in comp2; exrepnd.
    apply (computes_to_value_ren_utokens _ _ _ ren) in comp2; auto.
    rw @ren_utokens_can in comp2.

    assert (match
               get_utok_c
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             with
               | Some a => NUTok (ren_atom ren a)
               | None =>
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             end = c) as e.
    { destruct c; allsimpl; tcsp.
      rw @inv_ren_atom2; auto.
      apply computes_to_value_preserves_utokens in comp; allsimpl.
      rw subset_cons_l in comp; repnd.
      intro i.
      rw @get_utokens_ren_utokens in comp3.
      rw in_map_iff in comp3; exrepnd; subst.
      rw in_diff in i; repnd.
      destruct (ren_atom_or ren a) as [d|d]; tcsp.
      rw d in i0.
      apply in_dom_in_range in i0; auto.
    }
    rw e in comp2; clear e.

    eexists; dands;[exact comp2|].
    unfold lblift; unfold lblift in comp0.
    allrw map_length; repnd; dands; auto.
    introv i.
    applydup comp0 in i.
    unfold blift; unfold blift in i0.
    exrepnd.
    repeat (onerw @selectbt_map; auto; try omega).
    remember (selectbt tl_subterms n) as b1.
    remember (selectbt tr_subterms n) as b2.

    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i1.
    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i2.

    assert (disjoint (dom_utok_ren ren)
                     (diff (get_patom_deq o)
                           (range_utok_ren ren)
                           (get_utokens_b b1))) as d.
    {
(*      clear IND.*)
      admit.
    }

    rw @inv_ren_utokens_b2 in i2; auto.
    allsimpl.
    exists lv (ren_utokens ren nt1) (ren_utokens ren nt2); dands; auto.

    unfold olift; unfold olift in i0; repnd.
    dands.
    { apply nt_wf_ren_utokens; auto. }
    { apply nt_wf_ren_utokens; auto. }
    introv wfs isp1 isp2.



(*
Lemma ren_utokens_lsubst_aux_approx {o} :
  forall lib (t1 t2 : @NTerm o) ren sub,
    prog_sub sub
    -> no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
    -> (forall sub, prog_sub sub -> approx lib (lsubst_aux t1 sub) (lsubst_aux t2 sub))
    -> approx lib (lsubst_aux (ren_utokens ren t1) sub) (lsubst_aux (ren_utokens ren t2) sub).
Proof.
  intro lib.

  pose proof
       (approx_acc
          lib
          (fun a b => {t1,t2 : NTerm
                       $ {ren : utok_ren
                       $ {sub : Sub
                       $ prog_sub sub
                       # no_repeats (range_utok_ren ren)
                       # no_repeats (dom_utok_ren ren)
                       # disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
                       # disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
                       # (forall sub, prog_sub sub -> approx lib (lsubst_aux t1 sub) (lsubst_aux t2 sub))
                       # a = lsubst_aux (ren_utokens ren t1) sub
                       # b = lsubst_aux (ren_utokens ren t2) sub}}})
          (@bot2 o)) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> ?B |- _ ] =>
      assert B as h;
        [|introv ps nr1 nr2 d1 d2 k; eapply h;exists t1 t2 ren sub;dands;eauto;fail]
  end;[].

  apply HH; clear HH.
  introv hb hr h; exrepnd; subst.
  rename h0 into ps.
  rename h2 into nr1.
  rename h3 into nr2.
  rename h4 into disj1.
  rename h5 into disj2.
  rename h6 into imp.

  constructor.
  allunfold @close_comput; repnd; dands; tcsp.

  - pose proof (imp sub ps) as h.
    apply approx_relates_only_progs in h; repnd.
    rw <- @cl_lsubst_lsubst_aux in h0; eauto 2 with slow.
    applydup @lsubst_program_implies in h0.
    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
    apply isprogram_lsubst_iff in h0; repnd.
    apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @free_vars_ren_utokens; auto.

  - pose proof (imp sub ps) as h.
    apply approx_relates_only_progs in h; repnd.
    rw <- @cl_lsubst_lsubst_aux in h; eauto 2 with slow.
    applydup @lsubst_program_implies in h.
    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
    apply isprogram_lsubst_iff in h; repnd.
    apply isprogram_lsubst_if_isprog_sub; eauto 3 with slow.
    rw @free_vars_ren_utokens; auto.

  - introv comp.
    clear cl3 cl.
    dup comp as comp1.
    apply (computes_to_value_ren_utokens _ _ _ (inv_utok_ren ren)) in comp1;
    allrw @range_utok_ren_inv_utok_ren;
    allrw @dom_utok_ren_inv_utok_ren;
    auto;[|rw @get_utokens_ren_utokens; apply disjoint_dom_diff_range_map_ren_atom].
    rw @inv_ren_utokens in comp1; auto.

    rw @ren_utokens_can in comp1.

    dup comp1 as comp2.
    apply cl2 in comp2; exrepnd.
    apply (computes_to_value_ren_utokens _ _ _ ren) in comp2; auto.
    rw @ren_utokens_can in comp2.

    assert (match
               get_utok_c
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             with
               | Some a => NUTok (ren_atom ren a)
               | None =>
                 match get_utok_c c with
                   | Some a => NUTok (ren_atom (inv_utok_ren ren) a)
                   | None => c
                 end
             end = c) as e.
    { destruct c; allsimpl; tcsp.
      rw @inv_ren_atom2; auto.
      apply computes_to_value_preserves_utokens in comp; allsimpl.
      rw subset_cons_l in comp; repnd.
      intro i.
      rw @get_utokens_ren_utokens in comp3.
      rw in_map_iff in comp3; exrepnd; subst.
      rw in_diff in i; repnd.
      destruct (ren_atom_or ren a) as [d|d]; tcsp.
      rw d in i0.
      apply in_dom_in_range in i0; auto.
    }
    rw e in comp2; clear e.

    eexists; dands;[exact comp2|].
    unfold lblift; unfold lblift in comp0.
    allrw map_length; repnd; dands; auto.
    introv i.
    applydup comp0 in i.
    unfold blift; unfold blift in i0.
    exrepnd.
    repeat (onerw @selectbt_map; auto; try omega).
    remember (selectbt tl_subterms n) as b1.
    remember (selectbt tr_subterms n) as b2.

    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i1.
    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i2.

    assert (disjoint (dom_utok_ren ren)
                     (diff (get_patom_deq o)
                           (range_utok_ren ren)
                           (get_utokens_b b1))) as d.
    {
(*      clear IND.*)
      admit.
    }

    rw @inv_ren_utokens_b2 in i2; auto.
    allsimpl.
    exists lv (ren_utokens ren nt1) (ren_utokens ren nt2); dands; auto.

    unfold olift; unfold olift in i0; repnd.
    dands.
    { apply nt_wf_ren_utokens; auto. }
    { apply nt_wf_ren_utokens; auto. }
    introv wfs isp1 isp2.
Qed.
*)

    pose proof (ex_new_utok_ren
                  (dom_utok_ren ren)
                  (dom_utok_ren ren
                                ++ range_utok_ren ren
                                ++ get_utokens_sub sub
                                ++ get_utokens nt1
                                ++ get_utokens nt2)) as h.
    destruct h as [ren' h]; repnd.
    allrw disjoint_app_l; repnd.

    pose proof (lsubst_ren_utokens2 nt1 ren ren' sub) as e1.
    repeat (autodimp e1 hyp); eauto 3 with slow.
    pose proof (lsubst_ren_utokens2 nt2 ren ren' sub) as e2.
    repeat (autodimp e2 hyp); eauto 3 with slow.

    pose proof (ren_utokens_ren_utokens
                  (lsubst nt1 (ren_utokens_sub ren' sub))
                  (inv_utok_ren ren')
                  ren) as f1.
    rw @compose_ren_utokens_trivial in f1;
      [|rw @dom_utok_ren_inv_utok_ren; eauto 2 with slow].

    pose proof (ren_utokens_ren_utokens
                  (lsubst nt2 (ren_utokens_sub ren' sub))
                  (inv_utok_ren ren')
                  ren) as f2.
    rw @compose_ren_utokens_trivial in f2;
      [|rw @dom_utok_ren_inv_utok_ren; eauto 2 with slow].

    rw <- f1 in e1; rw <- f2 in e2; clear f1 f2.

    rewrite e1, e2; clear e1 e2.

    pose proof (i0 (ren_utokens_sub ren' sub)) as q; clear i0.
    repeat (autodimp q hyp); eauto 2 with slow.
    { apply isprogram_lsubst_iff in isp1; repnd.
      apply isprogram_lsubst_iff.
      rw @nt_wf_ren_utokens_iff in isp0; dands; auto.
      introv j.
      rw @free_vars_ren_utokens in isp1.
      apply isp1 in j; exrepnd.
      rw @sub_find_ren_utokens_sub; rw j1.
      eexists; dands; eauto.
      - apply nt_wf_ren_utokens; auto.
      - unfold closed; rw @free_vars_ren_utokens; auto. }
    { apply isprogram_lsubst_iff in isp2; repnd.
      apply isprogram_lsubst_iff.
      rw @nt_wf_ren_utokens_iff in isp0; dands; auto.
      introv j.
      rw @free_vars_ren_utokens in isp2.
      apply isp2 in j; exrepnd.
      rw @sub_find_ren_utokens_sub; rw j1.
      eexists; dands; eauto.
      - apply nt_wf_ren_utokens; auto.
      - unfold closed; rw @free_vars_ren_utokens; auto. }

    repndors; tcsp; try (complete (allunfold @bot2; sp)).


Theorem approx_acc {p} :
  forall (lib : library)
         (l r0 : bin_rel (@NTerm p))
         (OBG: forall (r: bin_rel NTerm)
                      (INC: r0 =2> r)
                      (CIH: l =2> r),
                 l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros.
  assert (SIM: approx_aux lib (r0 \2/ l) x0 x1) by auto.
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
Qed.


(*
    pose proof
         (hr
            (ren_utokens ren (lsubst nt1 (ren_utokens_sub ren' sub)))
            (ren_utokens ren (lsubst nt2 (ren_utokens_sub ren' sub))))
      as ind1.
    autodimp ind1 hyp.
    { exists
        (lsubst nt1 (ren_utokens_sub ren' sub))
        (lsubst nt2 (ren_utokens_sub ren' sub))
        ren; dands; auto.
      - admit.
      - admit.
    }
*)


    apply IND; tcsp.
    { rw @range_utok_ren_inv_utok_ren; rw h0; auto. }
    { rw @dom_utok_ren_inv_utok_ren; auto. }
    { clear IND; admit. }
    { clear IND; admit. }

    apply IND; tcsp.
    { clear IND; admit. }
    { clear IND; admit. }

  - clear IND; admit.

  - clear IND; admit.
Qed.

(*

      apply hr.
      exists (lsubst nt1 (ren_utokens_sub ren' sub))
             (lsubst nt2 (ren_utokens_sub ren' sub))
             ren;
        dands; eauto 3 with slow.

      * rw @range_utok_ren_app.
        rw @range_utok_ren_inv_utok_ren.
        apply no_repeats_app; dands; eauto 3 with slow.
        { rw h7; auto. }
        { eauto 3 with slow. }

pose proof (hr (ren_utokens (ren ++ inv_utok_ren ren')
                                  (lsubst nt1 (ren_utokens_sub ren' sub)))
                     (ren_utokens (ren ++ inv_utok_ren ren')
                                  (lsubst nt2 (ren_utokens_sub ren' sub)))
*)

Qed.
 *)
