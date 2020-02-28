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


Require Export approx.
Require Export atom_ren.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


Lemma respects_alpha_r2 {o} :
  forall (r1 r2 : bin_rel (@NTerm o)),
    respects_alpha_r r1
    -> respects_alpha_r r2
    -> respects_alpha_r (r1 \2/ r2).
Proof.
  introv resp1 resp2; introv aeq r.
  allsimpl; repndors.
  - eapply resp1 in aeq; apply aeq in r; auto.
  - eapply resp2 in aeq; apply aeq in r; auto.
Qed.
Hint Resolve respects_alpha_r2 : slow.

Lemma respects_alpha_l2 {o} :
  forall (r1 r2 : bin_rel (@NTerm o)),
    respects_alpha_l r1
    -> respects_alpha_l r2
    -> respects_alpha_l (r1 \2/ r2).
Proof.
  introv resp1 resp2; introv aeq r.
  allsimpl; repndors.
  - eapply resp1 in aeq; apply aeq in r; auto.
  - eapply resp2 in aeq; apply aeq in r; auto.
Qed.
Hint Resolve respects_alpha_l2 : slow.

Lemma respects_alpha_r_bot2 {o} :
  respects_alpha_r (@bot2 o).
Proof.
  introv aeq x; tcsp.
Qed.
Hint Resolve respects_alpha_r_bot2 : slow.

Lemma respects_alpha_l_bot2 {o} :
  respects_alpha_l (@bot2 o).
Proof.
  introv aeq x; tcsp.
Qed.
Hint Resolve respects_alpha_l_bot2 : slow.

Lemma approx_bad_implies_approx {o} :
  forall lib (t1 t2 : @NTerm o),
    approx_bad lib t1 t2 -> approx lib t1 t2.
Proof.
  intro lib.
  pose proof
       (approx_acc
          lib
          (fun a b => approx_bad lib a b)
          (@bot2 o)) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> ?B |- _ ] => assert B as h;[|introv ap; eapply h; eauto]
  end.
  introv ap.
  apply HH; auto; clear HH ap.
  introv hb hr ap.

  inversion ap as [? ? ? cl]; subst; clear ap.
  constructor.
  allunfold @close_comput; repnd; dands; auto.

  - introv comp.
    clear cl3 cl.
    apply cl2 in comp; exrepnd.
    eexists; dands; eauto.
    allunfold @lblift; dands; repnd; auto.
    introv i.
    apply comp0 in i.
    allunfold @blift; exrepnd.
    eexists; eexists; eexists; dands; eauto.
    allunfold @olift; repnd; dands; auto.

  - introv comp.
    clear cl2 cl.
    apply cl3 in comp; exrepnd.
    eexists; eexists; dands; eauto.
Qed.

Lemma approx_implies_approx_bad {o} :
  forall lib (t1 t2 : @NTerm o),
    approx lib t1 t2 -> approx_bad lib t1 t2.
Proof.
  intro lib.
  cofix IND.
  introv apr.
  inversion apr as [cl].
  constructor.
  allunfold @close_comput; repnd; dands; auto.

  - introv comp.
    clear cl3 cl.
    apply cl2 in comp; exrepnd.
    eexists; dands; eauto.
    allunfold @lblift; dands; repnd; auto.
    introv i.
    apply comp0 in i; clear comp0.
    allunfold @blift; exrepnd.
    eexists; eexists; eexists; dands; eauto.
    allunfold @olift; repnd; dands; auto.
    introv wf isp1 isp2.
    pose proof (i1 sub wf isp1 isp2) as h; clear i1.
    repndors.
    + apply IND; auto.
    + unfold bot2 in h; tcsp.

  - introv comp.
    clear cl2 cl.
    apply cl3 in comp; exrepnd.
    repndors; try (complete (allunfold @bot2; sp)).
    eexists; eexists; dands; eauto.
Qed.

Lemma approx_open_simpler_equiv_r {o} :
  forall lib (a c : @NTerm o) r,
    respects_alpha_r (approx_aux lib r \2/ r)
    -> respects_alpha_l (approx_aux lib r \2/ r)
    -> (simpl_olift (approx_aux lib r \2/ r) a c <=> olift (approx_aux lib r \2/ r) a c).
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

(*
Definition rens_utokens {o} (rens : list (@utok_ren o)) (t : NTerm) :=
  ren_utokens (flatten rens) t.

Inductive correct_rens {o} : list (@utok_ren o) -> list (get_patom_set o) -> Type :=
| correct_rens_nil : forall atoms, correct_rens [] atoms
| correct_rens_cons :
    forall ren rens atoms,
      disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) atoms)
      -> no_repeats (range_utok_ren ren)
      -> no_repeats (dom_utok_ren ren)
      -> disjoint (dom_utok_ren ren) (range_utok_ren ren)
      -> correct_rens rens (map (ren_atom ren) atoms)
      -> correct_rens (ren :: rens) atoms.

Lemma approx_change_utoks {o} :
  forall lib (t1 t2 : @NTerm o) rens,
    correct_rens rens (get_utokens t1 ++ get_utokens t2)
    -> approx lib t1 t2
    -> approx lib (rens_utokens rens t1) (rens_utokens rens t2).
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

XXXXXXXXX
*)


(*
Lemma alpha_eq_swap_lsubst_aux_var_ren {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs2 vs1
    -> disjoint vs2 (free_vars t)
    -> disjoint vs2 (bound_vars t)
    -> alpha_eq (swap (mk_swapping vs1 vs2) t)
                (lsubst_aux t (var_ren vs1 vs2)).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv norep disj1 disj2 disj3.

  - Case "vterm".
    allsimpl.
    allrw disjoint_singleton_r.
    rw @sub_find_var_ren_as_option_map.
    rw swapvar_eq; eauto 2 with slow.
    remember (renFind (mk_swapping vs1 vs2) v) as rf; destruct rf; allsimpl; auto.

  - Case "oterm"; allsimpl.
    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2]; allsimpl.
    applydup in_combine in i1; repnd.
    disj_flat_map; allsimpl.
    allrw disjoint_app_r; repnd.
Qed.
*)

Definition approx_or_bts {o} lib (r : bin_rel (@NTerm o)) :=
  lblift (olift (approx_aux lib r \2/ r)).

Lemma approx_or_bts_alpha_eq_bterms_l {o} :
  forall lib (bs1 bs2 bs3 : list (@BTerm o)) r,
    alpha_eq_bterms bs1 bs2
    -> approx_or_bts lib r bs1 bs3
    -> approx_or_bts lib r bs2 bs3.
Proof.
  introv aeq apr.
  allunfold @approx_or_bts.
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

Lemma approx_or_bts_alpha_eq_bterms_r {o} :
  forall lib (bs1 bs2 bs3 : list (@BTerm o)) r,
    alpha_eq_bterms bs2 bs3
    -> approx_or_bts lib r bs1 bs3
    -> approx_or_bts lib r bs1 bs2.
Proof.
  introv aeq apr.
  allunfold @approx_or_bts.
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

Lemma respects_alpha_r_approx_aux {o} :
  forall lib (r : bin_rel (@NTerm o)),
    respects_alpha_r r
    -> respects_alpha_r (approx_aux lib r).
Proof.
  introv resp; introv aeq apr.
  revert resp a b b' aeq apr.

  pose proof
       (approx_acc
          lib
          (fun a b => {c : NTerm
                       $ respects_alpha_r r
                       # alpha_eq c b
                       # approx_aux lib r a c})
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
  allunfold @close_comput; repnd; dands; tcsp.

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
    exrepnd.
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
Qed.
Hint Resolve respects_alpha_r_approx_aux : slow.

Lemma alpha_eq_respects_nt_wf {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> nt_wf a
    -> nt_wf b.
Proof.
  introv aeq wf.
  apply alphaeq_preserves_wf in aeq; apply aeq; auto.
Qed.
Hint Resolve alpha_eq_respects_nt_wf : slow.

Lemma alpha_eq_respects_nt_wf_inv {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> nt_wf b
    -> nt_wf a.
Proof.
  introv aeq wf; apply alpha_eq_sym in aeq; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_respects_nt_wf_inv : slow.

Lemma respects_alpha_l_approx_aux {o} :
  forall lib (r : bin_rel (@NTerm o)),
    respects_alpha_l r
    -> respects_alpha_l (approx_aux lib r).
Proof.
  introv resp; introv aeq apr.
  apply alpha_eq_sym in aeq.
  revert resp a b a' aeq apr.

  pose proof
       (approx_acc
          lib
          (fun a b => {c : NTerm
                       $ respects_alpha_l r
                       # alpha_eq a c
                       # approx_aux lib r c b})
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
  allunfold @close_comput; repnd; dands; tcsp.

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
    exrepnd.
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
Qed.
Hint Resolve respects_alpha_l_approx_aux : slow.

Theorem approx_acc_resp {p} :
  forall (lib : library)
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
                  l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros.
  assert (SIM: approx_aux lib (r0 \2/ l) x0 x1) by eauto 6 with slow.
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
    repndors; tcsp.
    left.
    apply CIH; apply OBG; eauto 3 with slow.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd.
    exists a' e'; dands; auto; repndors; auto; tcsp;
    try (complete (left; apply CIH; apply OBG; tcsp; eauto 3 with slow)).
Qed.

(*
Lemma approx_change_utoks_lsubst_aux {o} :
  forall lib (t1 t2 : @NTerm o) sub1 sub2 l,
    nrut_sub l sub1
    -> nrut_sub l sub2
    -> dom_sub sub1 = dom_sub sub2
    -> no_repeats (dom_sub sub1)
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> approx lib (lsubst_aux t1 sub1) (lsubst_aux t2 sub1)
    -> approx lib (lsubst_aux t1 sub2) (lsubst_aux t2 sub2).
Proof.
  intro lib.

  pose proof
       (approx_acc_resp
          lib
          (fun a b => {t1,t2 : NTerm
                       $ {sub1,sub2 : Sub
                       $ {l : list (get_patom_set o)
                       $ nrut_sub l sub1
                       # nrut_sub l sub2
                       # dom_sub sub1 = dom_sub sub2
                       # no_repeats (dom_sub sub1)
                       # subset (get_utokens t1) l
                       # subset (get_utokens t2) l
                       # approx lib (lsubst_aux t1 sub1) (lsubst_aux t2 sub1)
                       # alpha_eq a (lsubst_aux t1 sub2)
                       # alpha_eq b (lsubst_aux t2 sub2)}}})
          (@bot2 o)) as HH.
  allsimpl.
  match goal with
      [ HH : _ -> _ -> _ -> _ -> _ -> ?B |- _ ] =>
      assert B as h;
        [|introv nr1 nr2 e nr ss1 ss2 apr; eapply h;
          exists t1 t2 sub1 sub2 l; dands; auto; fail]
  end.

  apply HH; clear HH; eauto 2 with slow.
  { introv aeq h; allsimpl; exrepnd; subst.
    exists t1 t2 sub1 sub2 l; dands; eauto with slow. }
  { introv aeq h; allsimpl; exrepnd; subst.
    exists t1 t2 sub1 sub2 l; dands; eauto with slow. }

  introv hb hr rar ral h; exrepnd; subst.
  rename h1 into nrut1.
  rename h2 into nrut2.
  rename h3 into eqdoms.
  rename h4 into norep.
  rename h5 into ss1.
  rename h6 into ss2.
  rename h7 into apr.
  rename h8 into aeqls1.
  rename h0 into aeqls2.

  pose proof (respects_alpha_r_approx_aux lib r rar) as rar_aa.
  pose proof (respects_alpha_l_approx_aux lib r ral) as ral_aa.
  eapply rar_aa;[apply alpha_eq_sym;exact aeqls2|].
  eapply ral_aa;[apply alpha_eq_sym;exact aeqls1|].

  constructor.
  inversion apr as [cl]; clear apr; subst.
  allunfold @close_comput; repnd.

  prove_and isp1.

  {
    rw <- @cl_lsubst_lsubst_aux in cl0; eauto 2 with slow.
    rw @isprogram_lsubst_iff in cl0.
    repnd.
    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow;
    apply isprogram_lsubst_iff; dands; eauto; introv i.
    apply cl0 in i; exrepnd.
    pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v l nrut2 eqdoms) as h.
    rw i1 in h; exrepnd.
    rw h0; eexists; dands; eauto 2 with slow.
  }

  prove_and isp2.

  {
    rw <- @cl_lsubst_lsubst_aux in cl1; eauto 2 with slow.
    rw @isprogram_lsubst_iff in cl1.
    repnd.
    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow;
    apply isprogram_lsubst_iff; dands; eauto; introv i.
    apply cl1 in i; exrepnd.
    pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v l nrut2 eqdoms) as h.
    rw i1 in h; exrepnd.
    rw h0; eexists; dands; eauto 2 with slow.
  }

  dands.

  - clear cl3 cl.
    introv comp.
    rw <- @cl_lsubst_lsubst_aux in comp; eauto with slow.
    pose proof (computes_to_value_change_utok_sub
                  lib t1 (oterm (Can c) tl_subterms) sub2 sub1
                  comp) as h.
    repeat (autodimp h hyp); eauto 2 with slow.
    { unfold nrut_sub in nrut2; repnd.
      eapply subset_disjoint_r;[apply disjoint_sym in nrut2; exact nrut2|]; auto. }
    { unfold nrut_sub in nrut1; repnd.
      eapply subset_disjoint_r;[apply disjoint_sym in nrut1; exact nrut1|]; auto. }
    exrepnd.

    dup h5 as comp1.
    repeat (rw <- @cl_lsubst_lsubst_aux in cl2; eauto with slow).
    unfold close_compute_val in cl2.

    remember (get_utok_c c) as guo; symmetry in Heqguo; destruct guo.

    {
       apply get_utok_c_some in Heqguo; subst; allsimpl.
       dup comp as isv; unfold computes_to_value in isv; repnd.
       apply compute_max_steps_eauto2 in isv.
       apply isprogram_implies_wf in isv; auto.
       apply wf_term_utok in isv; subst; allsimpl; fold_terms.
       apply alpha_eq_mk_utoken in h0.
       rw @cl_lsubst_lsubst_aux in h0; eauto 2 with slow.
       destruct w as [v|op bs]; allsimpl.

       - allrw subvars_singleton_l.
         remember (sub_find sub2 v) as sf; symmetry in Heqsf; destruct sf; ginv; subst.
         pose proof (sub_find_some_eq_doms_nrut_sub sub2 sub1 v l nrut1) as e.
         autodimp e hyp; rw Heqsf in e; exrepnd.
         rw @cl_lsubst_lsubst_aux in h1; allsimpl; eauto 2 with slow.
         rw e0 in h1.
         apply alpha_eq_sym in h1.
         apply alpha_eq_mk_utoken in h1; subst.

         apply cl2 in comp1; exrepnd.
         unfold lblift in comp0; allsimpl; repnd; cpx; clear comp0; fold_terms.

         pose proof (computes_to_value_change_utok_sub
                       lib t2 (mk_utoken a) sub1 sub2 comp1) as q.
         repeat (autodimp q hyp); eauto 3 with slow.
         { unfold nrut_sub in nrut1; repnd.
           eapply subset_disjoint_r;[apply disjoint_sym in nrut1; exact nrut1|]; auto. }
         { unfold nrut_sub in nrut2; repnd.
           eapply subset_disjoint_r;[apply disjoint_sym in nrut2; exact nrut2|]; auto. }
         exrepnd.

         destruct w as [v'|op' bs']; allsimpl; dgc.

         + allrw subvars_singleton_l.
           rw @cl_lsubst_lsubst_aux in q1; eauto 2 with slow.
           rw @cl_lsubst_lsubst_aux in q0; eauto 2 with slow.
           allsimpl.
           pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v' l nrut2) as e'.
           autodimp e' hyp.
           remember (sub_find sub1 v') as sf'; symmetry in Heqsf'; destruct sf'.

           * exrepnd.
             rw e'0 in q1.
             apply alpha_eq_mk_utoken in q0; subst.
             apply alpha_eq_sym in q1.
             apply alpha_eq_mk_utoken in q1; subst.
             pose proof (nrut_sub_sub_find_same sub1 v v' (mk_utoken a) l) as e.
             repeat (autodimp e hyp); exrepnd; ginv; GC.
             rw e'0 in Heqsf; ginv.
             exists ([] : list (@BTerm o)); fold_terms.
             rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow; dands; auto.
             unfold lblift; simpl; sp.

           * inversion q0.

         + allrw disjoint_app_r; repnd.
           allrw subset_app; repnd.
           rw @cl_lsubst_lsubst_aux in q0; eauto 2 with slow; allsimpl.
           apply alpha_eq_mk_utoken in q0; subst.
           inversion q0; subst.
           destruct bs'; allsimpl; cpx; fold_terms; GC; dgc.
           allrw disjoint_singleton_r.
           allrw singleton_subset.
           rw @cl_lsubst_lsubst_aux in q1; eauto 2 with slow; allsimpl; fold_terms.
           apply alpha_eq_sym in q1; apply alpha_eq_mk_utoken in q1; subst.
           apply sub_find_some in e0; apply in_sub_eta in e0; repnd.
           destruct q6.
           rw lin_flat_map; exists (mk_utoken a); simpl; sp.

       - allrw disjoint_app_r; allrw subset_app; repnd.
         inversion h0; subst; allsimpl; cpx.
         destruct bs; allsimpl; cpx; fold_terms; GC; dgc.
         allrw disjoint_singleton_r; allrw singleton_subset.
         rw @cl_lsubst_lsubst_aux in h1; eauto 2 with slow; allsimpl; fold_terms.
         apply alpha_eq_sym in h1; apply alpha_eq_mk_utoken in h1; subst.
         apply cl2 in h5; exrepnd.
         unfold lblift in h0; allsimpl; repnd; cpx; clear h0; fold_terms.

         pose proof (computes_to_value_change_utok_sub
                       lib t2 (mk_utoken g) sub1 sub2 h1) as q.
         repeat (autodimp q hyp); eauto 3 with slow.
         { unfold nrut_sub in nrut1; repnd.
           eapply subset_disjoint_r;[apply disjoint_sym in nrut1; exact nrut1|]; auto. }
         { unfold nrut_sub in nrut2; repnd.
           eapply subset_disjoint_r;[apply disjoint_sym in nrut2; exact nrut2|]; auto. }
         exrepnd.

         destruct w as [v|op bs]; allsimpl; dgc.

         + allrw subvars_singleton_l.
           rw @cl_lsubst_lsubst_aux in q1; eauto 2 with slow.
           rw @cl_lsubst_lsubst_aux in q0; eauto 2 with slow.
           allsimpl.
           pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v l nrut2) as e.
           autodimp e hyp.
           remember (sub_find sub1 v) as sf; symmetry in Heqsf; destruct sf.

           * exrepnd; rw e0 in q1.
             apply alpha_eq_sym in q1.
             allapply @alpha_eq_mk_utoken; subst; allsimpl.
             unfold nrut_sub in nrut1; repnd.
             apply ss1 in h6; apply nrut1 in h6; destruct h6.
             apply sub_find_some in Heqsf; apply in_sub_eta in Heqsf; repnd.
             rw lin_flat_map; exists (mk_utoken g); simpl; sp.

           * inversion q0.

         + allrw disjoint_app_r; allrw subset_app; repnd.
           rw @cl_lsubst_lsubst_aux in q0; eauto 2 with slow; allsimpl.
           apply alpha_eq_mk_utoken in q0.
           inversion q0; subst; destruct bs; allsimpl; cpx; fold_terms; GC; dgc.
           allrw disjoint_singleton_r; allrw singleton_subset.
           rw @cl_lsubst_lsubst_aux in q1; eauto 2 with slow; allsimpl.
           apply alpha_eq_sym in q1; apply alpha_eq_mk_utoken in q1; subst.
           rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
           exists ([] : list (@BTerm o)); dands; auto.
           unfold lblift; simpl; sp.
    }

    destruct w as [v|op bs].

    {
      rw @cl_lsubst_lsubst_aux in h0; allsimpl; eauto 2 with slow.
      remember (sub_find sub2 v) as sf; symmetry in Heqsf; destruct sf.
      - apply sub_find_some in Heqsf.
        eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst.
        apply alpha_eq_sym in h0; apply alpha_eq_mk_utoken in h0; subst.
        inversion h0; subst; allsimpl; ginv.
      - inversion h0.
    }

    rw @cl_lsubst_lsubst_aux in h0; eauto 2 with slow; allsimpl.
    apply alpha_eq_oterm_combine2 in h0; repnd; subst.
    allrw map_length; allsimpl; GC.
    rw @cl_lsubst_lsubst_aux in h1; eauto 2 with slow; allsimpl.
    apply alpha_eq_sym in h1; apply alpha_eq_oterm_implies_combine in h1; exrepnd; subst.
    allrw map_length; GC.
    allrw disjoint_app_r; allrw subset_app; repnd.

    apply cl2 in h5; exrepnd.

    pose proof (computes_to_value_change_utok_sub
                  lib t2 (oterm (Can c) tr_subterms) sub1 sub2
                  h5) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { unfold nrut_sub in nrut1; repnd.
      eapply subset_disjoint_r;[apply disjoint_sym in nrut1; exact nrut1|]; auto. }
    { unfold nrut_sub in nrut2; repnd.
      eapply subset_disjoint_r;[apply disjoint_sym in nrut2; exact nrut2|]; auto. }
    exrepnd.

    destruct w as [v|op'' bs''].

    {
      rw @cl_lsubst_lsubst_aux in q0; allsimpl; eauto 2 with slow.
      remember (sub_find sub1 v) as sf; symmetry in Heqsf; destruct sf.
      - apply sub_find_some in Heqsf.
        eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst.
        apply alpha_eq_sym in q0; apply alpha_eq_mk_utoken in q0; subst.
        inversion q0; subst; allsimpl; ginv.
      - inversion q0.
    }

    rw @cl_lsubst_lsubst_aux in q0; eauto 2 with slow; allsimpl.
    apply alpha_eq_oterm_combine2 in q0; repnd; subst.
    allrw map_length; allsimpl; GC.
    rw @cl_lsubst_lsubst_aux in q1; eauto 2 with slow; allsimpl.
    apply alpha_eq_sym in q1; apply alpha_eq_oterm_implies_combine in q1; exrepnd; subst.
    allrw map_length; GC.
    allrw disjoint_app_r; allrw subset_app; repnd.

    exists bs'0.
    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow; dands; auto.

    assert (alpha_eq_bterms (lsubst_bterms_aux bs'' sub2) bs'0) as aebs1.
    { unfold alpha_eq_bterms, lsubst_bterms_aux; allrw map_length; dands; auto. }

    assert (alpha_eq_bterms tl_subterms (lsubst_bterms_aux bs sub2)) as aebs2.
    { unfold alpha_eq_bterms, lsubst_bterms_aux; allrw map_length; dands; auto. }

    assert (alpha_eq_bterms (lsubst_bterms_aux bs sub1) bs') as aebs3.
    { unfold alpha_eq_bterms, lsubst_bterms_aux; allrw map_length; dands; auto. }

    assert (alpha_eq_bterms tr_subterms (lsubst_bterms_aux bs'' sub1)) as aebs4.
    { unfold alpha_eq_bterms, lsubst_bterms_aux; allrw map_length; dands; auto. }

    assert (approx_or_bts lib bot2 bs' tr_subterms) as apr1 by sp.

    pose proof (approx_or_bts_alpha_eq_bterms_l
                  lib bs' (lsubst_bterms_aux bs sub1) tr_subterms bot2) as apr2.
    repeat (autodimp apr2 hyp); eauto 2 with slow.

    pose proof (approx_or_bts_alpha_eq_bterms_r
                  lib (lsubst_bterms_aux bs sub1) (lsubst_bterms_aux bs'' sub1) tr_subterms bot2) as apr3.
    repeat (autodimp apr3 hyp); eauto 2 with slow.

    fold (approx_or_bts lib r tl_subterms bs'0).
    eapply approx_or_bts_alpha_eq_bterms_l;[apply alpha_eq_bterms_sym;exact aebs2|].
    eapply approx_or_bts_alpha_eq_bterms_r;[apply alpha_eq_bterms_sym;exact aebs1|].

    clear h6 h0 q0 q6.

    unfold approx_or_bts in apr3; unfold approx_or_bts.
    unfold lblift in apr3; unfold lblift.
    allrw @length_lsubst_bterms_aux; repnd; dands; auto.
    introv i.
    pose proof (apr3 n i) as bl; clear apr3.

    repeat (rw @selectbt_lsubst_bterms_aux; auto; try omega).
    repeat (rw @selectbt_lsubst_bterms_aux in bl; auto; try omega).

    remember (selectbt bs n) as b1.
    remember (selectbt bs'' n) as b2.
    unfold blift in bl; exrepnd.
    unfold blift.

    pose proof (length_dom sub1) as el; rw eqdoms in el; rw @length_dom in el.

    assert (disjoint (get_utokens_sub sub1) (get_utokens_b b1)) as d11.
    { (* using h4 *)
      assert (subset (get_utokens_b b1) (get_utokens_bs bs)) as ss.
      { introv k; unfold get_utokens_bs; rw lin_flat_map.
        exists (selectbt bs n); rw <- Heqb1; dands; auto.
        rw Heqb1; apply selectbt_in; auto. }
      eapply subset_disjoint_r;[|exact ss].
      eapply subset_disjoint_r;[|exact h4].
      eapply subset_disjoint_r;[|exact ss1].
      unfold nrut_sub in nrut1; repnd; eauto with slow.
    }

    assert (disjoint (get_utokens_sub sub1) (get_utokens_b b2)) as d12.
    { (* using q4 *)
      assert (subset (get_utokens_b b2) (get_utokens_bs bs'')) as ss.
      { introv k; unfold get_utokens_bs; rw lin_flat_map.
        exists (selectbt bs'' n); rw <- Heqb2; dands; auto.
        rw Heqb2; apply selectbt_in; auto; try omega. }
      eapply subset_disjoint_r;[|exact ss].
      eapply subset_disjoint_r;[|exact q4].
      eapply subset_disjoint_r;[|exact ss2].
      unfold nrut_sub in nrut1; repnd; eauto with slow.
    }

(* XXXXXXXXXXXX *)

    pose proof (alpha_eq_bterm_ren_utokens_b
                  (lsubst_bterm_aux b1 sub1)
                  (bterm lv nt1)
                  (nrut_subs_to_utok_ren sub1 sub2)
                  bl2)
      as aeqr1.
    rw @lsubst_aux_bterm_ren_utokens_b in aeqr1.
    rw @ren_utokens_b_trivial in aeqr1;
      [|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; complete eauto].

    pose proof (alpha_eq_bterm_ren_utokens_b
                  (lsubst_bterm_aux b2 sub1)
                  (bterm lv nt2)
                  (nrut_subs_to_utok_ren sub1 sub2)
                  bl0)
      as aeqr2.
    rw @lsubst_aux_bterm_ren_utokens_b in aeqr2.
    rw @ren_utokens_b_trivial in aeqr2;
      [|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; complete eauto].

    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in aeqr1; eauto.
    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in aeqr2; eauto.
    remember (nrut_subs_to_utok_ren sub1 sub2) as ren.
    allsimpl.

    exists lv (ren_utokens ren nt1) (ren_utokens ren nt2); dands; auto.

    apply approx_open_simpler_equiv; eauto 3 with slow.

    unfold simpl_olift; unfold olift in bl1; repnd.

    prove_and ntwfsu1; eauto 2 with slow.
    prove_and ntwfsu2; eauto 2 with slow.

    introv wfs ispl1 ispl2.

(* rename the tokens of sub to fresh tokens *)
    pose proof (ex_new_utok_ren
                  (remove_repeats (get_patom_deq o) (get_utokens_sub sub1 ++ get_utokens_sub sub2))
                  (get_utokens_sub sub1
                                   ++ get_utokens_sub sub2
                                   ++ get_utokens_sub sub
                                   ++ get_utokens nt1
                                   ++ get_utokens nt2))
      as newut; exrepnd.

    pose proof (bl1 (ren_utokens_sub ren0 sub)) as rr.
    repeat (autodimp rr hyp); eauto 2 with slow.
    { apply wf_sub_ren_utokens_sub; eauto with slow. }
    { apply isprogram_lsubst_iff.
      apply isprogram_lsubst_iff in ispl1; repnd.
      apply nt_wf_ren_utokens_iff in ispl0; dands; auto.
      introv j.
      pose proof (ispl1 v) as k; rw @free_vars_ren_utokens in k; autodimp k hyp.
      exrepnd.
      rw @sub_find_ren_utokens_sub; rw k1; eexists; dands; eauto 2 with slow.
      unfold closed; rw @free_vars_ren_utokens; auto.
    }
    { apply isprogram_lsubst_iff.
      apply isprogram_lsubst_iff in ispl2; repnd.
      apply nt_wf_ren_utokens_iff in ispl0; dands; auto.
      introv j.
      pose proof (ispl2 v) as k; rw @free_vars_ren_utokens in k; autodimp k hyp.
      exrepnd.
      rw @sub_find_ren_utokens_sub; rw k1; eexists; dands; eauto 2 with slow.
      unfold closed; rw @free_vars_ren_utokens; auto.
    }

    repndors; tcsp.

    pose proof (pull_out_atoms
                  nt1
                  (get_utokens_sub sub1)
                  (free_vars nt2
                             ++ (sub_free_vars (ren_utokens_sub ren0 sub))
                             ++ dom_sub sub)) as pullout.
    autodimp pullout hyp; eauto 2 with slow.
    exrepnd.
    allrw disjoint_app_l; repnd.
    rw remove_repeats_if_no_repeats in pullout1; eauto 2 with slow.

    pose proof (pull_out_nrut_sub nt2 sub0 (get_utokens u)) as pullout'.
    repeat (autodimp pullout' hyp); eauto 2 with slow.
    exrepnd.

    pose proof (pull_out_atoms_sub
                  (ren_utokens_sub ren0 sub)
                  (range_utok_ren ren0)
                  (allvars u ++ allvars u0 ++ dom_sub sub0)) as pullout''.
    autodimp pullout'' hyp.
    { apply wf_sub_ren_utokens_sub; eauto with slow. }
    exrepnd.
    allrw disjoint_app_l; repnd.
    rw remove_repeats_if_no_repeats in pullout''1; auto.

    pose proof (respects_alpha_r_approx_aux_bot2 lib) as respr.
    unfold respects2_r in respr.
    pose proof (respr
                  (lsubst nt1 (ren_utokens_sub ren0 sub))
                  (lsubst nt2 (ren_utokens_sub ren0 sub))
                  (lsubst (lsubst u0 sub0) (lsubst_sub s' sub3)))
          as rer; clear respr.
    repeat (autodimp rer hyp).
    { apply lsubst_alpha_congr3; auto. }

    pose proof (respects_alpha_l_approx_aux_bot2 lib) as respl.
    unfold respects2_l in respl.
    pose proof (respl
                  (lsubst nt1 (ren_utokens_sub ren0 sub))
                  (lsubst (lsubst u0 sub0) (lsubst_sub s' sub3))
                  (lsubst (lsubst u sub0) (lsubst_sub s' sub3)))
          as rel; clear respl.
    repeat (autodimp rel hyp).
    { apply lsubst_alpha_congr3; auto. }
    clear rer.

    assert (subset (sub_free_vars s') (dom_sub sub3)) as ss.
    { introv is.
      rw @cl_lsubst_sub_eq_lsubst_aux_sub in pullout''5; eauto 3 with slow.
      applydup @alphaeq_sub_preserves_free_vars in pullout''5 as fvs.
      rw @sub_free_vars_ren_utokens_sub in fvs.
      rw @cl_sub_free_vars_lsubst_aux_sub in fvs; eauto 2 with slow.
      rw (sub_free_vars_if_cl_sub sub) in fvs; eauto 2 with slow.
      symmetry in fvs; apply null_iff_nil in fvs.
      pose proof (in_deq _ deq_nvar x (dom_sub sub3)) as [d|d]; auto.
      provefalse.
      pose proof (fvs x) as h; rw in_remove_nvars in h; sp. }

    applydup @alphaeq_sub_implies_eq_doms in pullout''5 as eqd.
    rw @dom_sub_ren_utokens_sub in eqd.
    rw @dom_sub_lsubst_sub in eqd.
    applydup @alphaeq_sub_preserves_cl_sub in pullout''5; eauto 3 with slow.
    pose proof (cl_lsubst_lsubst_lsubst_sub u s' sub0 sub3) as a1.
    rw <- eqd in a1.
    repeat (autodimp a1 hyp); eauto 4 with slow.
    pose proof (cl_lsubst_lsubst_lsubst_sub u0 s' sub0 sub3) as a2.
    rw <- eqd in a2.
    repeat (autodimp a2 hyp); eauto 4 with slow.

    pose proof (respects_alpha_r_approx_aux_bot2 lib) as respr.
    unfold respects2_r in respr.
    pose proof (respr
                  (lsubst (lsubst u sub0) (lsubst_sub s' sub3))
                  (lsubst (lsubst u0 sub0) (lsubst_sub s' sub3))
                  (lsubst (lsubst u0 s') (sub0 ++ sub3)))
          as rer; clear respr.
    repeat (autodimp rer hyp).
    clear rel.

    pose proof (respects_alpha_l_approx_aux_bot2 lib) as respl.
    unfold respects2_l in respl.
    pose proof (respl
                  (lsubst (lsubst u sub0) (lsubst_sub s' sub3))
                  (lsubst (lsubst u0 s') (sub0 ++ sub3))
                  (lsubst (lsubst u s') (sub0 ++ sub3)))
          as rel; clear respl.
    repeat (autodimp rel hyp).
    clear rer.

    right.
    apply hr.
    exists (lsubst u s') (lsubst u0 s') (sub0 ++ sub3).

Print nrut_sub.
XXXXXXXXXXXXX


    pose proof (pull_out_nrut_sub nt1 sub1 l) as pont1.
    repeat (autodimp pont1 hyp); eauto 3 with slow.

XXXXXXXXX

    pose proof (simple_lsubst_lsubst_sub_aeq4 u1 sub2 sub) as swap1.
    repeat (autodimp swap1 hyp); eauto 3 with slow.
    pose proof (simple_lsubst_lsubst_sub_aeq4 u2 sub2 sub) as swap2.
    repeat (autodimp swap2 hyp); eauto 3 with slow.
    repeat (rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow).
    rw swap1; rw swap2; clear swap1 swap2.

(* do I have to remove lv? *)
    pose proof (bl1 (ren_utokens_sub (nrut_subs_to_utok_ren sub2 sub1) sub)) as rr.
    repeat (autodimp rr hyp); eauto 2 with slow.
    { apply wf_sub_ren_utokens_sub; eauto with slow. }
    {
    }

XXXXXXXXXXXx

    pose proof (fresh_vars (length lv)
                           (lv ++ free_vars nt1
                               ++ free_vars nt2
                               ++ bound_vars nt1
                               ++ bound_vars nt2
                               ++ dom_sub sub1
                               ++ dom_sub sub2)) as fvs.
    exrepnd.
    allrw disjoint_app_r; repnd.

    pose proof (pull_out_nrut_sub_b_aux (bterm lv nt1) sub1 l lvn) as po1.
    allsimpl; repeat (autodimp po1 hyp); eauto 3 with slow.
    { apply alpha_eq_bterm_preserves_wf_bterm in bl2; auto.
      apply wf_bterm_lsubst_bterm_aux; eauto 2 with slow.
      rw Heqb1; apply wf_bterm_selectbt.
      apply (wf_bterms_lsubst_bterms_aux_implies bs sub2).
      apply alpha_eq_bterms_preserves_wf_bterms in aebs2; auto.
      unfold computes_to_value in comp; repnd.
      apply compute_max_steps_eauto2 in comp.
      apply isprogram_implies_wf in comp.
      apply wf_oterm_iff in comp; repnd; auto.
    }
    { simpl.
      apply alpha_eq_bterm_preserves_free_vars in bl2; allsimpl; rw <- bl2.
      erewrite @free_vars_bterm_lsubst_bterm_aux_nrut_sub; eauto.
      apply disjoint_remove_nvars_l.
      assert (subset (free_vars_bterm b1) (free_vars_bterms bs)) as ss.
      { unfold free_vars_bterms.
        apply subsetSingleFlatMap; rw Heqb1.
        apply selectbt_in; auto. }
      eapply subset_disjoint;[exact ss|].
      apply disjoint_remove_nvars_l.
      rw eqdoms.
      erewrite <- free_vars_bterms_lsubst_bterms_aux_nrut_sub; eauto.
      apply alpha_eq_bterms_preserves_free_vars in aebs2; rw <- aebs2.
      unfold computes_to_value in comp; repnd.
      apply compute_max_steps_eauto2 in comp.
      destruct comp as [cl wf].
      apply closed_oterm_iff1 in cl.
      apply null_iff_nil in cl; rw cl; auto.
    }
    { apply disjoint_app_r; dands; auto. }
    exrepnd.

    pose proof (pull_out_nrut_sub_b_aux (bterm lv nt2) sub1 l lvn) as qo1.
    allsimpl; repeat (autodimp qo1 hyp); eauto 3 with slow.
    { apply alpha_eq_bterm_preserves_wf_bterm in bl0; auto.
      apply wf_bterm_lsubst_bterm_aux; eauto 2 with slow.
      rw Heqb2; apply wf_bterm_selectbt.
      apply (wf_bterms_lsubst_bterms_aux_implies bs'' sub1).
      apply alpha_eq_bterms_preserves_wf_bterms in aebs4; auto.
      unfold computes_to_value in h5; repnd.
      apply compute_max_steps_eauto2 in h5.
      apply isprogram_implies_wf in h5.
      apply wf_oterm_iff in h5; repnd; auto.
    }
    { simpl.
      apply alpha_eq_bterm_preserves_free_vars in bl0; allsimpl; rw <- bl0.
      erewrite @free_vars_bterm_lsubst_bterm_aux_nrut_sub; eauto.
      apply disjoint_remove_nvars_l.
      assert (subset (free_vars_bterm b2) (free_vars_bterms bs'')) as ss.
      { unfold free_vars_bterms.
        apply subsetSingleFlatMap; rw Heqb2.
        apply selectbt_in; auto; try omega. }
      eapply subset_disjoint;[exact ss|].
      apply disjoint_remove_nvars_l.
      erewrite <- free_vars_bterms_lsubst_bterms_aux_nrut_sub; eauto.
      apply alpha_eq_bterms_preserves_free_vars in aebs4; rw <- aebs4.
      unfold computes_to_value in h5; repnd.
      apply compute_max_steps_eauto2 in h5.
      destruct h5 as [cl wf].
      apply closed_oterm_iff1 in cl.
      apply null_iff_nil in cl; rw cl; auto.
    }
    { apply disjoint_app_r; dands; auto. }
    exrepnd.

    assert (alpha_eq_bterm (lsubst_bterm_aux b1 sub1) (lsubst_bterm_aux u sub1)) as aeq1 by eauto 2 with slow.
    assert (alpha_eq_bterm (lsubst_bterm_aux b2 sub1) (lsubst_bterm_aux u0 sub1)) as aeq2 by eauto 2 with slow.
    apply (alpha_eq_bterm_ren_utokens_b _ _ (nrut_subs_to_utok_ren sub1 sub2)) in aeq1.
    apply (alpha_eq_bterm_ren_utokens_b _ _ (nrut_subs_to_utok_ren sub1 sub2)) in aeq2.
    repeat (rw @lsubst_aux_bterm_ren_utokens_b in aeq1).
    repeat (rw @lsubst_aux_bterm_ren_utokens_b in aeq2).
    repeat (rw @ren_utokens_b_trivial in aeq1;
            [|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; complete eauto]).
    repeat (rw @ren_utokens_b_trivial in aeq2;
            [|erewrite @dom_utok_ren_nrut_subs_to_utok_ren; complete eauto]).
    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in aeq1; eauto.
    erewrite @ren_utokens_sub_nrut_subs_to_utok_ren in aeq2; eauto.

    destruct u as [vs u1].
    destruct u0 as [vs' u2].
    allsimpl.
    subst vs vs'.
    repeat (onerw (sub_filter_disjoint1 sub1 lvn); eauto 2 with slow).
    repeat (onerw (sub_filter_disjoint1 sub2 lvn); eauto 2 with slow).

    exists lvn (lsubst_aux u1 sub2) (lsubst_aux u2 sub2); dands; auto.

    apply approx_open_simpler_equiv; eauto 3 with slow.

    unfold simpl_olift; unfold olift in bl1; repnd.

    prove_and ntwfsu1.
    {
      apply nt_wf_eq; apply lsubst_aux_preserves_wf_term2; eauto 2 with slow.
      apply alphaeqbt_preserves_nt_wf in po1.
      repeat (rw @nt_wf_eq in po1); rw @nt_wf_eq in bl3; apply po1 in bl3.
      rw <- @cl_lsubst_lsubst_aux in bl3; eauto 2 with slow.
      apply lsubst_wf_term in bl3; auto.
    }

    prove_and ntwfsu2.
    {
      apply nt_wf_eq; apply lsubst_aux_preserves_wf_term2; eauto 2 with slow.
      apply alphaeqbt_preserves_nt_wf in qo1.
      repeat (rw @nt_wf_eq in qo1); rw @nt_wf_eq in bl4; apply qo1 in bl4.
      rw <- @cl_lsubst_lsubst_aux in bl4; eauto 2 with slow.
      apply lsubst_wf_term in bl4; auto.
    }

    assert (isprogram_bt (bterm lv nt1)) as isplvnt1.
    { apply alpha_eq_bterm_preserves_isprogram_bt in bl2; auto.
      apply preserve_program in comp; auto;[|complete unflsubst].
      apply isprogram_ot_iff in comp; repnd.
      unfold alpha_eq_bterms in aebs2; repnd.
      pose proof (aebs2 (selectbt tl_subterms n) (selectbt (lsubst_bterms_aux bs sub2) n)) as h.
      unfold selectbt, lsubst_bterms_aux in h.
      autodimp h hyp.
      { apply in_nth_combine; allrw map_length; auto; try omega. }
      rw (@map_nth2 (@BTerm o) (@BTerm o) (@default_bt o)) in h; tcsp.
      unfold selectbt in Heqb1; rw <- Heqb1 in h.
      pose proof (comp (nth n tl_subterms default_bt)) as k.
      autodimp k hyp.
      { apply nth_in; auto; try omega. }
      apply alpha_eq_bterm_preserves_isprogram_bt in h; auto.

    }

    assert (isprogram_bt (bterm lv nt2)) as isplvnt2.
    {

    }

    introv wfs ispl1 ispl2.

    pose proof (simple_lsubst_lsubst_sub_aeq4 u1 sub2 sub) as swap1.
    repeat (autodimp swap1 hyp); eauto 3 with slow.
    pose proof (simple_lsubst_lsubst_sub_aeq4 u2 sub2 sub) as swap2.
    repeat (autodimp swap2 hyp); eauto 3 with slow.
    repeat (rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow).
    rw swap1; rw swap2; clear swap1 swap2.

(* rename lvn into lv in the domain of this substitution *)
    pose proof (bl1 (ren_utokens_sub (nrut_subs_to_utok_ren sub2 sub1) sub)) as rr.
    repeat (autodimp rr hyp); eauto 2 with slow.
    { apply wf_sub_ren_utokens_sub; eauto with slow. }
    {
    }

SearchAbout wf_sub ren_utokens_sub.

SearchAbout (lsubst (lsubst _ _) _).

(* replace sub2 by sub1 in sub --> sub'
   instantiate bl1 using sub'
   pull out sub1 from sub' and sub2 from sub
   use IH
 *)

Qed.
*)

Require Import sqle.


Lemma map_ren_atom_get_utokens_library_if_disjoint_dom {o} :
  forall (lib : @plibrary o) ren,
    disjoint (get_utokens_library lib) (dom_utok_ren ren)
    -> map (ren_atom ren) (get_utokens_library lib)
       = get_utokens_library lib.
Proof.
  introv disj.
  apply eq_map_l; introv i.
  apply disj in i.
  apply ren_atom_not_in; auto.
Qed.

Lemma get_utokens_lib_ren_utokens {o} :
  forall lib (t : @NTerm o) (ren : utok_ren),
    disjoint (get_utokens_library lib) (dom_utok_ren ren)
    -> get_utokens_lib lib (ren_utokens ren t)
       = map (ren_atom ren) (get_utokens_lib lib t).
Proof.
  introv disj; unfold get_utokens_lib.
  rw @get_utokens_ren_utokens.
  rw map_app.
  rewrite map_ren_atom_get_utokens_library_if_disjoint_dom; auto.
Qed.

Lemma inv_ren_utokens_lib {o} :
  forall lib (t : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens_lib lib t))
    -> ren_utokens (inv_utok_ren ren) (ren_utokens ren t) = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; tcsp.
  Case "oterm".
  allrw @ren_utokens_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

  - apply get_utok_some in Heqguo; subst; allsimpl.
    rw <- disjoint_diff_l in disj.
    rw disjoint_cons_r in disj; repnd.
    rw disjoint_diff_l in disj0.
    rw @inv_ren_atom; auto.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
    allrw <- disjoint_diff_l.
    unfold get_utokens_lib.
    allrw disjoint_app_r; repnd; dands; auto.
    disj_flat_map; allsimpl; auto.

  - rw Heqguo.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
    allrw <- disjoint_diff_l.
    allrw disjoint_app_r; repnd.
    disj_flat_map; allsimpl; auto.
Qed.

Definition get_utokens_lib_b {o} lib (b : @BTerm o) :=
  get_utokens_b b ++ get_utokens_library lib.

Lemma get_utokens_lib_b_tl_subterms_subset_get_utokens_lib {o} :
  forall (lib : @plibrary o) op bs n,
    n < length bs
    -> subset (get_utokens_lib_b lib (bs {[n]}))
              (get_utokens_lib lib (oterm op bs)).
Proof.
  introv ltn i; unfold get_utokens_lib_b in i; unfold get_utokens_lib.
  allrw in_app_iff; simpl in *; repndors; tcsp.
  left; right.
  rw lin_flat_map.
  exists (selectbt bs n); dands; auto.
  apply selectbt_in; auto.
Qed.

Lemma get_utokens_lib_b_ren_utokens_b {o} :
  forall lib (b : @BTerm o) (ren : utok_ren),
    disjoint (get_utokens_library lib) (dom_utok_ren ren)
    -> get_utokens_lib_b lib (ren_utokens_b ren b)
       = map (ren_atom ren) (get_utokens_lib_b lib b).
Proof.
  introv disj; unfold get_utokens_lib_b.
  rw @get_utokens_b_ren_utokens_b.
  rw map_app.
  rewrite map_ren_atom_get_utokens_library_if_disjoint_dom; auto.
Qed.

Lemma subset_get_utokens_lib_oterm_implies_b {o} :
  forall lib op (bs : list (@BTerm o)) l b,
    LIn b bs
    -> subset (get_utokens_lib lib (oterm op bs)) l
    -> subset (get_utokens_lib_b lib b) l.
Proof.
  introv i ss j.
  unfold get_utokens_lib in ss; unfold get_utokens_lib_b in j.
  apply ss; clear ss; allrw in_app_iff.
  repndors; tcsp.
  left; right.
  apply lin_flat_map.
  eexists; dands; eauto.
Qed.

Lemma inv_ren_utokens2_lib {o} :
  forall lib (t : @NTerm o) ren,
    no_repeats (dom_utok_ren ren)
    -> disjoint (dom_utok_ren ren) (diff (get_patom_deq o) (range_utok_ren ren) (get_utokens_lib lib t))
    -> ren_utokens ren (ren_utokens (inv_utok_ren ren) t) = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; tcsp.
  Case "oterm".
  allrw @ren_utokens_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

  - apply get_utok_some in Heqguo; subst; allsimpl.
    rw <- disjoint_diff_l in disj.
    rw disjoint_cons_r in disj; repnd.
    rw disjoint_diff_l in disj0.
    rw @inv_ren_atom2; auto.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
    allrw <- disjoint_diff_l.
    unfold get_utokens_lib.
    allrw disjoint_app_r; repnd; dands; auto.
    disj_flat_map; allsimpl; auto.

  - rw Heqguo.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
    allrw <- disjoint_diff_l.
    allrw disjoint_app_r; repnd.
    disj_flat_map; allsimpl; auto.
Qed.

Lemma inv_ren_utokens_b2_lib {o} :
  forall lib (b : @BTerm o) ren,
    no_repeats (dom_utok_ren ren)
    -> disjoint (dom_utok_ren ren) (diff (get_patom_deq o) (range_utok_ren ren) (get_utokens_lib_b lib b))
    -> ren_utokens_b ren (ren_utokens_b (inv_utok_ren ren) b) = b.
Proof.
  introv norep disj.
  destruct b as [l t]; allsimpl.
  f_equal; apply (inv_ren_utokens2_lib lib); auto.
Qed.

Lemma approx_change_utoks {o} :
  forall lib (t1 t2 : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (get_utokens_library lib) (range_utok_ren ren)
    -> disjoint (get_utokens_library lib) (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens_lib lib t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens_lib lib t2))
    -> approx lib t1 t2
    -> approx lib (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  introv nr1 nr2 dl1 dl2 d1 d2 apr.
  allrw @approx_sqle.
  allunfold @sqle.
  intro m.
  pose proof (apr m) as h; clear apr.
  revert t1 t2 ren nr1 nr2 dl1 dl2 d1 d2 h.

  induction m; introv norep1 norep2 dl1 dl2 disj1 disj2 apr.

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
      eauto 3 with slow;
      [|rewrite get_utokens_lib_ren_utokens; auto;
        apply disjoint_dom_diff_range_map_ren_atom];[].

    rw (inv_ren_utokens_lib lib) in comp1; auto.

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
      rw @get_utokens_lib_ren_utokens in comp3; auto.
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
    eapply (subset_trans _ (get_utokens_lib_b lib b1)) in ss1;
      [|subst b1; apply get_utokens_lib_b_tl_subterms_subset_get_utokens_lib; auto].

    apply (subset_map_map (ren_atom (inv_utok_ren ren))) in ss1.

    rw <- @get_utokens_lib_b_ren_utokens_b in ss1; auto;
      [|rewrite dom_utok_ren_inv_utok_ren; auto];[].
    rw <- @get_utokens_lib_ren_utokens in ss1; auto;
      [|rewrite dom_utok_ren_inv_utok_ren; auto];[].
    rw (inv_ren_utokens_lib lib) in ss1; auto;[].
    applydup @alpha_eq_bterm_preserves_utokens in i2 as put1; allsimpl.

    unfold get_utokens_lib_b in ss1.
    rw put1 in ss1; clear put1.
    fold (get_utokens_lib lib nt1) in ss1.

    applydup @computes_to_value_preserves_utokens in comp22 as ss2; allsimpl; eauto 3 with slow.
    eapply (subset_trans _ (get_utokens_lib_b lib b2)) in ss2;
      [|subst b2; apply get_utokens_lib_b_tl_subterms_subset_get_utokens_lib;
        auto; rw <- comp3; auto];[].

    applydup @alpha_eq_bterm_preserves_utokens in i1 as put2; allsimpl.

    unfold get_utokens_lib_b in ss2.
    rw put2 in ss2; clear put2.
    fold (get_utokens_lib lib nt2) in ss2.

    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i1.
    apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i2.

    assert (disjoint (dom_utok_ren ren)
                     (diff (get_patom_deq o)
                           (range_utok_ren ren)
                           (get_utokens_lib_b lib b1))) as d.
    {
      apply computes_to_value_preserves_utokens in comp; allsimpl; eauto 3 with slow.
      assert (LIn b1 tl_subterms) as itl.
      { subst b1; unfold selectbt; apply nth_in; auto. }

      eapply subset_get_utokens_lib_oterm_implies_b in comp;[|exact itl].
      rw @get_utokens_lib_ren_utokens in comp; auto;[].
      rw <- disjoint_diff_l.
      eapply subset_disjoint_r;[|exact comp].
      rw disjoint_diff_l.
      apply disjoint_dom_diff_range_map_ren_atom.
    }

    rw (inv_ren_utokens_b2_lib lib) in i2; auto;[].
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
                  (get_utokens nt1 ++ get_utokens nt2 ++ get_utokens_library lib)) as exren.
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

    assert (disjoint (get_utokens_library lib) (range_utok_ren ren')) as disjl'.
    {
      clear sqn.
      introv j k.
      apply exren4 in k; rw in_app_iff in k.
      applydup exren8 in j.
      applydup dl2 in j.
      repndors; tcsp.
    }

    repeat (autodimp sqn hyp); dands; eauto 3 with slow.

    { introv a b; applydup disj1 in a.
      allrw in_diff; allrw in_app_iff.
      allrw not_over_or; repnd.
      apply not_over_and in a0;
        [|destruct (in_deq _ (get_patom_deq o) t (get_utokens t1));
          try (complete (left; tcsp));
          destruct (in_deq _ (get_patom_deq o) t (get_utokens_library lib));
          try (complete (left; tcsp));
          right; tcsp];[].
      repndors; tcsp;[].
      allrw not_over_or; repnd.

      apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp;
        [apply (get_utokens_subset_get_utokens_lib lib) in b0;
         apply ss1 in b0;
         unfold get_utokens_lib in b0; rw in_app_iff in b0; tcsp|];[].

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
      allrw in_diff; allrw in_app_iff.
      allrw not_over_or; repnd.
      apply not_over_and in a0;
        [|destruct (in_deq _ (get_patom_deq o) t (get_utokens t1));
          try (complete (left; tcsp));
          destruct (in_deq _ (get_patom_deq o) t (get_utokens_library lib));
          try (complete (left; tcsp));
          right; tcsp];[].
      repndors; tcsp;[].
      allrw not_over_or; repnd.

      apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp;
        [apply (get_utokens_subset_get_utokens_lib lib) in b0;
         apply ss2 in b0;
         unfold get_utokens_lib in b0; rw in_app_iff in b0; tcsp|];[].

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
      eauto 3 with slow;
      [|rw @get_utokens_lib_ren_utokens; auto;
        apply disjoint_dom_diff_range_map_ren_atom].

    rw (inv_ren_utokens_lib lib) in comp1; auto.

    dup comp1 as comp2.
    apply cl3 in comp2; exrepnd.
    dup comp0 as comp00.
    apply (computes_to_exception_ren_utokens _ _ _ _ ren) in comp0; eauto 3 with slow.

    eexists; eexists; dands;[exact comp0|idtac|].

    {
      pose proof (IHm (ren_utokens (inv_utok_ren ren) a) a' ren) as h.
      repeat (autodimp h hyp).

      { apply computes_to_exception_preserves_utokens in comp1; repnd; eauto 3 with slow. }

      { apply computes_to_exception_preserves_utokens in comp00; repnd; eauto 3 with slow. }

      rw (inv_ren_utokens2_lib lib) in h; auto.
      apply computes_to_exception_preserves_utokens in comp; repnd; eauto 3 with slow.
      introv i j.
      rw @get_utokens_lib_ren_utokens in comp4; auto.
      apply (disjoint_dom_diff_range_map_ren_atom (get_utokens_lib lib t1)) in i; destruct i.
      allrw in_diff; repnd; dands; auto.
    }

    {
      pose proof (IHm (ren_utokens (inv_utok_ren ren) e) e' ren) as h.
      repeat (autodimp h hyp).

      { apply computes_to_exception_preserves_utokens in comp1; repnd; eauto 3 with slow. }

      { apply computes_to_exception_preserves_utokens in comp00; repnd; eauto 3 with slow. }

      rw (inv_ren_utokens2_lib lib) in h; auto.
      apply computes_to_exception_preserves_utokens in comp; repnd; eauto 3 with slow.
      introv i j.
      rw @get_utokens_lib_ren_utokens in comp; auto.
      apply (disjoint_dom_diff_range_map_ren_atom (get_utokens_lib lib t1)) in i; destruct i.
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
