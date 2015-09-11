(*

  Copyright 2014 Cornell University

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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export approx_star_props1.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

Hint Resolve approx_star_relates_only_wf : slow.


Lemma alpha_implies_approx_star {p} :
  forall lib nt1 nt2,
  @nt_wf p nt1
  -> alpha_eq nt1 nt2
  -> approx_star lib nt1 nt2.
Proof.
  introv H1nt H2nt.
  apply approx_open_implies_approx_star.
  apply alpha_implies_approx_open; trivial.
Qed.

Lemma approx_star_trans {p} : forall lib t1 t2 t3,
  @approx_star p lib t1 t2
  -> approx_star lib t2 t3
  -> approx_star lib t1 t3.
Proof.
  nterm_ind1s t1 as [v1|f ind|o lbt1 Hind] Case; introv H1as H2as;
  inversion H1as as [? ? ? aop|?|]; subst; clear H1as.
Abort. (** see comments above for approx_star_open_trans*)

Lemma le_approx_ntwf {p} :
  forall lib, le_bin_rel (approx_star lib) (indep_bin_rel nt_wf (@nt_wf p)).
Proof.
  eauto with slow.
Qed.

Lemma approx_rel_wf_sub {p} :
  forall lib lvi lnta lntb,
  bin_rel_nterm (@approx_star p lib) lnta lntb
  -> wf_sub (combine lvi lnta) # wf_sub (combine lvi lntb).
Proof.
  introv Hb. apply (le_binrel_list_un _ _ _ _ (le_approx_ntwf lib)) in Hb.
  exrepnd. unfold wf_sub, sub_range_sat.   dands; eauto with slow.
Qed.

Lemma approx_star_btermd_fr {p} :
  forall lib op bt1 bt2 lva,
    op = NCan NFresh
    -> approx_star_bterm lib op bt1 bt2
    -> {lvn : list NVar
        & {nt1',nt2' : @NTerm p
        $ {sub : Sub
        $ approx_star lib (lsubst nt1' sub) (lsubst nt2' sub)
        # nrut_sub (get_utokens nt1' ++ get_utokens nt2') sub
        # lvn = dom_sub sub
        # alpha_eq_bterm bt1 (bterm lvn nt1')
        # alpha_eq_bterm bt2 (bterm lvn nt2')
        # no_repeats lvn
        (* # disjoint lvn (all_vars (get_nt bt1) ++ all_vars (get_nt bt2)) *)
        # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva }}}.
Proof.
  introv d Hab.
  unfold approx_star_bterm in Hab.
  repnud Hab. exrepnd.
  pose proof (alpha_bterm_pair_change _ _ _ _ _ lva Hab2 Hab0) as Hp.
  exrepnd.
  exists lvn.

  repndors; exrepnd; subst; tcsp; GC.
  allrw disjoint_app_r; allrw disjoint_app_l; repnd.

  exists (lsubst nt1n (var_ren (dom_sub sub) lvn))
         (lsubst nt2n (var_ren (dom_sub sub) lvn))
         (combine lvn (range sub)).
  rw @boundvars_lsubst_vars; auto.
  rw @boundvars_lsubst_vars; auto.
  rw @get_utokens_lsubst_allvars; eauto 3 with slow.
  rw @get_utokens_lsubst_allvars; eauto 3 with slow.
  rw @dom_sub_combine; allrw @length_range; allrw @length_dom; auto.

  dands; eauto 3 with slow.

  - pose proof (lsubst_nest_same_alpha nt1n (dom_sub sub) lvn (range sub)) as nest1.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest1 hyp).
    { apply alphaeq_preserves_free_vars in Hp2; rw <- Hp2; auto. }
    rw <- @sub_eta in nest1.

    pose proof (lsubst_nest_same_alpha nt2n (dom_sub sub) lvn (range sub)) as nest2.
    allrw @length_dom; allrw @length_range.
    repeat (autodimp nest2 hyp).
    { apply alphaeq_preserves_free_vars in Hp3; rw <- Hp3; auto. }
    rw <- @sub_eta in nest2.

    pose proof (lsubst_alpha_congr2 nt1 nt1n sub Hp2) as as1.
    pose proof (lsubst_alpha_congr2 nt2 nt2n sub Hp3) as as2.

    eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym; exact nest1].
    eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym; exact nest2].
    eauto 3 with slow.

  - apply alphaeq_preserves_utokens in Hp2.
    apply alphaeq_preserves_utokens in Hp3.
    rw <- Hp2; rw <- Hp3.
    eapply nrut_sub_change_sub_same_range;[|exact Hab5].
    rw @range_combine; auto; allrw @length_range; allrw @length_dom; auto.

  - allrw disjoint_app_l; dands; auto.
Qed.

(*
Lemma change_nr_ut_sub_in_lsubst_aux_approx_star {o} :
  forall lib (t1 t2 : @NTerm o) sub1 sub2 l,
    wf_term t1
    -> wf_term t2
    -> approx_star lib (lsubst_aux t1 sub1) (lsubst_aux t2 sub1)
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> nrut_sub l sub1
    -> nrut_sub l sub2
    -> dom_sub sub1 = dom_sub sub2
    -> approx_star lib (lsubst_aux t1 sub2) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v|op bs ind] Case;
  introv w1 s2 ap ss1 ss2 nrut1 nrut2 eqdoms; allsimpl.

Focus 2.
{
  destruct t2 as [v2|op2 bs2]; allsimpl.

Focus 2.
{
  
}

  - pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v2 l) as e.
    repeat (autodimp e hyp).
    remember (sub_find sub1 v2) as sf; symmetry in Heqsf; destruct sf.

(*
Focus 2.
{
  rw e.
  inversion ap as [? ? ? ao|]; subst; clear ap.
  constructor.
       apply approx_open_vterm_iff_reduces_to in ao;
       [|apply lsubst_aux_preserves_wf_term2; eauto with slow];
       apply approx_open_vterm_iff_reduces_to;
       [apply lsubst_aux_preserves_wf_term2; eauto with slow|];
       apply (reduces_to_vterm_nrut_sub_change lib t2 sub1 sub2 l); auto
}
*)

    + exrepnd; rw e0.
      applydup @sub_find_some in Heqsf.
      eapply in_nrut_sub in Heqsf0; eauto.
      exrepnd; subst.
      inversion ap as [|? ? ? ? ? len lift apo]; subst; allsimpl; cpx; clear ap.
      allrw map_length.
      apply approx_open_simpler_equiv in apo.
      unfold simpl_olift in apo; repnd.
      pose proof (apo (ax_sub (free_vars (oterm op lbt1')))) as ap; clear apo.
      repeat (autodimp ap hyp).
      { apply isprogram_lsubst_prog_sub; eauto 3 with slow.
        rw @dom_sub_ax_sub; auto. }
      { rw @cl_lsubst_lsubst_aux; eauto 1 with slow.
        simpl; repeat constructor; simpl; sp. }
      repeat (rw @cl_lsubst_lsubst_aux in ap; eauto 1 with slow).
      simpl in ap.
      allfold (@mk_utoken o a0).

SearchAbout dom_sub ax_sub.
}

  - Case "vterm".
    pose proof (sub_find_some_eq_doms_nrut_sub sub1 sub2 v l) as h.
    repeat (autodimp h hyp).
    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1; exrepnd;
    [|rw h;
       inversion ap as [? ? ? ao|]; subst; clear ap;
       constructor;
       apply approx_open_vterm_iff_reduces_to in ao;
       [|apply lsubst_aux_preserves_wf_term2; eauto with slow];
       apply approx_open_vterm_iff_reduces_to;
       [apply lsubst_aux_preserves_wf_term2; eauto with slow|];
       apply (reduces_to_vterm_nrut_sub_change lib t2 sub1 sub2 l); auto
    ].

    rw h0.
    apply (apso _ _ _ _ []); simpl; auto; fold_terms.
    { unfold lblift_sub; simpl; tcsp. }
    dup Heqsf1 as i.
    apply sub_find_some in Heqsf1.
    eapply in_nrut_sub in Heqsf1; eauto; exrepnd; subst.
    assert (!LIn a0 (get_utokens t2)) as ni by (intro k; apply ss2 in k; sp).
    inversion ap as [|? ? ? ? ? len lift apo]; subst; allsimpl; cpx; clear lift ap.
    fold_terms.

    apply approx_open_simpler_equiv in apo.
    unfold simpl_olift in apo; repnd.

    apply approx_open_simpler_equiv.
    apply lsubst_aux_nt_wf in apo1.
    unfold simpl_olift; dands; eauto 3 with slow.
    introv ps isp1 isp2.
    rw (cl_lsubst_trivial (mk_utoken a)); simpl; eauto 3 with slow.

    (* replace the [a]s in sub by [a0]s to build a sub' and instantiate apo using that? *)

    rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
    rw <- @cl_lsubst_lsubst_aux in isp2; eauto 2 with slow.
    rw @cl_lsubst_swap_sub_filter; eauto 2 with slow.
    rw @cl_lsubst_swap_sub_filter in isp2; eauto 2 with slow.
    remember (sub_filter sub (dom_sub sub2)) as sub0.

Lemma pull_out_nrut_sub_from_term {o} :
  forall (t : @NTerm o) (sub : @Sub o) l,
    nrut_sub l sub
    -> {t' : NTerm
        & t = lsubst t' sub
        # disjoint (get_utokens t) (get_utokens_sub sub)}.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv nrut; allsimpl.

  - exists ([] : @Sub o); simpl; dands; auto.
    unfold get_utokens_sub; simpl; auto.

  - destruct x as [v t].
    pose proof (IHsub1 sub2 l nrut) as h; exrepnd.
Qed.

Lemma pull_out_nrut_sub_from_sub {o} :
  forall (sub1 sub2 : @Sub o) l,
    nrut_sub l sub2
    -> {sub : Sub
        & sub1 = lsubst_sub sub sub2
        # disjoint (get_utokens_sub sub) (get_utokens_sub sub2)}.
Proof.
  induction sub1 as [|x sub1]; introv nrut.

  - exists ([] : @Sub o); simpl; dands; auto.
    unfold get_utokens_sub; simpl; auto.

  - destruct x as [v t].
    pose proof (IHsub1 sub2 l nrut) as h; exrepnd.
Qed.

      remember (ren_utokens_sub (nrut_subs_to_utok_ren sub2 sub1) sub0) as sub0'.

      pose proof (dom_sub_ren_utokens_sub (nrut_subs_to_utok_ren sub2 sub1) sub0) as eqdoms0.
      rw <- Heqsub0' in eqdoms0.

      pose proof (apo sub0') as h; clear apo.
      rw <- @cl_lsubst_lsubst_aux in h; eauto 2 with slow.

      assertdimp h hh.
      { subst; eauto with slow. }
      rw @cl_lsubst_swap_sub_filter in h; eauto 2 with slow.
      rw eqdoms in h.
      rw @sub_filter_disjoint1 in h;
        [|rw eqdoms0; rw Heqsub0; rw <- @dom_sub_sub_filter; complete (eauto with slow)].
      rw (cl_lsubst_trivial (mk_utoken a0)) in h; simpl; eauto 2 with slow.

      repeat (assertdimp h hh); eauto 2 with slow.
      { apply (prog_sub_change sub2 sub1); eauto 2 with slow.
        apply lsubst_program_implies in isp2.
        unfold isprogram; dands.
        - unfold closed.
          rw @free_vars_cl_lsubst; eauto 2 with slow.
          apply null_iff_nil.
          apply null_remove_nvars_subvars.
          eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
          rw eqdoms0.
          apply subvars_eq in isp2.
          eapply subvars_eqvars in isp2;[|apply eqvars_free_vars_disjoint].
          rw Heqsub0'.
          rw @sub_keep_first_ren_utokens_sub.
          rw @sub_free_vars_ren_utokens_sub; auto.
        - apply lsubst_wf_if_eauto; eauto with slow. }

      apply approx_utoken_implies_reduces_to in h.
      apply reduces_to_implies_approx1; auto.

(* pull out the atoms from [lsubst t2 sub0'] in [h]
   and from [lsubst t2 sub0] in the conclusion.
   Something like that, maybe:
 *)

Lemma xxx {o} :
  forall (t : @NTerm o) (sub sub1 sub2 : @Sub o) l,
    let sub' := ren_utokens_sub (nrut_subs_to_utok_ren sub2 sub1) sub in
    nrut_sub l sub1
    -> nrut_sub l sub2
    -> dom_sub sub1 = dom_sub sub2
    -> {sub0 : Sub
        & sub' = lsubst_sub sub0 sub1
        # sub  = lsubst_sub sub0 sub2
        # disjoint (get_utokens_sub sub1) (get_utokens_sub sub0)
        # disjoint (get_utokens_sub sub2) (get_utokens_sub sub0)}.

Check reduces_in_atmost_k_steps_change_utok_sub.

XXXXXXX

      unfold reduces_to in h; exrepnd.

(*
      pose proof (reduces_in_atmost_k_steps_change_utok_sub
                    lib k t (mk_utoken a0) sub1 sub2) as h.
      repeat (autodimp h hyp); eauto 3 with slow.
*)

(*
XXXXXXXXXXXXXXXXXX

      pose proof (apo sub) as h; clear apo.
      rw (cl_lsubst_trivial (mk_utoken a0)) in h; simpl; eauto 3 with slow.
      repeat (autodimp h hyp); eauto 2 with slow.
      { rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
        rw <- @cl_lsubst_lsubst_aux in isp2; eauto 2 with slow.
        rw @cl_lsubst_swap_sub_filter in isp2; eauto 2 with slow.
        rw @cl_lsubst_swap_sub_filter; eauto 2 with slow.
        rw eqdoms.
        eapply prog_sub_change; eauto with slow. }

      rw <- @cl_lsubst_lsubst_aux in h; eauto 2 with slow.
      rw @cl_lsubst_swap_sub_filter in h; eauto 2 with slow.
      rw eqdoms in h.

      remember (lsubst t2 (sub_filter sub (dom_sub sub2))) as t.

      apply approx_utoken_implies_reduces_to in h.
      unfold reduces_to in h; exrepnd.
      pose proof (reduces_in_atmost_k_steps_change_utok_sub
                    lib k t (mk_utoken a0) sub1 sub2) as h.
      repeat (autodimp h hyp); eauto 3 with slow.

      assert (subset (get_utokens t) l) as ss3.
      {
        subst; introv j; apply get_utokens_lsubst in j.
        allrw in_app_iff; repndors; tcsp.
        rw @sub_keep_first_sub_filter in j.
        apply in_get_utokens_sub in j; exrepnd.
        apply in_sub_filter in j0; repnd.
        apply in_sub_keep_first in j2; repnd.

      }
*)

Abort.
*)


Lemma isprogram_ren_utokens_iff {o} :
  forall (ren : @utok_ren o) (t : NTerm),
    isprogram (ren_utokens ren t) <=> isprogram t.
Proof.
  introv; split; intro k; try (apply isprogram_ren_utokens); auto.
  allunfold @isprogram; repnd; allunfold @closed.
  allrw @free_vars_ren_utokens; dands; auto.
  allrw @nt_wf_ren_utokens_iff; auto.
Qed.

Lemma prog_sub_ren_utokens_sub_iff {o} :
  forall (ren : @utok_ren o) (sub : Sub),
    prog_sub (ren_utokens_sub ren sub) <=> prog_sub sub.
Proof.
  induction sub; allsimpl; tcsp.
  destruct a as [v t]; allsimpl; allrw @prog_sub_cons.
  rw IHsub; rw @isprogram_ren_utokens_iff; sp.
Qed.

Lemma approx_open_change_utoks {o} :
  forall lib (t1 t2 : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
    -> approx_open lib t1 t2
    -> approx_open lib (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  introv norep1 norep2 disj1 disj2 apo.

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift.
  repnd.
  allrw @nt_wf_ren_utokens_iff; dands; auto.
  introv ps isp1 isp2.

  pose proof (ex_ren_utokens_sub
                sub
                ren
                (get_utokens t1 ++ get_utokens t2)) as exren.
  autodimp exren hyp; exrepnd.

  pose proof (apo sub') as h.
  repeat (autodimp h hyp).
  { subst; allrw @prog_sub_ren_utokens_sub_iff; auto. }
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

  pose proof (approx_change_utoks lib (lsubst t1 sub') (lsubst t2 sub') (ren ++ ren')) as k.
  allrw @range_utok_ren_app.
  allrw @dom_utok_ren_app.
  allrw no_repeats_app.
  allrw disjoint_app_l.
  allrw disjoint_app_r.
  repnd.
  repeat (autodimp k hyp); dands; eauto 3 with slow.

    { introv a b; applydup disj1 in a.
      allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
      apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
      apply in_get_utokens_sub in b0; exrepnd.
      apply in_sub_keep_first in b2; repnd.
      pose proof (exren1 t) as hh.
      repeat (autodimp hh hyp).
      rw lin_flat_map; apply sub_find_some in b3; apply in_sub_eta in b3; repnd.
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
      apply in_sub_keep_first in b2; repnd.
      pose proof (exren1 t) as hh.
      repeat (autodimp hh hyp).
      rw lin_flat_map; apply sub_find_some in b3; apply in_sub_eta in b3; repnd.
      eexists; dands; eauto.
    }

    { eapply subset_disjoint;[exact exren4|].
      apply disjoint_app_l; dands.
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
      { apply disjoint_diff_l; rw diff_nil_if_subset; eauto with slow. }
    }

    { repeat (rw @lsubst_ren_utokens in k).
      rw exren0 in k.
      repeat (rw @ren_utokens_app_weak_l in k; eauto 2 with slow).
    }
Qed.

Definition utok_ren_cond2 {o} atoms (ren ren' : @utok_ren o) :=
  forall a,
    LIn a atoms
    -> LIn a (range_utok_ren ren)
    -> !LIn a (dom_utok_ren ren)
    -> LIn a (dom_utok_ren ren').

Definition utok_ren_cond2_nil {o} :
  forall (ren1 ren2 : @utok_ren o),
    utok_ren_cond2 [] ren1 ren2.
Proof.
  introv i j k; allsimpl; tcsp.
Qed.
Hint Resolve utok_ren_cond2_nil : slow.

Definition utok_ren_cond2_app {o} :
  forall atoms1 atoms2 (ren1 ren2 : @utok_ren o),
    utok_ren_cond2 atoms1 ren1 ren2
    -> utok_ren_cond2 atoms2 ren1 ren2
    -> utok_ren_cond2 (atoms1 ++ atoms2) ren1 ren2.
Proof.
  introv c1 c2 i j k; allsimpl; tcsp.
  allrw in_app_iff; repndors.
  - apply c1 in i; repeat (autodimp i hyp).
  - apply c2 in i; repeat (autodimp i hyp).
Qed.
Hint Resolve utok_ren_cond2_app : slow.

Lemma ex_ren_atom2 {o} :
  forall (a : get_patom_set o) ren atoms,
    {ren' : utok_ren
     & disjoint (range_utok_ren ren') (a :: atoms ++ dom_utok_ren ren ++ range_utok_ren ren)
     # disjoint (dom_utok_ren ren') (dom_utok_ren ren)
     # subset (dom_utok_ren ren') (range_utok_ren ren)
     # subset (dom_utok_ren ren') [a]
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond2 [a] ren ren' }.
Proof.
  introv.
  destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)) as [d|d].

  - exists ([] : @utok_ren o); allsimpl; dands; tcsp.
    introv i j k; allsimpl; repndors; subst; tcsp.

  - destruct (in_deq _ (get_patom_deq o) a (range_utok_ren ren)) as [r|r].

    + pose proof (fresh_atom o (a :: atoms ++ dom_utok_ren ren ++ range_utok_ren ren)) as h.
      exrepnd.
      exists [(a,x)]; simpl.
      allrw disjoint_singleton_l.
      rw singleton_subset.
      dands; auto.
      introv i j k; allsimpl; repndors; subst; tcsp.

    + exists ([] : @utok_ren o); allsimpl; dands; tcsp.
      introv i j k; allsimpl; repndors; subst; tcsp.
Qed.

Lemma ex_ren_utokens_o2 {o} :
  forall (op : @Opid o) ren atoms,
    {ren' : utok_ren
     & disjoint (range_utok_ren ren') (get_utokens_o op ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren)
     # disjoint (dom_utok_ren ren') (dom_utok_ren ren)
     # subset (dom_utok_ren ren') (range_utok_ren ren)
     # subset (dom_utok_ren ren') (get_utokens_o op)
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond2 (get_utokens_o op) ren ren' }.
Proof.
  introv.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
  - apply get_utok_some in Heqguo; subst; allsimpl.
    pose proof (ex_ren_atom2 g ren atoms) as h; exrepnd.
    exists ren'; dands; auto.
  - exists ([] : @utok_ren o); allsimpl; dands; auto.
    apply get_utok_none in Heqguo; allrw; eauto with slow.
Qed.

Lemma ex_ren_utokens2 {o} :
  forall (t : @NTerm o) ren atoms,
    {ren' : utok_ren
     & disjoint (range_utok_ren ren') (get_utokens t ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren)
     # disjoint (dom_utok_ren ren') (dom_utok_ren ren)
     # subset (dom_utok_ren ren') (range_utok_ren ren)
     # subset (dom_utok_ren ren') (get_utokens t)
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond2 (get_utokens t) ren ren' }.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv.

  - Case "vterm".
    exists ([] : @utok_ren o); simpl; dands; eauto with slow.

  - Case "sterm".
    exists ([] : @utok_ren o); simpl; dands; eauto with slow.

  - Case "oterm".

    assert
      (forall atoms ren,
         {ren' : utok_ren
          & disjoint (range_utok_ren ren') (get_utokens_bs bs ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren)
          # disjoint (dom_utok_ren ren') (dom_utok_ren ren)
          # subset (dom_utok_ren ren') (range_utok_ren ren)
          # subset (dom_utok_ren ren') (get_utokens_bs bs)
          # no_repeats (dom_utok_ren ren')
          # no_repeats (range_utok_ren ren')
          # utok_ren_cond2 (get_utokens_bs bs) ren ren' }) as ebs.
    { clear ren atoms.
      induction bs; introv.
      - exists ([] : @utok_ren o); simpl; dands; eauto with slow.
      - destruct a as [l t].
        autodimp IHbs hyp.
        { introv i; apply (ind nt lv); eauto; simpl; sp. }
        pose proof (IHbs (atoms ++ get_utokens t) ren) as ibs; clear IHbs; exrepnd; allsimpl.
        pose proof (ind t l) as h; clear ind; autodimp h hyp.
        pose proof (h (ren ++ ren') (get_utokens_bs bs ++ atoms)) as k; clear h; exrepnd.
        exists (ren' ++ ren'0); simpl.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw no_repeats_app.
        allrw disjoint_app_l.
        allrw subset_app.
        allrw disjoint_app_r.
        allrw app_assoc.
        repnd; dands; eauto 2 with slow.

        {
          introv i; applydup k3 in i as j; allrw in_app_iff; repndors; tcsp.
          apply k4 in i; apply ibs8 in j; sp.
        }

        {
          apply utok_ren_cond2_app; auto.
          - introv i j k.
            applydup k0 in i.
            allrw @range_utok_ren_app.
            allrw @dom_utok_ren_app.
            allrw in_app_iff; allrw not_over_or.
            destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren')) as [d|d]; tcsp.
          - introv i j k.
            applydup ibs0 in i.
            allrw @dom_utok_ren_app; allrw in_app_iff.
            repeat (autodimp i0 hyp).
        }
    }

    pose proof (ebs (atoms ++ get_utokens_o op) ren) as ebs'; clear ebs; exrepnd.

    pose proof (ex_ren_utokens_o2 op (ren ++ ren') (get_utokens_bs bs ++ atoms)) as eop; exrepnd.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw disjoint_app_l; repnd.
    allrw disjoint_app_r; repnd.

    exists (ren' ++ ren'0); simpl.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw subset_app.
    allrw disjoint_app_l; allrw disjoint_app_r.
    repeat (rw app_assoc).
    dands; eauto 3 with slow.

    {
      introv i; applydup eop3 in i as j; allrw in_app_iff; repndors; tcsp.
      apply eop4 in i; apply ebs'8 in j; sp.
    }

    {
      apply utok_ren_cond2_app; auto.
      - introv i j k.
        applydup eop0 in i.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw in_app_iff; allrw not_over_or.
        destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren')) as [d|d]; tcsp.
      - introv i j k.
        applydup ebs'0 in i.
        allrw @dom_utok_ren_app; allrw in_app_iff.
        repeat (autodimp i0 hyp).
    }
Qed.

Lemma ex_ren_utokens_sub2 {o} :
  forall (sub : @Sub o) ren atoms,
    {ren' : utok_ren
     & disjoint (range_utok_ren ren') (get_utokens_sub sub ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren)
     # disjoint (dom_utok_ren ren') (dom_utok_ren ren)
     # subset (dom_utok_ren ren') (range_utok_ren ren)
     # subset (dom_utok_ren ren') (get_utokens_sub sub)
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond2 (get_utokens_sub sub) ren ren' }.
Proof.
  induction sub; introv.
  - exists ([] : @utok_ren o); simpl; rw @get_utokens_sub_nil; dands; eauto with slow.
  - destruct a as [v t]; allsimpl.
    pose proof (IHsub ren (atoms ++ get_utokens t)) as ih; clear IHsub; exrepnd.

    pose proof (ex_ren_utokens2 t (ren ++ ren') (get_utokens_sub sub ++ atoms)) as h; exrepnd.

    exists (ren' ++ ren'0); simpl.
    repeat (rw app_assoc).
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw @get_utokens_sub_cons.
    allrw disjoint_app_l; allrw disjoint_app_r.
    allrw subset_app.

    repnd; dands; eauto 3 with slow.

    {
      introv i; applydup h3 in i as j; allrw in_app_iff; repndors; tcsp.
      apply h4 in i; apply ih8 in j; sp.
    }

    {
      apply utok_ren_cond2_app; auto.
      - introv i j k.
        applydup h0 in i.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw in_app_iff; allrw not_over_or.
        destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren')) as [d|d]; tcsp.
      - introv i j k.
        applydup ih0 in i.
        allrw @dom_utok_ren_app; allrw in_app_iff.
        repeat (autodimp i0 hyp).
    }
Qed.

Lemma ren_utokens_o_app_weak_l {o} :
  forall (op : @Opid o) ren1 ren2,
    disjoint (dom_utok_ren ren2) (get_utokens_o op)
    -> ren_utok_op (ren1 ++ ren2) op
       = ren_utok_op ren1 op.
Proof.
  introv disj.
  destruct op; tcsp.
  destruct c; tcsp.
  allsimpl.
  allrw disjoint_cons_r; repnd.
  rw @ren_atom_app_weak_l; auto.
Qed.

Lemma length_ren_utokens_bs {o} :
  forall (bs : list (@BTerm o)) ren,
    length (ren_utokens_bs ren bs) = length bs.
Proof.
  induction bs; introv; allsimpl; tcsp.
Qed.

Lemma ren_utok_op_diff_fresh {o} :
  forall (op : @Opid o) ren,
    (ren_utok_op ren op = NCan NFresh) <=> (op = NCan NFresh).
Proof.
  introv; split; intro e; subst; tcsp.
  destruct op; tcsp.
  destruct c; tcsp.
  allsimpl; ginv.
Qed.

Lemma ut_sub_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren,
    ut_sub sub
    -> ut_sub (ren_utokens_sub ren sub).
Proof.
  induction sub; introv uts; allsimpl; tcsp.
  destruct a as [v t]; allrw @ut_sub_cons; repnd; dands; tcsp.
  allunfold @isutoken; exrepnd; subst; allsimpl; fold_terms.
  eexists; dands; eauto.
Qed.
Hint Resolve ut_sub_ren_utokens_sub : slow.

Lemma nrut_sub_implies_ut_sub {o} :
  forall (sub : @Sub o) l,
    nrut_sub l sub -> ut_sub sub.
Proof.
  introv nrut; unfold nrut_sub in nrut; sp.
Qed.
Hint Resolve nrut_sub_implies_ut_sub : slow.

Lemma utok_ren_cond_app_iff {o} :
  forall (atoms1 atoms2 : list (get_patom_set o)) (ren : utok_ren),
    utok_ren_cond (atoms1 ++ atoms2) ren
    <=> (utok_ren_cond atoms1 ren # utok_ren_cond atoms2 ren).
Proof.
  introv; split; intro k; try (apply utok_ren_cond_app; tcsp).
  dands; introv i j; pose proof (k a) as h; allrw in_app_iff; tcsp.
Qed.

Lemma false_if_utok_ren_cond_on_eq_ren_atoms {o} :
  forall ren (a b : @get_patom_set o) atoms1 atoms2,
    no_repeats (range_utok_ren ren)
    -> utok_ren_cond atoms1 ren
    -> utok_ren_cond atoms2 ren
    -> disjoint atoms1 atoms2
    -> LIn a atoms1
    -> LIn b atoms2
    -> ren_atom ren a = ren_atom ren b
    -> False.
Proof.
  introv nrr cond1 cond2 disj ia ib e.
  destruct (get_patom_deq o a b) as [x|x]; subst; tcsp.
  { apply disj in ib; sp. }

  pose proof (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)) as [d1|d1];
    pose proof (in_deq _ (get_patom_deq o) b (dom_utok_ren ren)) as [d2|d2].

  + apply ren_atom_eq1 in e; sp.

  + rw (ren_atom_not_in ren b) in e; auto.

    pose proof (in_deq _ (get_patom_deq o) b (range_utok_ren ren)) as [r|r].

    * pose proof (cond2 b) as h; allsimpl; repeat (autodimp h hyp).

    * pose proof (in_dom_in_range ren a d1) as h.
      rw e in h; sp.

  + rw (ren_atom_not_in ren a) in e; auto.

    pose proof (in_deq _ (get_patom_deq o) a (range_utok_ren ren)) as [r|r].

    * pose proof (cond1 a) as h; allsimpl; repeat (autodimp h hyp).

    * pose proof (in_dom_in_range ren b d2) as h.
      rw <- e in h; sp.

  + rw (ren_atom_not_in ren a) in e; auto.
    rw (ren_atom_not_in ren b) in e; auto.
Qed.

Lemma no_repeats_get_utokens_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (get_utokens t)
    -> utok_ren_cond (get_utokens t) ren
    -> no_repeats (get_utokens (ren_utokens ren t)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv nrr nrt cond; allsimpl; auto.
  Case "oterm".
  allrw no_repeats_app; repnd; dands; eauto 3 with slow.

  - destruct op; tcsp.
    destruct c; allsimpl; tcsp.

  - rw flat_map_map; unfold compose.

    induction bs; allsimpl; tcsp.
    allrw disjoint_app_r; repnd.
    allrw no_repeats_app; repnd.
    repeat (autodimp IHbs hyp).
    { introv i nr1 nr2; eapply ind; eauto. }
    { allrw @utok_ren_cond_app_iff; tcsp. }
    dands; eauto 3 with slow.

    + destruct a as [l t]; allsimpl.
      eapply ind; eauto.
      allrw @utok_ren_cond_app_iff; tcsp.

    + destruct a as [l1 t1]; allsimpl.
      allrw disjoint_flat_map_r.
      introv i; destruct x as [l2 t2]; allsimpl.
      applydup nrt1 in i; allsimpl.
      allrw @get_utokens_ren_utokens.
      apply disjoint_map_l; introv a b; allrw in_map_iff; exrepnd.

      allrw @utok_ren_cond_app_iff; repnd.
      pose proof (false_if_utok_ren_cond_on_eq_ren_atoms
                    ren x a0 (get_utokens t1) (get_utokens t2)) as h.
      repeat (autodimp h hyp).
      introv p q; apply cond; auto.
      rw lin_flat_map; eexists; dands; eauto.

  - destruct op; try (complete (allsimpl; tcsp)).
    destruct c; allsimpl; tcsp.
    allrw disjoint_singleton_l.
    intro i.
    allrw flat_map_map; allunfold @compose.
    allrw lin_flat_map; exrepnd.
    destruct x as [l t]; allsimpl.
    allrw @get_utokens_ren_utokens; allrw in_map_iff; exrepnd.

    rw cons_as_app in cond.
    allrw @utok_ren_cond_app_iff; repnd.

    pose proof (false_if_utok_ren_cond_on_eq_ren_atoms
                  ren g a [g] (get_utokens t)) as h.
    repeat (autodimp h hyp); allsimpl; tcsp.

    + introv p q; apply cond; auto.
      rw lin_flat_map; eexists; dands; eauto.

    + apply disjoint_singleton_l; intro i.
      destruct nrt; eexists; dands; eauto; simpl; auto.
Qed.

Lemma get_utokens_sub_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren,
    get_utokens_sub (ren_utokens_sub ren sub)
    = map (ren_atom ren) (get_utokens_sub sub).
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a as [v t]; allsimpl.
  allrw @get_utokens_sub_cons; allrw map_app.
  rw IHsub.
  rw @get_utokens_ren_utokens; auto.
Qed.

Lemma no_repeats_get_utokens_sub_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (get_utokens_sub sub)
    -> utok_ren_cond (get_utokens_sub sub) ren
    -> no_repeats (get_utokens_sub (ren_utokens_sub ren sub)).
Proof.
  induction sub; introv nrr nrs cond; allsimpl;
  allrw @get_utokens_sub_nil; auto.
  destruct a as [v t]; allrw @get_utokens_sub_cons.
  allrw @utok_ren_cond_app_iff; repnd.
  allrw no_repeats_app; dands; repnd; eauto 3 with slow.
  - apply no_repeats_get_utokens_ren_utokens; auto.
  - allrw @get_utokens_ren_utokens.
    allrw @get_utokens_sub_ren_utokens_sub.
    clear IHsub.
    remember (get_utokens t) as atoms1; clear Heqatoms1.
    remember (get_utokens_sub sub) as atoms2; clear Heqatoms2.
    introv i j.
    allrw in_map_iff; exrepnd; subst.
    pose proof (false_if_utok_ren_cond_on_eq_ren_atoms
                  ren a0 a atoms2 atoms1) as h.
    repeat (autodimp h hyp); eauto with slow.
Qed.
Hint Resolve no_repeats_get_utokens_sub_ren_utokens_sub : slow.

Lemma nrut_sub_implies_no_repeats {o} :
  forall (sub : @Sub o) l,
    nrut_sub l sub
    -> no_repeats (get_utokens_sub sub).
Proof.
  introv nr; unfold nrut_sub in nr; sp.
Qed.
Hint Resolve nrut_sub_implies_no_repeats : slow.

Lemma change_nr_ut_sub_in_lsubst_aux_approx_star {o} :
  forall lib (t1 t2 : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> no_repeats (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t1))
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t2))
    -> approx_star lib t1 t2
    -> approx_star lib (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv norep1 norep2 disj1 disj2 apr.

  - Case "vterm".
    allsimpl.
    constructor.
    inversion apr as [? ? ? apo|?|]; subst; clear apr.

    pose proof (approx_open_change_utoks lib (vterm v1) t2 ren) as h.
    repeat (autodimp h hyp).

  - Case "sterm".
    allsimpl.
    inversion apr as [|? ? ? ? imp aop|]; subst; clear apr.
    econstructor; eauto.
    apply (approx_open_change_utoks _ _ _ ren) in aop; auto.

  - Case "oterm".
    inversion apr as [|?|? ? ? ? ? len lift apo]; subst.

    pose proof (ex_ren_utokens2
                  (oterm op1 lbt1')
                  ren
                  (get_utokens (oterm op1 bs1) ++ get_utokens t2))
      as extra_ren; exrepnd.
    allsimpl; allrw disjoint_app_r; repnd.

    pose proof (approx_open_change_utoks lib (oterm op1 lbt1') t2 (ren ++ ren')) as h.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw disjoint_app_l; allrw disjoint_app_r.
    repeat (autodimp h hyp); dands; eauto 3 with slow.

    { introv i j; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
      pose proof (extra_ren0 t) as h; allrw in_app_iff; repeat (autodimp h hyp). }

    { introv i j; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
      applydup extra_ren12 in i.
      applydup extra_ren7 in i.
      repndors; tcsp. }

    { introv i j; apply disj2 in i; allrw in_diff; allrw in_app_iff; allrw not_over_or; tcsp. }

    { introv i j; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
      apply extra_ren8 in i; sp. }

    allsimpl.
    rw (ren_utokens_app_weak_l t2) in h;
      [|introv i j; applydup extra_ren3 in i;
        applydup disj2 in i0; allrw in_diff; tcsp].
    rw (ren_utokens_o_app_weak_l op1) in h;
      [|introv i j; applydup extra_ren3 in i;
        applydup disj1 in i0; allrw in_diff;
        allrw in_app_iff; tcsp].

    apply (apso _ _ _ _ (ren_utokens_bs (ren ++ ren') lbt1'));
    allrw map_length; allrw @length_ren_utokens_bs; auto.

    allunfold @lblift_sub;
    allrw map_length; allrw @length_ren_utokens_bs;
    repnd; dands; auto.

    introv i.
    applydup lift in i; clear lift.
    allunfold @blift_sub; exrepnd.
    exists lv (ren_utokens ren nt1) (ren_utokens (ren ++ ren') nt2).
    dands; auto;
    [|rw @selectbt_map; auto;
      apply (alpha_eq_bterm_ren_utokens_b _ _ ren) in i2;
      allsimpl; auto
     |unfold ren_utokens_bs; rw @selectbt_map; auto; try omega;
      apply (alpha_eq_bterm_ren_utokens_b _ _ (ren ++ ren')) in i1;
      allsimpl; auto].

    pose proof (selectbt_in n bs1) as in1; autodimp in1 hyp.
    pose proof (selectbt_in n lbt1') as in2; autodimp in2 hyp; try omega.
    remember (selectbt bs1 n) as b1.
    remember (selectbt lbt1' n) as b2.
    destruct b1 as [l1 u1]; destruct b2 as [l2 u2].
    applydup @alpha_eq_bterm_preserves_osize in i2 as sz1.
    applydup @alpha_eq_bterm_preserves_osize in i1 as sz2.

    assert (subset (get_utokens nt1) (get_utokens_bs bs1)) as ss1.
    { introv a; unfold get_utokens_bs.
      rw lin_flat_map; eexists; dands; eauto; simpl.
      apply alpha_eq_bterm_preserves_utokens in i2; allsimpl; rw i2; auto. }

    assert (subset (get_utokens nt2) (get_utokens_bs lbt1')) as ss2.
    { introv a; unfold get_utokens_bs.
      rw lin_flat_map; eexists; dands; eauto; simpl.
      apply alpha_eq_bterm_preserves_utokens in i1; allsimpl; rw i1; auto. }

    repndors;exrepnd;[left|right].

    + dands; auto;[intro e; apply ren_utok_op_diff_fresh in e; auto|].
      pose proof (ind1 u1 nt1 l1) as q; clear ind1.
      rw sz1 in q.
      repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (q nt2 (ren ++ ren')) as aprs; clear q.
      allrw @range_utok_ren_app.
      allrw @dom_utok_ren_app.
      allrw no_repeats_app.
      allrw disjoint_app_l; allrw disjoint_app_r.
      repeat (autodimp aprs hyp); dands; eauto 3 with slow.

      { introv a b; apply disj1 in a; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd; tcsp. }

      { introv a b; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
        apply extra_ren10 in a; sp. }

      { introv a b; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
        pose proof (extra_ren0 t) as q; allrw in_app_iff; repeat (autodimp q hyp). }

      { introv a b; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
        applydup extra_ren7 in a; tcsp. }

      rw (ren_utokens_app_weak_l nt1) in aprs; auto.

      introv a b.
      applydup extra_ren3 in a.
      applydup extra_ren2 in a.
      applydup disj1 in a0; allrw in_diff; destruct a2; dands; tcsp.
      rw in_app_iff; right; rw lin_flat_map; eexists; dands; eauto; simpl.
      apply alpha_eq_bterm_preserves_utokens in i2; allsimpl; rw i2; auto.

    + pose proof (ex_ren_utokens_sub2
                    sub
                    (ren ++ ren')
                    (get_utokens nt1
                                 ++ get_utokens nt2
                                 ++ get_utokens (lsubst nt1 sub)
                                 ++ get_utokens (lsubst nt2 sub)))
        as extra_ren'; exrepnd.
      allsimpl; allrw disjoint_app_r; repnd.

      pose proof (ind1 u1 (lsubst nt1 sub) l1) as ih; clear ind1.
      rw sz1 in ih; repeat (autodimp ih hyp).
      { rw @simple_osize_lsubst; eauto with slow. }
      pose proof (ih (lsubst nt2 sub) ((ren ++ ren') ++ ren'0)) as q; clear ih.

      allrw @range_utok_ren_app.
      allrw @dom_utok_ren_app.
      allrw no_repeats_app.
      allrw disjoint_app_l; allrw disjoint_app_r.
      repnd; repeat (autodimp q hyp); dands; eauto 3 with slow.

      { introv a b; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
        apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
        - applydup ss1 in b0.
          applydup disj1 in a.
          allrw in_diff; allrw in_app_iff; allrw not_over_or; sp.
        - apply in_get_utokens_sub in b0; exrepnd.
          apply in_sub_keep_first in b3; repnd.
          apply sub_find_some in b4.
          pose proof (extra_ren'0 t) as r.
          allrw @range_utok_ren_app; allrw @dom_utok_ren_app.
          allrw in_app_iff.
          repeat (autodimp r hyp); tcsp.
          apply in_get_utokens_sub.
          eexists; eexists; dands; eauto.
      }

      { introv a b; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
        apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
        - applydup ss1 in b0; tcsp.
          apply extra_ren10 in a; tcsp.
        - apply in_get_utokens_sub in b0; exrepnd.
          apply in_sub_keep_first in b3; repnd.
          apply sub_find_some in b4.
          pose proof (extra_ren'0 t) as r.
          allrw @range_utok_ren_app; allrw @dom_utok_ren_app.
          allrw in_app_iff.
          repeat (autodimp r hyp); tcsp.
          apply in_get_utokens_sub.
          eexists; eexists; dands; eauto.
      }

      { introv a b; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
        apply extra_ren'12 in a; sp.
      }

      { introv a b; allrw in_diff; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
        apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
        - applydup ss2 in b0.
          pose proof (extra_ren0 t) as q; allrw in_app_iff.
          repeat (autodimp q hyp); tcsp.
        - apply in_get_utokens_sub in b0; exrepnd.
          apply in_sub_keep_first in b3; repnd.
          apply sub_find_some in b4.
          pose proof (extra_ren'0 t) as r.
          allrw @range_utok_ren_app; allrw @dom_utok_ren_app.
          allrw in_app_iff.
          repeat (autodimp r hyp); tcsp.
          apply in_get_utokens_sub.
          eexists; eexists; dands; eauto.
      }

      { introv a b; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
        apply get_utokens_lsubst in b0; allrw in_app_iff; repndors; tcsp.
        - applydup ss2 in b0.
          apply extra_ren7 in a; tcsp.
        - apply in_get_utokens_sub in b0; exrepnd.
          apply in_sub_keep_first in b3; repnd.
          apply sub_find_some in b4.
          pose proof (extra_ren'0 t) as r.
          allrw @range_utok_ren_app; allrw @dom_utok_ren_app.
          allrw in_app_iff.
          repeat (autodimp r hyp); tcsp.
          apply in_get_utokens_sub.
          eexists; eexists; dands; eauto.
      }

      { introv a b; allrw in_diff; allrw in_app_iff; allrw not_over_or; repnd.
        apply extra_ren'8 in a; sp.
      }

      repeat (rw @lsubst_ren_utokens in q).

      assert (disjoint (dom_utok_ren ren'0) (get_utokens nt1)) as disj'0nt1.
      { introv a b.
        applydup extra_ren'3 in a.
        applydup extra_ren'2 in a.
        allrw in_app_iff.
        repndors; tcsp.
        - applydup extra_ren'13 in a.
          applydup disj1 in a0; allrw in_diff; allrw in_app_iff; allrw not_over_or.
          destruct a3; dands; tcsp.
        - apply extra_ren10 in a0; tcsp.
      }

      pose proof (ren_utokens_app_weak_l nt1 (ren ++ ren') ren'0 disj'0nt1) as e1.
      rw e1 in q.

      assert (disjoint (dom_utok_ren ren') (get_utokens nt1)) as disj'nt1.
      { introv a b.
        applydup extra_ren3 in a.
        applydup extra_ren2 in a.
        applydup disj1 in a0; allrw in_diff; destruct a2; dands; tcsp.
        rw in_app_iff; right; rw lin_flat_map; eexists; dands; eauto; simpl.
        apply alpha_eq_bterm_preserves_utokens in i2; allsimpl; rw i2; auto.
      }

      pose proof (ren_utokens_app_weak_l nt1 ren ren' disj'nt1) as e2.
      rw e2 in q.

      assert (disjoint (dom_utok_ren ren'0) (get_utokens nt2)) as disj'0nt2.
      { introv a b.
        applydup extra_ren'3 in a.
        applydup extra_ren'2 in a.
        allrw in_app_iff.
        repndors; tcsp.
        - applydup extra_ren'13 in a.
          pose proof (extra_ren0 t) as r; allrw in_app_iff.
          repeat (autodimp r hyp); tcsp.
        - apply extra_ren7 in a0; tcsp.
      }

      pose proof (ren_utokens_app_weak_l nt2 (ren ++ ren') ren'0 disj'0nt2) as e3.
      rw e3 in q.

      exists (ren_utokens_sub ((ren ++ ren') ++ ren'0) sub).
      rw @ren_utok_op_diff_fresh.
      rw @dom_sub_ren_utokens_sub.
      dands; auto.

      assert (no_repeats (range_utok_ren ((ren ++ ren') ++ ren'0))) as norep_ren.
      { repeat (rw @range_utok_ren_app).
        repeat (rw no_repeats_app).
        rw disjoint_app_l; dands; eauto with slow. }

      assert (utok_ren_cond (get_utokens_sub sub) ((ren ++ ren') ++ ren'0)) as cond1.
      { introv x y.
        pose proof (extra_ren'0 a) as r.
        allrw @dom_utok_ren_app; allrw @range_utok_ren_app.
        allrw in_app_iff; allrw not_over_or.
        repndors.
        - destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)); tcsp.
          destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren')); tcsp.
        - destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)); tcsp.
          destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren')); tcsp.
        - apply extra_ren'7 in y; sp. }

      assert (utok_ren_cond (get_utokens nt1) ren) as cond2.
      { introv x y.
        applydup ss1 in x.
        applydup disj1 in y.
        rw in_diff in y0; rw in_app_iff in y0.
        destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)); tcsp.
        destruct y0; dands; tcsp.
      }

      assert (utok_ren_cond (get_utokens nt2) (ren ++ ren')) as cond3.
      { introv x y.
        applydup ss2 in x.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        pose proof (extra_ren0 a) as r.
        allrw in_app_iff.
        destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)); tcsp.
        repndors; tcsp.
        clear r.
        apply extra_ren7 in y; sp.
      }

      unfold nrut_sub; dands; eauto 3 with slow.

      rw <- e3; rw <- e2; rw <- e1.
      repeat (rw @get_utokens_ren_utokens).
      rw @get_utokens_sub_ren_utokens_sub.
      rw <- map_app.
      apply disjoint_map_l; introv u v.
      rw in_map_iff in v; exrepnd.

      pose proof (false_if_utok_ren_cond_on_eq_ren_atoms
                    ((ren ++ ren') ++ ren'0)
                    x a
                    (get_utokens nt1 ++ get_utokens nt2)
                    (get_utokens_sub sub)) as hh.
      allunfold @nrut_sub; repnd.
      repeat (autodimp hh hyp); tcsp.

      clear u.
      apply utok_ren_cond_app.

      { introv z w.
        applydup cond2 in z.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw in_app_iff.
        repndors; tcsp.
        - apply extra_ren10 in w.
          apply ss1 in z; sp.
        - apply extra_ren'10 in w; sp.
      }

      { introv z w.
        applydup cond3 in z.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw in_app_iff.
        repndors; tcsp.
        apply extra_ren'11 in w; sp.
      }
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../terms/" "../computation/" "../util/")
*** End:
*)
