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


Require Export approx_star_def.


(* begin hide *)

Lemma exists_nr_ut_sub {o} :
  forall lib lv (t : @NTerm o),
    {sub : Sub
     & nr_ut_sub lib t sub
     # lv = dom_sub sub }.
Proof.
  induction lv as [|v lv]; introv.
  - exists ([] : @Sub o); simpl; auto.
  - destruct (fresh_atom o (get_utokens_lib lib t)) as [a h].
    pose proof (IHlv (subst t v (mk_utoken a))) as k; exrepnd; subst; clear IHlv.
    exists ((v,mk_utoken a) :: sub); simpl; dands; auto.
Qed.

Lemma select2bts {o} :
  forall (bs1 bs2 : list (@BTerm o)) n,
    n < length bs1
    -> length bs1 = length bs2
    -> {b1 : BTerm
        & {b2 : BTerm
        & selectbt bs1 n = b1
        # selectbt bs2 n = b2
        # LIn (b1,b2) (combine bs1 bs2)}}.
Proof.
  introv len1 len2.
  exists (selectbt bs1 n) (selectbt bs2 n); dands; auto.
  unfold selectbt.
  revert dependent n.
  revert dependent bs2.
  induction bs1; destruct bs2; introv len1 len2; allsimpl; tcsp; cpx.
  destruct n; tcsp; cpx.
Qed.

Lemma cl_disjoint_free_vars_lsubst_aux_dom {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> disjoint (free_vars (lsubst_aux t sub)) (dom_sub sub).
Proof.
  introv cl i j.
  rw @free_vars_lsubst_aux_cl in i; auto.
  allrw in_remove_nvars; sp.
Qed.
Hint Resolve cl_disjoint_free_vars_lsubst_aux_dom : slow.

Lemma sub_find_some_eq_doms_nrut_sub {o} :
  forall (sub1 sub2 : @Sub o) v l,
    nrut_sub l sub2
    -> dom_sub sub1 = dom_sub sub2
    -> match sub_find sub1 v with
         | Some _ => {a : get_patom_set o & sub_find sub2 v = Some (mk_utoken a)}
         | None => sub_find sub2 v = None
       end.
Proof.
  induction sub1; destruct sub2; introv nr eqdoms; allsimpl; tcsp.
  destruct a, p; allsimpl; cpx.
  allrw @nrut_sub_cons; exrepnd; subst.
  boolvar; allsimpl; tcsp.
  - eexists; dands; eauto.
  - pose proof (IHsub1 sub2 v l) as h; sp.
Qed.

Definition ax_sub {o} (vs : list NVar) : @Sub o :=
  map (fun v : NVar => (v, mk_axiom)) vs.

Definition ax_sub_fv {o} (t : @NTerm o) : @Sub o :=
  ax_sub (free_vars t).

Lemma wf_sub_ax_sub {o} :
  forall vs, @wf_sub o (ax_sub vs).
Proof.
  introv.
  unfold wf_sub, sub_range_sat, ax_sub; introv i.
  rw in_map_iff in i; exrepnd; cpx; eauto with slow.
Qed.
Hint Resolve wf_sub_ax_sub : slow.

Lemma wf_sub_ax_sub_fv {o} :
  forall (t : @NTerm o), wf_sub (ax_sub_fv t).
Proof.
  introv.
  unfold ax_sub_fv; eauto with slow.
Qed.
Hint Resolve wf_sub_ax_sub_fv : slow.

Lemma prog_sub_ax_sub {o} :
  forall vs, @prog_sub o (ax_sub vs).
Proof.
  introv.
  unfold prog_sub, sub_range_sat, ax_sub.
  introv i.
  rw in_map_iff in i; exrepnd; cpx.
Qed.
Hint Resolve prog_sub_ax_sub : slow.

Lemma prog_sub_ax_sub_fv {o} :
  forall (t : @NTerm o), prog_sub (ax_sub_fv t).
Proof.
  introv.
  unfold ax_sub_fv; eauto with slow.
Qed.
Hint Resolve prog_sub_ax_sub_fv : slow.

Lemma cl_sub_ax_sub {o} :
  forall vs, @cl_sub o (ax_sub vs).
Proof.
  introv.
  unfold prog_sub, sub_range_sat, ax_sub.
  introv i.
  rw in_map_iff in i; exrepnd; cpx.
Qed.
Hint Resolve cl_sub_ax_sub : slow.

Lemma cl_sub_ax_sub_fv {o} :
  forall (t : @NTerm o), cl_sub (ax_sub_fv t).
Proof.
  introv.
  unfold ax_sub_fv; eauto with slow.
Qed.
Hint Resolve cl_sub_ax_sub_fv : slow.

Lemma isprogram_lsubst_if_isprog_sub {o} :
  forall (t : @NTerm o) (sub : Substitution),
    nt_wf t
    -> prog_sub sub
    -> subset (free_vars t) (dom_sub sub)
    -> isprogram (lsubst t sub).
Proof.
  introv wf ps ss.
  apply isprogram_lsubst; auto.
Qed.

Lemma dom_sub_ax_sub {o} :
  forall vs, @dom_sub o (ax_sub vs) = vs.
Proof.
  introv.
  unfold ax_sub.
  unfold dom_sub.
  unfold dom_lmap.
  rw map_map; unfold compose; simpl.
  apply map_id.
Qed.

Lemma dom_sub_ax_sub_fv {o} :
  forall (t : @NTerm o), dom_sub (ax_sub_fv t) = free_vars t.
Proof.
  introv.
  unfold ax_sub_fv.
  apply dom_sub_ax_sub.
Qed.

Lemma implies_wf_lsubst_aux {o} :
  forall (sub : @Sub o) t,
    wf_sub sub
    -> nt_wf t
    -> nt_wf (lsubst_aux t sub).
Proof.
  introv ws wt.
  apply lsubst_aux_wf_iff; auto.
Qed.
Hint Resolve implies_wf_lsubst_aux : slow.

Lemma cl_lsubst_swap_sub_filter {o} :
  forall (t : @NTerm o) (s1 s2 : Substitution),
    cl_sub s1
    -> cl_sub s2
    -> lsubst (lsubst t s1) s2
       = lsubst (lsubst t (sub_filter s2 (dom_sub s1))) s1.
Proof.
  introv cl1 cl2.
  repeat unflsubst.
  revert s1 s2 cl1 cl2.

  nterm_ind t as [v|op bs ind] Case; introv cl1 cl2; simpl; auto.

  - Case "vterm".
    rw @sub_find_sub_filter_eq.
    boolvar; simpl; auto.

    + remember (sub_find s1 v) as sf; symmetry in Heqsf; destruct sf; simpl.

      * rw @lsubst_aux_trivial_cl2; auto.
        rw @cl_sub_eq2 in cl1.
        apply sub_find_some in Heqsf.
        apply cl1 in Heqsf; auto.

      * apply sub_find_none2 in Heqsf; sp.

    + apply sub_find_none_iff in Heqb; allrw; simpl.
      remember (sub_find s2 v) as sf; symmetry in Heqsf; destruct sf; simpl.

      * rw @lsubst_aux_trivial_cl2; auto.
        rw @cl_sub_eq2 in cl2.
        apply sub_find_some in Heqsf.
        apply cl2 in Heqsf; auto.

      * allrw; auto.

  - Case "oterm".
    allrw map_map; allunfold @compose.
    f_equal.
    apply eq_maps; introv i; destruct x as [l t]; simpl.
    f_equal.
    rw (ind t l); eauto with slow.
    f_equal; fequal.
    rw <- @dom_sub_sub_filter.
    allrw <- @sub_filter_app_r.
    rw <- @sub_filter_app_as_remove_nvars.
    apply sub_filter_eqvars; rw eqvars_prop; introv; allrw in_app_iff; split; sp.
Qed.

Lemma approx_utoken_implies_reduces_to {o} :
  forall lib a (t : @NTerm o),
    approx lib (mk_utoken a) t
    -> reduces_to lib t (mk_utoken a).
Proof.
  introv ap.
  destruct ap as [c].
  unfold close_comput in c; repnd.
  pose proof (c2 (NUTok a) []) as h; fold_terms.
  autodimp h hyp.
  { apply computes_to_value_isvalue_refl; eauto with slow. }
  exrepnd.
  unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
  unfold computes_to_value in h1; repnd; auto.
Qed.

Lemma implies_prog_sub_app {o} :
  forall (sub1 sub2 : @Sub o),
    prog_sub sub1
    -> prog_sub sub2
    -> prog_sub (sub1 ++ sub2).
Proof.
  introv ps1 ps2.
  allrw <- @prog_sub_eq.
  introv i.
  allrw @range_app; allrw in_app_iff; repndors; tcsp.
Qed.
Hint Resolve implies_prog_sub_app : slow.

Lemma nr_ut_sub_approx_star_aux {o} :
  forall lib (t1 t2 : @NTerm o) sub,
    nr_ut_sub lib (mk_pair t1 t2) sub
    -> approx_star lib t1 t2
    -> approx_star lib (lsubst_aux t1 sub) (lsubst_aux t2 sub).
Proof.
  nterm_ind1s t1 as [v|op bs ind] Case; introv ut ap; auto.

  - Case "vterm".
    simpl.
    inversion ap as [? ? ? apo|]; subst; clear ap.
    pose proof (approx_open_lsubst_congr lib (vterm v) t2 sub) as h.
    repeat (autodimp h hyp); eauto with slow.
    repeat (unflsubst in h); allsimpl.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf.

    + apply sub_find_some in Heqsf.
      eapply in_nr_ut_sub in Heqsf; eauto; exrepnd; subst.
      apply (apso _ _ _ _ []); simpl; eauto with slow.
      unfold lblift_sub; simpl; tcsp.

    + constructor; auto.

  - Case "oterm".
    simpl.
    inversion ap as [|? ? ? ? ? len lbls apo]; subst.
    apply (apso _ _ _ _ (map (fun t : BTerm => lsubst_bterm_aux t sub) lbt1')).

    + allrw map_length; auto.

    + unfold lblift_sub; allrw map_length; dands; auto.
      introv i.
      unfold lblift_sub in lbls; repnd; GC.
      pose proof (lbls n) as h; autodimp h hyp; clear lbls.
      unfold blift_sub in h; exrepnd.
      unfold blift_sub.

      repeat (rw @selectbt_map; auto; try omega).
      pose proof (select2bts bs lbt1' n) as k; repeat (autodimp k hyp); exrepnd.
      allrw k0; allrw k2; clear k0 k2.

      exists lv (lsubst_aux nt1 (sub_filter sub lv)) (lsubst_aux nt2 (sub_filter sub lv)).
      dands.

      * repndors; exrepnd; subst.

(*
        { right.
        }

        { left.
          exists sub0; dands; auto.

          - repeat unflsubst.

            rw (cl_lsubst_aux_swap nt1); eauto 3 with slow;
            [|rw <- @dom_sub_sub_filter; eauto with slow].
            rw @cl_lsubst_aux_swap_filter; eauto 3 with slow.

            rw (cl_lsubst_aux_swap nt2); eauto 3 with slow;
            [|rw <- @dom_sub_sub_filter; eauto with slow].
            rw @cl_lsubst_aux_swap_filter; eauto 3 with slow.

            destruct b1 as [l1 u1].
            destruct b2 as [l2 u2].
            applydup in_combine in k1; repnd.

            repeat (unflsubst in h4).

            apply (ind u1 _ l1); auto.
            rw @simple_size_lsubst_aux; eauto with slow.
            apply alpha_eq_bterm_preserves_size in h2; rw h2; auto.
          -
        }
*)

Abort.

Lemma exists_nrut_sub {o} :
  forall lv l,
    {sub : @Sub o
     & nrut_sub l sub
     # lv = dom_sub sub }.
Proof.
  induction lv as [|v lv]; introv.
  - exists ([] : @Sub o); simpl; dands; eauto with slow.
  - pose proof (IHlv l) as k; exrepnd; subst; clear IHlv.
    destruct (fresh_atom o (l ++ get_utokens_sub sub)) as [a h].
    allrw in_app_iff; allrw not_over_or; repnd.
    exists ((v,mk_utoken a) :: sub); simpl; dands; auto.
    apply nrut_sub_cons; eexists; dands; eauto.
Qed.

Lemma nrut_sub_subset {o} :
  forall (sub : @Sub o) l1 l2,
    subset l2 l1
    -> nrut_sub l1 sub
    -> nrut_sub l2 sub.
Proof.
  introv ss nrut.
  allunfold @nrut_sub; repnd; dands; auto.
  introv i j.
  apply ss in i; apply nrut in i; sp.
Qed.

Lemma simple_osize_lsubst {o} :
  forall (t : @NTerm o) sub,
    oshallow_sub sub
    -> osize (lsubst t sub) = osize t.
Proof.
  introv sh.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  rw @simple_osize_lsubst_aux; eauto 3 with slow.
  apply alpha_eq_preserves_osize; eauto with slow.
Qed.

Lemma nrut_sub_implies_oshallow_sub {o} :
  forall (sub : @Sub o) atoms,
    nrut_sub atoms sub
    -> oshallow_sub sub.
Proof.
  introv nrut i.
  apply in_range_iff in i; exrepnd.
  eapply in_nrut_sub in nrut; eauto.
  exrepnd; subst; allsimpl; auto.
Qed.
Hint Resolve nrut_sub_implies_oshallow_sub : slow.

(* end hide *)

Lemma approx_star_refl {p} : forall lib t, @nt_wf p t -> approx_star lib t t.
Proof.
  nterm_ind1s t as [?|o lbt Hind] Case; introv Hwf; eauto 3 with slow.

  - Case "oterm".

    apply apso with (lbt1':=lbt); eauto with slow.

    unfold lblift_sub. split;auto;[].
    introv Hlt.
    pose proof (selectbt_in2 n lbt Hlt) as Hbt. exrepnd. destruct bt as [lv nt].
    rw Hbt0.
    exrepnd.
    unfold blift_sub.
    exists (lv) (nt) (nt); spc; eauto.
    assert (nt_wf nt) as w by (eapply nt_wf_ot_implies in Hwf; eauto).
    applydup (Hind nt nt lv) in Hbt1 as ap; eauto 3 with slow.
    destruct (dec_op_eq_fresh o) as [e|e]; subst.

    + right.
      pose proof (exists_nrut_sub lv (get_utokens_lib lib nt)) as h; exrepnd; subst.
      exists sub; dands; auto.

      * pose proof (Hind nt (lsubst nt sub) (dom_sub sub)) as h.
        repeat (autodimp h hyp); eauto 3 with slow.
        rw @simple_osize_lsubst; eauto with slow.

      * eapply nrut_sub_subset;[|exact h1].
        introv i; allrw in_app_iff; sp.

    + left.
      invertsn Hwf. apply Hwf in Hbt1.
      inverts Hbt1; tcsp.
Qed.
Hint Resolve approx_star_refl : slow.

(* begin hide *)

Lemma approx_starbt_refl {p} :
  forall lib op bt, @bt_wf p bt -> approx_star_bterm lib op bt bt.
Proof.
  introv hbt.
  destruct bt as [lv nt]. simpl. invertsn hbt.
  exrepnd. exists (lv) (nt) (nt); spc.
  destruct (dec_op_eq_fresh op) as [e|e]; subst; eauto with slow.
  pose proof (exists_nrut_sub lv (get_utokens_lib lib nt)) as h; exrepnd; subst.
  right; exists sub; dands; eauto 4 with slow.
  eapply nrut_sub_subset;[|exact h1].
  introv i; allrw in_app_iff; sp.
Qed.
Hint Resolve approx_starbt_refl : slow.

Lemma approx_open_implies_approx_star {p} :
  forall lib (t1 t2 : @NTerm p),
    approx_open lib t1 t2
    -> approx_star lib t1 t2.
Proof.
  nterm_ind t1 as [v|op bs ind] Case; eauto 3 with slow.

  - Case "oterm".
    introv Hap.
    apply apso with (lbt1':=bs); auto.
    unfold lblift.
    split; auto.

    intros. apply approx_starbt_refl.
    unfold approx_open in Hap.
    repnud Hap.
    invertsn Hap0.
    apply Hap0. apply selectbt_in; auto.
Qed.
Hint Resolve approx_open_implies_approx_star : slow.

Definition get_defs_entry {o} (entry : @library_entry o) : list marker :=
  match entry with
  | lib_cs name vals => []
  | lib_abs opabs vars rhs correct => [opabs_name opabs]
  end.

Definition get_defs_lib {o} (lib : @pre_library o) : list marker :=
  flat_map get_defs_entry lib.

Lemma find_entry_abs_marker_none_if_not_in {o} :
  forall (lib : @pre_library o) m bs,
    !LIn m (get_defs_lib lib)
    -> find_entry lib (abs_marker m) bs = None.
Proof.
  induction lib; introv ni; simpl; auto.
  destruct a; allsimpl; allrw not_over_or; repnd.
  rw IHlib; auto.
  boolvar; auto.
  provefalse.
  unfold matching_entry in m0; allsimpl; tcsp.
Qed.

(*
Lemma exists_is_mrk {o} :
  forall (lib : @library o) t,
    {m : marker & is_mrk lib m # not_marked_lib m t lib}.
Proof.
  introv.
  remember (get_defs_lib lib ++ get_markers t ++ get_markers_lib lib) as ms.
  exists (String.append "x" (append_string_list ms)).

  assert (!LIn (String.append "x" (append_string_list ms)) ms) as ni.
  {
    clear Heqms.
    remember ("x") as extra.
    assert (0 < String.length extra) as len by (subst; simpl; auto).
    clear Heqextra.
    revert dependent extra.
    induction ms; introv s; allsimpl; tcsp.
    rw string_append_assoc.
    rw not_over_or; dands; auto.

    - intro k.
      assert (String.length a
              = String.length
                  (String.append
                     (String.append extra a)
                     (append_string_list ms))) as e.
      { rw <- k; auto. }
      allrw string_length_append.
      omega.

    - apply IHms.
      rw string_length_append; omega.
  }

  remember (String.append "x" (append_string_list ms)) as m; clear Heqm.
  subst.
  unfold is_mrk; simpl.
  allrw in_app_iff; allrw not_over_or; repnd.
  dands.
  - apply find_entry_abs_marker_none_if_not_in; auto.
  - unfold not_marked_lib; rw in_app_iff; sp.
Qed.
*)

(*
Lemma approx_open_vterm {o} :
  forall lib x (t : @NTerm o),
    approx_open lib (vterm x) t
    -> reduces_to lib t (vterm x).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv ap.

  - Case "vterm".
    unfold approx_open, olift in ap; repnd.
    destruct (deq_nvar v x); subst; auto;[apply reduces_to_symm|].
    provefalse.
    pose proof (ap [(v,mk_zero),(x,mk_one)]) as h.
    unfold lsubst in h; simpl in h; boolvar; tcsp.
    repeat (autodimp h hyp).

    + unfold wf_sub, sub_range_sat; simpl; sp; cpx; apply nt_wf_eq; sp.

    + inversion h as [c].
      unfold close_comput in c; repnd.
      pose proof (c2 (Nint (Z_of_nat 1)) []) as k.
      autodimp k hyp.
      * apply computes_to_value_isvalue_refl; auto.
      * exrepnd.
        apply computes_to_value_isvalue_eq in k1;
        try (complete (repeat constructor; allsimpl; sp)).
        ginv.

  - Case "oterm".
    unfold approx_open, olift in ap; repnd.

    pose proof (exists_is_mrk lib (oterm op bs)) as em; exrepnd.

    pose proof (ap ((x,mk_marker m) :: bot_sub_fv (oterm op bs))) as h.
    repeat (autodimp h hyp); clear ap.

    + apply wf_sub_cons; dands; auto.
      apply wf_marker.

    + apply isprogram_lsubst; auto.

      * simpl; introv i; dorn i; cpx.
        { apply isprogram_marker. }
        { apply in_bot_sub_fv in i; repnd; subst; apply isprogram_bot. }

      * simpl; introv i; dorn i; subst; tcsp.

    + apply isprogram_lsubst; auto.

      * simpl; introv i; dorn i; cpx.
        { apply isprogram_marker. }
        { apply in_bot_sub_fv in i; repnd; subst; apply isprogram_bot. }

      * simpl; introv i; rw @dom_sub_bot_sub_fv; simpl; sp.

    + inversion h as [c]; clear h.
      unfold close_comput in c; simpl in c; repnd.
      clear c2 c3.
      pose proof (c m) as h; clear c.

      autodimp h hyp.

      * unfold lsubst; simpl; boolvar.
        apply computes_to_marker_refl; auto.

      * allrw @nt_wf_eq.
        apply computes_to_marker_lsubst_bot_sub in h; auto.
Qed.
*)

Lemma dom_sub_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o),
    dom_sub (lsubst_aux_sub sub1 sub2) = dom_sub sub1.
Proof.
  induction sub1; introv; allsimpl; tcsp.
  destruct a; simpl; rw IHsub1; auto.
Qed.

Lemma lsubst_aux_sub_filter_range2 {o} :
  forall (sub1 sub2 : @Sub o) vs,
    disjoint vs (sub_free_vars sub1)
    -> lsubst_aux_sub sub1 sub2
       = lsubst_aux_sub sub1 (sub_filter sub2 vs).
Proof.
  induction sub1; introv disj; allsimpl; auto.
  destruct a.
  allrw disjoint_app_r; repnd.
  rw <- IHsub1; auto.
  f_equal.
  f_equal.
  rw @lsubst_aux_sub_filter; eauto with slow.
Qed.

Lemma simple_lsubst_aux_lsubst_aux_sub_disj {o} :
  forall (t : @NTerm o) sub1 sub2,
    disjoint (dom_sub sub1) (sub_free_vars sub2)
    -> disjoint (bound_vars t) (sub_free_vars sub2)
    -> disjoint (sub_bound_vars sub1) (sub_free_vars sub2)
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> lsubst_aux (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                  (lsubst_aux_sub sub1 sub2)
       = lsubst_aux (lsubst_aux t sub1) sub2.
Proof.
  nterm_ind t as [x|op bs ind] Case; introv disj1 disj2 disj3 disj4; tcsp.

  - Case "vterm".
    allsimpl.
    destruct (in_deq NVar deq_nvar x (dom_sub sub1)) as [i|i].

    + rw @sub_find_sub_filter; tcsp; simpl; boolvar; auto.
      rw @sub_find_lsubst_aux_sub.
      remember (sub_find sub1 x) as f; symmetry in Heqf; destruct f; simpl; auto.
      apply sub_find_none_iff in Heqf; sp.

    + applydup @sub_find_none_iff in i; rw i0; simpl.
      rw @sub_find_sub_filter_eta; simpl; tcsp.
      remember (sub_find sub2 x) as f; symmetry in Heqf; destruct f;
      simpl; boolvar; tcsp.

      * apply sub_find_some in Heqf.
        apply lsubst_aux_trivial_cl_term.
        rw @dom_sub_lsubst_aux_sub.
        rw @sub_free_vars_is_flat_map_free_vars_range in disj1.
        rw disjoint_flat_map_r in disj1.
        apply disjoint_sym; apply disj1.
        apply in_range_iff; eexists; eauto.

      * rw @sub_find_lsubst_aux_sub; rw i0; simpl; auto.

  - Case "oterm".
    simpl.
    allrw map_map; unfold compose.
    f_equal; apply eq_maps; introv i.

    destruct x; allsimpl.
    allrw disjoint_flat_map_l.
    applydup disj4 in i as j; simpl in j.
    applydup disj2 in i as k; simpl in k.
    allrw disjoint_app_l; repnd.
    f_equal.

    rw @sub_filter_swap.
    rw @sub_filter_lsubst_aux_sub.
    rw (lsubst_aux_sub_filter_range2 (sub_filter sub1 l) sub2 l); auto;
    [| eapply subvars_disjoint_r;[|exact j0];
       apply subvars_sub_free_vars_sub_filter].
    rw @sub_filter_sub_filter_dom_sub.
    eapply ind; eauto.

    + rw <- @dom_sub_sub_filter.
      rw disjoint_remove_nvars_l.
      eapply subvars_disjoint_r;[|exact disj1].
      apply subvars_remove_nvars.
      apply subvars_app_weak_l.
      apply subvars_sub_free_vars_sub_filter.

    + eapply subvars_disjoint_r;[|exact k].
      apply subvars_sub_free_vars_sub_filter.

    + apply (subvars_disjoint_r _ (sub_free_vars sub2));
      [apply subvars_sub_free_vars_sub_filter|].
      apply (subvars_disjoint_l _ (sub_bound_vars sub1));
        [apply subvars_sub_bound_vars_sub_filter|auto].

    + eapply subvars_disjoint_r;[|exact j].
      apply subvars_sub_free_vars_sub_filter.
Qed.

(* This is what's called simpl_olift in approx.v *)
Definition cl_olift {o} (R : NTrel) (x y : @NTerm o) : [univ] :=
  nt_wf x # nt_wf y
  # forall sub: Sub,
      prog_sub sub
      -> isprogram (lsubst x sub)
      -> isprogram (lsubst y sub)
      -> R (lsubst x sub) (lsubst y sub).

Lemma isprogram_lsubst_prog_sub {o} :
  forall (t : @NTerm o) sub,
    nt_wf t
    -> prog_sub sub
    -> subvars (free_vars t) (dom_sub sub)
    -> isprogram (lsubst t sub).
Proof.
  introv wf ps sv.
  rw subvars_prop in sv.
  apply isprogram_lsubst; auto.
Qed.

Lemma in_dom_sub_iff {o} :
  forall v (sub : @Sub o),
    LIn v (dom_sub sub) <=> {t : NTerm & LIn (v,t) sub}.
Proof.
  induction sub; simpl; split; intro k; exrepnd; allsimpl; tcsp.
  - dorn k; subst; tcsp.
    + exists a; sp.
    + apply IHsub in k; exrepnd.
      exists t; sp.
  - dorn k0; cpx; right; apply IHsub; eexists; eauto.
Qed.

Lemma eqvars_dom_sub_sub_keep_first {o} :
  forall (sub : @Sub o) vs,
    subvars vs (dom_sub sub)
    -> eqvars (dom_sub (sub_keep_first sub vs)) vs.
Proof.
  introv sv.
  rw eqvars_prop; introv; split; intro k.
  - apply in_dom_sub_iff in k; exrepnd.
    apply in_sub_keep_first in k0; repnd; auto.
  - rw subvars_prop in sv; applydup sv in k.
    apply in_dom_sub_exists in k0; exrepnd.
    apply in_dom_sub_iff.
    exists t.
    apply in_sub_keep_first; dands; auto.
Qed.

Lemma cl_olift_implies_olift {o} :
  forall R (x y : @NTerm o),
    respects_alpha R
    -> cl_olift R x y
    -> olift R x y.
Proof.
  introv resp clo.
  unfold cl_olift in clo; repnd.
  unfold olift; dands; auto.
  introv wf isp1 isp2.
  pose proof (lsubst_trim2_alpha2 x y sub wf isp1 isp2) as h.
  pose proof (lsubst_trim2_alpha1 x y sub isp1 isp2) as k; simpl in k; repnd.

  pose proof (fst resp
                  (lsubst x (sub_keep_first sub (free_vars x ++ free_vars y)))
                  (lsubst y sub)
                  (lsubst x sub))
    as x1; repeat (autodimp x1 hyp);[apply alpha_eq_sym; auto|].
  pose proof (snd resp
                  (lsubst x (sub_keep_first sub (free_vars x ++ free_vars y)))
                  (lsubst y (sub_keep_first sub (free_vars x ++ free_vars y)))
                  (lsubst y sub))
    as x2 ; repeat (autodimp x2 hyp);[apply alpha_eq_sym; auto|].

  applydup @lsubst_program_implies in isp1.
  applydup @lsubst_program_implies in isp2.

  apply clo; auto.

  - apply isprogram_lsubst_prog_sub; auto.
    pose proof (eqvars_dom_sub_sub_keep_first sub (free_vars x ++ free_vars y)) as e.
    autodimp e hyp;[rw subvars_eq; rw subset_app; sp|].
    apply eqvars_sym in e.
    eapply subvars_eqvars_r;[|exact e].
    apply subvars_app_weak_l; auto.

  - apply isprogram_lsubst_prog_sub; auto.
    pose proof (eqvars_dom_sub_sub_keep_first sub (free_vars x ++ free_vars y)) as e.
    autodimp e hyp;[rw subvars_eq; rw subset_app; sp|].
    apply eqvars_sym in e.
    eapply subvars_eqvars_r;[|exact e].
    apply subvars_app_weak_r; auto.
Qed.

Lemma reduces_to_lsubst_aux {o} :
  forall lib (t u : @NTerm o) sub,
    nt_wf t
    -> prog_sub sub
    -> subvars (free_vars t) (dom_sub sub)
    -> reduces_to lib t u
    -> {v : NTerm
        & reduces_to lib (lsubst_aux t sub) v
        # alpha_eq v (lsubst_aux u sub) }.
Proof.
  introv wf cl sv r.
  unfold reduces_to in r; exrepnd.
  revert dependent u.
  revert dependent t.

  induction k; introv wf sv r.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    exists (lsubst_aux u sub); dands; auto.
    exists 0; rw @reduces_in_atmost_k_steps_0; auto.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    pose proof (compute_step_lsubst_aux lib t u0 sub) as h.
    repeat (autodimp h hyp); exrepnd; eauto 3 with slow.

    applydup @compute_step_preserves in r1; repnd; auto.
    assert (subvars (free_vars u0) (dom_sub sub))
      as sv2 by (eapply subvars_trans; eauto).

    pose proof (IHk u0 r2 sv2 u r0) as j; exrepnd.

    pose proof (reduces_to_alpha lib (lsubst_aux u0 sub) v v0) as x;
      repeat (autodimp x hyp);[|apply alpha_eq_sym;auto|];
      exrepnd;
      eauto 3 with slow.
    exists t2'; dands; auto.

    + eapply reduces_to_trans;[|complete eauto].
      apply reduces_to_if_step; auto.

    + eapply alpha_eq_trans;[|complete eauto].
      apply alpha_eq_sym; auto.
Qed.

(*
Lemma approx_open_vterm_iff_reduces_to {o} :
  forall lib x (t : @NTerm o),
    wf_term t
    -> (approx_open lib (vterm x) t
        <=> reduces_to lib t (vterm x)).
Proof.
  introv wf; split; intro k.
  - apply approx_open_vterm; auto.
  - unfold approx_open.
    apply cl_olift_implies_olift; auto.
    unfold cl_olift.
    dands; auto.
    + apply wf_term_eq; auto.
    + introv cl isp1 isp2.

      applydup @prog_sub_implies_cl_sub in cl.
      applydup @lsubst_program_implies in isp1.
      applydup @lsubst_program_implies in isp2.

      pose proof (reduces_to_lsubst_aux lib t (vterm x) sub) as h;
        repeat (autodimp h hyp);[rw subvars_eq;auto|].
      exrepnd.

      eapply approx_alpha_rw_l_aux;[eauto|].

      eapply approx_comput_functionality_left;[eauto|].

      revert isp2.
      unfold lsubst; boolvar; introv isp2.

      * apply approx_refl; auto.

      * t_change t'.
        eapply lsubst_aux_alpha_congr_same_cl_sub in h; eauto.
        apply alpha_implies_approx2; auto.
Qed.
*)

(*
Lemma compute_step_approx_star {o} :
  forall lib (t1 t2 t3 : @NTerm o),
    approx_star lib t1 t3
    -> compute_step lib t1 = csuccess t2
    -> approx_star lib t2 t3.
Proof.
  nterm_ind t1 as [v|op bs ind] Case; introv ap comp.

  - Case "vterm".
    allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|mrk|abs] SCase.

    + SCase "Can".
      allsimpl; ginv; allsimpl; sp.

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).
      destruct t as [v|op bts]; try (complete (allsimpl; ginv)).

      dopid op as [can2|ncan2|exc2|mrk2|abs2] SSCase.

      * SSCase "Can".
        dopid_noncan ncan SSSCase.

        { SSSCase "NApply".

          clear ind; simpl in comp.
          apply compute_step_apply_success in comp; exrepnd; subst; fold_terms.
          inversion ap as [|? ? ? ? bs len lift ap2]; subst; clear ap.
          allsimpl; repeat (destruct bs; allsimpl; cpx); GC.

          unfold lblift in lift; allsimpl; repnd; GC.
          pose proof (lift 0) as h1; autodimp h1 hyp.
          pose proof (lift 1) as h2; autodimp h2 hyp.
          clear lift.
          allunfold @selectbt; allsimpl.
          allfold (approx_star_bterm lib).

          apply approx_star_bterm_nobnd in h1; exrepnd; subst.
          apply approx_star_bterm_nobnd in h2; exrepnd; subst.
          fold_terms.

          inversion h0 as [|? ? ? ? bs len lift ap3]; subst; clear h0.
          allsimpl; repeat (destruct bs; allsimpl; cpx); GC.

          unfold lblift in lift; allsimpl; repnd; GC.
          pose proof (lift 0) as h3; autodimp h3 hyp.
          clear lift.
          allunfold @selectbt; allsimpl.
          allfold (approx_star_bterm lib).

          apply approx_star_btermd_1var in h3; exrepnd; subst.
          fold_terms.

          assert (approx_open lib (mk_apply (mk_lam vr b3) b0) t3) as ap.
          {
            eapply approx_open_trans;[|exact ap2].
            applydup @approx_open_relates_only_wf in ap2; repnd.
            applydup @approx_open_relates_only_wf in ap3; repnd.

            unfold approx_open.
            apply cl_olift_implies_olift; auto.
            unfold cl_olift; dands; auto;
            [allrw @nt_wf_eq; allrw <- @wf_apply_iff; sp|].
            introv i isp1 isp2.

Abort.

Lemma approx_star_trans {p} :
  forall lib (t1 t2 t3 : @NTerm p),
    approx_star lib t1 t2
    -> approx_star lib t2 t3
    -> approx_star lib t1 t3.
Proof.
  nterm_ind1s t1 as [v1 | op1 bs1 ind1] Case; introv ap1 ap2.

  - Case "vterm".
    inversion ap1 as [? ? ? aop|]; subst; clear ap1.
    apply approx_open_vterm in aop.
    constructor.
    applydup @approx_star_relates_only_wf in ap2; repnd.

    apply approx_open_vterm_iff_reduces_to;[apply wf_term_eq;auto|].

Abort.
*)


(* end hide *)


(* begin hide *)

Lemma bt_wf_bt_wf2 {o} :
  forall (b : @BTerm o),
    bt_wf b <=> bt_wf2 b.
Proof.
  introv; destruct b as [l t]; split; intro k.
  - inversion k; subst.
    constructor.
    apply nt_wf_nt_wf2; auto.
  - inversion k; subst.
    constructor.
    apply nt_wf_nt_wf2; auto.
Qed.

Lemma alphaeq_preserves_noutokens {o} :
  forall (a b : @NTerm o), alpha_eq a b -> (noutokens a <=> noutokens b).
Proof.
  introv aeq.
  unfold noutokens.
  apply alphaeq_preserves_utokens in aeq; rw aeq; sp.
Qed.

Lemma alpha_eq_bterm_preserves_osize {o} :
  forall (lv1 : list NVar) (nt1 : @NTerm o) (lv2 : list NVar) (nt2 : NTerm),
    alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2) -> osize nt1 = osize nt2.
Proof.
  introv aeq.
  inversion aeq as [? ? ? ? ? disj  len1 len2 norep a]; subst.
  apply alpha_eq_preserves_osize in a.
  allrw @lsubst_allvars_preserves_osize2; auto.
Qed.

Theorem approx_star_relates_only_wf {p} : forall lib (t1 t2 : @NTerm p),
  approx_star lib t1 t2 -> nt_wf t1 # nt_wf t2.
Proof.
  nterm_ind1s t1 as [v1|o lbt1 Hind] Case; introv Hap.

  - Case "vterm".
    invertsn Hap. apply approx_open_relates_only_wf in Hap; sp.

  - Case "oterm".
    inverts Hap as Hlen Hrel Hapo.

    apply approx_open_relates_only_wf in Hapo. repnd; split; trivial.
    apply nt_wf_nt_wf2. apply nt_wf_nt_wf2 in Hapo0.
    inverts Hapo0 as H1wf H2wf.
    clear Hapo. constructor; spcf. introv Hlt.
    applydup Hrel in Hlt as Has.
    duplicate Hlt. rw Hlen in Hlt. apply H2wf in Hlt.
    repnd.
    pose proof (selectbt_in2 n lbt1 Hlt0) as H1bt. exrepnd.
    rw H1bt0.
    rw H1bt0 in Has. destruct bt as [lv nt].
    destruct (selectbt lbt1' n) as [lv' nt'].
    allunfold @num_bvars. allsimpl. unfold blift_sub in Has.
    exrepnd; repndors; exrepnd.

    + inverts Has0.
      inverts Has2.
      split; spcf;[]. constructor. apply nt_wf_nt_wf2.
      eapply Hind in Has1; repnd; eauto.
      * allapply @alphaeq_preserves_wf.
        sp3; eauto 4 with slow.
      * allapply @alpha_eq_preserves_osize.
        allrw @lsubst_allvars_preserves_osize2.
        allrw; eauto 3 with slow.

    + subst; repeat (allsimpl; cpx).
      destruct n; allsimpl; cpx.
      repndors; tcsp; subst; GC.
      unfold selectbt in H1bt0; allsimpl; GC.
      pose proof (H2wf 0) as k; clear H2wf.
      repeat (autodimp k hyp).
      unfold selectbt in k; allsimpl; repnd.
      destruct x as [l' t']; allsimpl; repnd; cpx.
      unfold lblift_sub in Hrel; allsimpl; repnd; GC.
      pose proof (Hrel 0) as q; autodimp q hyp; clear Hrel.
      unfold blift_sub in q; exrepnd; repndors; exrepnd; tcsp; GC; subst.
      allunfold @selectbt; allsimpl.
      applydup @alphaeqbt1v2 in q0; exrepnd; subst.
      destruct sub0 as [|z sub0]; allsimpl; tcsp.
      destruct sub0; allsimpl; tcsp; destruct z as [v t]; allsimpl; ginv.
      apply alpha_eq_bterm_sym in q2.
      applydup @alphaeqbt1v2 in q2; exrepnd; subst.
      allsimpl; dands; auto.

      pose proof (Hind nt (lsubst nt0 [(v',t)]) [v'0]) as h; clear Hind; repeat (autodimp h hyp).
      { rw @simple_osize_lsubst; eauto with slow.
        apply alpha_eq_bterm_preserves_osize in q2; allrw; eauto 3 with slow. }
      apply h in q4; repnd; clear h.
      apply bt_wf_bt_wf2.
      apply lsubst_wf_iff in q1; eauto 3 with slow.
      applydup @alphaeqbt_preserves_wf in q2 as btw; apply btw.
      constructor; auto.
Qed.

Theorem approx_starbt_relates_only_wf {p} :
  forall lib op (t1 t2 : @BTerm p),
    approx_star_bterm op lib t1 t2
    -> bt_wf t1 # bt_wf t2.
Proof.
  introv H. destruct t1 as [lv1 nt1]. destruct t2 as [lv2 nt2].
  repeat(rewrite bt_wf_iff).
  allunfold @approx_star_bterm.
  unfold blift_sub in H.
  exrepnd; repndors; exrepnd; subst.

  - apply approx_star_relates_only_wf in H1; repnd.
    invertsna H0 H2bal.
    invertsna H2 H1bal.
    apply alphaeq_preserves_wf in H1bal3.
    apply alphaeq_preserves_wf in H2bal3.
    split; constructor; sp3; eauto 4 with slow.

  - apply approx_star_relates_only_wf in H4; repnd.
    apply lsubst_wf_iff in H1; eauto 3 with slow.
    apply lsubst_wf_iff in H4; eauto 3 with slow.
    apply alphaeqbt_preserves_nt_wf in H2.
    apply alphaeqbt_preserves_nt_wf in H0.
    allrw @bt_wf_iff; auto.
    dands; try (apply H2); try (apply H0); auto.
Qed.

(* end hide *)

Lemma approx_star_congruence {p} :
  forall lib (o: Opid) (lbt1 lbt2 : list (@BTerm p)),
    approx_starbts lib o lbt1 lbt2
    -> map num_bvars lbt2 = OpBindings o
    -> approx_star lib (oterm o lbt1) (oterm o lbt2).
Proof.
  introv  Hbts Hnum2. duplicate Hbts.
  allunfold @approx_starbts.
  repnud Hbts.
  apply apso with (lbt1':=lbt2); spc;[].
  apply approx_open_refl. apply ntot_wf_iff.
  split; auto. introv Hle. rw <- Hbts1 in Hle.
  apply Hbts in Hle.
  apply approx_starbt_relates_only_wf in Hle. repnd; auto.
Qed.

(* begin hide *)

Theorem approx_star_congruence2 {o} :
  forall lib op (lbt1 lbt2 : list (@BTerm o)),
    approx_starbts lib op lbt1 lbt2
    -> nt_wf (oterm op lbt2)
    -> approx_star lib (oterm op lbt1) (oterm op lbt2).
Proof.
   introv Haps Hnt.
   inverts Hnt.
   apply approx_star_congruence; sp.
Qed.

Lemma approx_star_alpha_fun_l {p} :
  forall lib nt1 nt2 nt1',
  @approx_star p lib nt1 nt2
  -> alpha_eq nt1 nt1'
  -> approx_star lib nt1' nt2.
Proof.
  nterm_ind1s nt1 as [v1|o lbt1 Hind] Case; introv Has Hal; duplicate Hal;
  inverts Hal as Hal Hlen; sp;[].

  Case "oterm".
  inverts Has as H1as H2as H3as.

  apply @apso with (lbt1' := lbt1'); spcf;[].
  destruct H2as as [H2as H4as].
  unfold lblift_sub, blift_sub.
  split; spcf;[].
  introv Hlt.
  rw <- Hal in Hlt.
  applydup Hlen in Hlt as Hbal.
  applydup H4as in Hlt as Hbap.
  pose proof (selectbt_in2 n lbt1 Hlt) as H1bt. exrepnd.
  destruct bt as [lv nt].
  rw H1bt0 in Hbal.
  rw H1bt0 in Hbap.
  destruct (selectbt lbt2 n) as [lbt2lv lbt2nt].
  destruct (selectbt lbt1' n) as [btslv btsnt].
  invertsna Hbap Hbbt.
  exrepnd; repndors; exrepnd; subst.

  - eexists; eexists; eexists; dands; eauto 3 with slow.

  - exists (dom_sub sub) nt1 nt0; dands; eauto with slow.
    right.
    exists sub; dands; auto.
Qed.

(* more useful for rewrite tactics*)
Lemma approx_star_alpha_fun_l_iff {p} :
  forall lib nt1 nt1', @alpha_eq p nt1 nt1'
    ->  (forall nt2,(approx_star lib nt1 nt2 <=> approx_star lib nt1' nt2)).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; intro H; eapply approx_star_alpha_fun_l; eauto.
Qed.

(* end hide *)

(* this is not transitivity.
    Clearly, transitivity implies this lemma. (approx_open => approx_star)
    So, it might not be a coincidence that Doug Howe
    chose to prove this, instead
    of transitivity.
    I think I once tried to proved transitivity on paper.
    But I couldnt *)
Lemma approx_star_open_trans {p} :
  forall lib a b c,
    @approx_star p lib a b
    -> approx_open lib b c
    -> approx_star lib a c.
Proof.
  introv Has Hap.
  inverts Has; try (complete (econstructor; eauto 3 with slow)).
Qed.

(* begin hide *)

Hint Resolve alpha_implies_approx_open : slow.

Lemma approx_star_alpha_fun_r {p} :
  forall lib nt1 nt2 nt2',
  @approx_star p lib nt1 nt2
  -> alpha_eq nt2 nt2'
  -> approx_star lib nt1 nt2'.
Proof.
  destruct nt1 as [v1|o lbt1];
  [Case "vterm" | Case "oterm"];
  introv Has Hal.

  - Case "vterm".
    inverts Has. constructor. apply alpha_eq_sym in Hal.
    unfold approx_open.
    rwg Hal; auto.

  - Case "oterm".
    applydup @alpha_eq_sym in Hal.
    applydup @approx_star_relates_only_wf in Has. repnd.
    apply alpha_implies_approx_open in Hal; eauto with slow.

    eapply approx_star_open_trans; eauto with slow.
Qed.

Hint Resolve approx_star_alpha_fun_r approx_star_alpha_fun_l : slow.

(* more useful for rewrite tactics*)
Lemma approx_star_alpha_fun_r_iff {p} :
  forall lib nt2 nt2', @alpha_eq p nt2 nt2'
         -> (forall nt1, (approx_star lib nt1 nt2 <=> approx_star lib nt1 nt2')).
Proof.
  introv Hal. applydup @alpha_eq_sym in Hal.
  split; intro H; eapply approx_star_alpha_fun_r; eauto.
Qed.

Ltac alpharw_as H := let X99:= fresh "Xalrw" in
let lhs := get_alpha_lhs H in
match goal with 
| [ |- approx_star ?lib (lsubst lhs ?sub1) _] =>
    apply (approx_star_alpha_fun_l_iff lib _ _ (lsubst_alpha_congr2 _ _ sub1 H))
| [ |- approx_star ?lib _ (lsubst lhs ?sub1)] =>
    apply (approx_star_alpha_fun_r_iff lib _ _ (lsubst_alpha_congr2 _ _ sub1 H))
| [ |- approx_star ?lib lhs ?rhs ] =>
    apply (approx_star_alpha_fun_l_iff lib _ _ H)
| [ |- approx_star ?lib ?llhs lhs ] =>
    apply (approx_star_alpha_fun_r_iff lib _ _ H)
end.

Ltac alpharwh_as H Hyp := let X99:= fresh "Xalrw" in
let lhs := get_alpha_lhs H in
match goal with
| [ Hyp : (approx_star ?lib (lsubst lhs ?sub1)) |- _ ] =>
    apply (approx_star_alpha_fun_l_iff lib _ _ (lsubst_alpha_congr2 _ _ sub1 H)) in Hyp
| [ Hyp : approx_star ?lib _ (lsubst lhs ?sub1) |- _ ] =>
    apply (approx_star_alpha_fun_r_iff lib _ _ (lsubst_alpha_congr2 _ _ sub1 H)) in Hyp
| [ Hyp : approx_star ?lib lhs ?rhs |- _ ] =>
    apply (approx_star_alpha_fun_l_iff lib _ _ H) in Hyp
| [ Hyp : approx_star ?lib ?lllhs lhs |- _ ] =>
    apply (approx_star_alpha_fun_r_iff lib _ _ H) in Hyp
end.

Lemma blift_sub_alpha_fun_r {p} :
  forall lib op R (nt1 nt2 nt2' : @BTerm p),
    blift_sub lib op R nt1 nt2
    -> alpha_eq_bterm nt2 nt2'
    -> blift_sub lib op R nt1 nt2'.
Proof.
  introv Has Hal.
  repnud Has .
  exrepnd.
  unfold blift.
  exists lv nt0 nt3.
  dands; eauto with slow.
Qed.

Lemma blift_sub_alpha_fun_l {p} :
  forall lib op R (nt1 nt1' nt2 : @BTerm p),
    blift_sub lib op R nt1 nt2
    -> alpha_eq_bterm nt1 nt1'
    -> blift_sub lib op R nt1' nt2.
Proof.
  introv Has Hal.
  repnud Has .
  exrepnd.
  unfold blift.
  exists lv nt0 nt3.
  dands; eauto with slow.
Qed.

Lemma approx_ot_change {p} :
  forall lib lva o lbt (b : @NTerm p),
    approx_star lib (oterm o lbt) b
    -> {lbtcv : list BTerm
        $ disjoint lva (bound_vars (oterm o lbtcv))
        # approx_starbts lib o lbt lbtcv
        # length lbt = length lbtcv
        # approx_open lib (oterm o lbtcv) b}.
Proof.
  introv Has.
  invertsna Has Has.

  pose proof (change_bvars_alpha_wspec_ot lva o lbt1') as Hfr1'.
  exrepnd. duplicate Hfr1'0. invertsna Hfr1'2 XXX.
  exists lbtcv.
  unfold approx_open in Has1.
  rwhg Hfr1'0 Has1.
  dands;spc.
  unfold approx_starbts.
  repnud Has0. unfold lblift_sub.
  dands; spcf;[].
  introv Hlt.

  eapply blift_sub_alpha_fun_r; eauto.
  apply XXX0;spc.
Qed.

Lemma approx_star_bterm_alpha_fun_r {o} :
  forall lib op (b1 b2 b3 : @BTerm o),
    approx_star_bterm lib op b1 b2
    -> alpha_eq_bterm b2 b3
    -> approx_star_bterm lib op b1 b3.
Proof.
  introv ap aeq.
  unfold approx_star_bterm, blift_sub in ap; exrepnd.
  unfold approx_star_bterm, blift_sub.
  exists lv nt1 nt2; dands; auto.
  eapply alpha_eq_bterm_trans;[|eauto].
  eauto with slow.
Qed.
Hint Resolve approx_star_bterm_alpha_fun_r : slow.

Lemma approx_star_bterm_alpha_fun_l {o} :
  forall lib op (b1 b2 b3 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> approx_star_bterm lib op b2 b3
    -> approx_star_bterm lib op b1 b3.
Proof.
  introv aeq ap.
  unfold approx_star_bterm, blift_sub in ap; exrepnd.
  unfold approx_star_bterm, blift_sub.
  exists lv nt1 nt2; dands; auto.
  eapply alpha_eq_bterm_trans;[|eauto].
  eauto with slow.
Qed.
Hint Resolve approx_star_bterm_alpha_fun_l : slow.

Lemma approx_starbts_cons {o} :
  forall lib op (b1 b2 : @BTerm o) bs1 bs2,
    approx_starbts lib op (b1 :: bs1) (b2 :: bs2)
    <=> (approx_star_bterm lib op b1 b2 # approx_starbts lib op bs1 bs2).
Proof.
  introv.
  unfold approx_starbts, lblift_sub; simpl; split; intro k; repnd; cpx; dands; auto.
  - pose proof (k 0) as h; autodimp h hyp; omega.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; omega.
  - introv i.
    destruct n; cpx.
    unfold selectbt; simpl.
    pose proof (k n) as h; autodimp h hyp.
Qed.

Lemma approx_star_berms_alpha_fun_l {o} :
  forall lib op (bs1 bs2 bs3 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2
    -> approx_starbts lib op bs2 bs3
    -> approx_starbts lib op bs1 bs3.
Proof.
  induction bs1; introv aeq ap.

  - destruct bs2.

    + destruct bs3; auto.

    + unfold alpha_eq_bterms in aeq; allsimpl; sp.

  - destruct bs2.

    + unfold alpha_eq_bterms in aeq; allsimpl; sp.

    + apply alpha_eq_bterms_cons in aeq; repnd.
      destruct bs3.

      * unfold approx_starbts, lblift_sub in ap; allsimpl; sp.

      * allrw @approx_starbts_cons; repnd; dands; eauto with slow.
Qed.
Hint Resolve approx_star_berms_alpha_fun_l : slow.

Lemma approx_star_berms_alpha_fun_r {o} :
  forall lib op (bs1 bs2 bs3 : list (@BTerm o)),
    alpha_eq_bterms bs2 bs3
    -> approx_starbts lib op bs1 bs2
    -> approx_starbts lib op bs1 bs3.
Proof.
  induction bs1; introv aeq ap.

  - destruct bs2.

    + destruct bs3; auto.
      unfold alpha_eq_bterms in aeq; allsimpl; sp.

    + destruct bs3; auto.
      * unfold alpha_eq_bterms in aeq; allsimpl; sp.
      * unfold approx_starbts, lblift_sub in ap; allsimpl; sp.

  - destruct bs2.

    + unfold approx_starbts, lblift_sub in ap; allsimpl; sp.

    + allrw @approx_starbts_cons; repnd.
      destruct bs3.

      * unfold alpha_eq_bterms in aeq; allsimpl; sp.

      * apply alpha_eq_bterms_cons in aeq; repnd.
        allrw @approx_starbts_cons; repnd; dands; eauto with slow.
Qed.
Hint Resolve approx_star_berms_alpha_fun_r : slow.

Lemma alpha_eq_oterm_implies_combine2 {o} :
  forall (op : Opid) (bs : list BTerm) (t : @NTerm o),
    alpha_eq (oterm op bs) t
    -> {bs' : list BTerm
        $ t = oterm op bs'
        # alpha_eq_bterms bs bs'}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq.
  auto.
Qed.

Lemma lblift_sub_eq {o} :
  forall lib (op : Opid) (R : NTrel) (bs1 bs2: list (@BTerm o)),
    lblift_sub lib op R bs1 bs2
    <=>
    (length bs1 = length bs2
     # forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> blift_sub lib op R b1 b2).
Proof.
  introv.
  unfold lblift_sub; split; introv k; repnd; dands; auto; introv i.
  - unfold selectbt in k.
    apply (in_nth_combine_iff _ _ default_bt default_bt) in i; exrepnd; subst.
    apply k; auto.
  - unfold selectbt.
    apply k.
    apply (in_nth_combine_iff _ _ default_bt default_bt).
    exists n; dands; auto; try omega.
Qed.

Lemma ex_change_bvars_bterm_alpha {o} :
  forall (lv : list NVar) (bt : @BTerm o),
    {bt' : BTerm $ disjoint lv (bound_vars_bterm bt') # alpha_eq_bterm bt bt'}.
Proof.
  introv.
  pose proof (change_bvars_alpha_wspec lv (oterm Exc [bt])) as h.
  exrepnd.
  apply alpha_eq_oterm_implies_combine in h0; exrepnd; allsimpl; cpx; allsimpl.
  allrw app_nil_r.
  pose proof (h2 bt x) as k; clear h2; autodimp k hyp.
  exists x; sp.
Qed.

Lemma get_utokens_lsubst_aux_allvars {o} :
  forall (t : @NTerm o) (sub : Substitution),
    allvars_sub sub
    -> get_utokens (lsubst_aux t sub) = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv avs; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_allvars in Heqsf; auto; exrepnd; subst; allsimpl; auto.

  - Case "oterm".
    apply app_if; auto.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; simpl.
    eapply ind; eauto with slow.
Qed.

Lemma get_utokens_lsubst_allvars {o} :
  forall (t : @NTerm o) (sub : Substitution),
    allvars_sub sub
    -> get_utokens (lsubst t sub) = get_utokens t.
Proof.
  introv avs.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  rw @get_utokens_lsubst_aux_allvars; auto.
  apply alphaeq_preserves_utokens; eauto with slow.
Qed.

Lemma nrut_sub_change_sub_same_range {o} :
  forall l (sub1 sub2 : @Sub o),
    range sub1 = range sub2
    -> nrut_sub l sub1
    -> nrut_sub l sub2.
Proof.
  induction sub1; destruct sub2; introv eqr nrut; allsimpl; tcsp.
  destruct a, p; allsimpl; cpx.
  allrw @nrut_sub_cons; exrepnd; subst.
  eexists; dands; eauto.
  allunfold @get_utokens_sub.
  inversion eqr as [x]; auto.
Qed.

Lemma allvars_sub_implies_shallow_sub {o} :
  forall sub : @Sub o,
    allvars_sub sub -> shallow_sub sub.
Proof.
  induction sub; introv avs; eauto with slow.
  destruct a as [v t].
  allrw @allvars_sub_cons; repnd.
  rw @shallow_sub_cons; dands; auto.
  allapply @isvariable_implies; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve allvars_sub_implies_shallow_sub : slow.

Lemma shallow_sub_combine_range {o} :
  forall (sub : @Sub o) l,
    shallow_sub sub
    -> shallow_sub (combine l (range sub)).
Proof.
  induction sub; introv sh; allsimpl.
  - rw combine_nil; auto.
  - destruct a as [vs t]; allsimpl.
    destruct l; allsimpl; eauto with slow.
    allrw @shallow_sub_cons; repnd; dands; auto.
Qed.
Hint Resolve shallow_sub_combine_range : slow.

Lemma lsubst_nest_swap3 {o} :
  forall (t : @NTerm o) (sub1 sub2 : Sub),
    disjoint (dom_sub sub1) (sub_free_vars sub2)
    -> disjoint (dom_sub sub2) (sub_free_vars sub1)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> disjoint (sub_bound_vars sub1) (sub_free_vars sub2)
    -> disjoint (sub_bound_vars sub2) (sub_free_vars sub1)
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> disjoint (bound_vars t) (sub_free_vars sub2)
    -> lsubst (lsubst t sub1) sub2 = lsubst (lsubst t sub2) sub1.
Proof.
  introv d1 d2 d3 s4 d5 d6 d7.
  apply lsubst_nest_swap2;
    allrw <- @sub_free_vars_is_flat_map_free_vars_range;
    allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
    allrw disjoint_app_r; auto.
Qed.

Lemma sub_free_vars_nrut_sub {o} :
  forall (sub : @Sub o) l,
    nrut_sub l sub -> sub_free_vars sub = [].
Proof.
  induction sub; introv nrut; allsimpl; auto.
  destruct a as [v t].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl.
  eapply IHsub; eauto.
Qed.

Lemma sub_free_vars_combine_range {o} :
  forall (sub : @Sub o) l,
    length l = length sub
    -> sub_free_vars (combine l (range sub)) = sub_free_vars sub.
Proof.
  induction sub; destruct l; introv e; allsimpl; tcsp; cpx; allsimpl.
  apply app_if; auto.
Qed.

Lemma sub_bound_vars_nrut_sub {o} :
  forall (sub : @Sub o) l,
    nrut_sub l sub -> sub_bound_vars sub = [].
Proof.
  induction sub; introv nrut; allsimpl; auto.
  destruct a as [v t].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl.
  eapply IHsub; eauto.
Qed.

Lemma sub_bound_vars_combine_range {o} :
  forall (sub : @Sub o) l,
    length l = length sub
    -> sub_bound_vars (combine l (range sub)) = sub_bound_vars sub.
Proof.
  induction sub; destruct l; introv e; allsimpl; tcsp; cpx; allsimpl.
  apply app_if; auto.
Qed.

Lemma allvars_sub_implies_oshallow_sub {o} :
  forall (sub : @Sub o), allvars_sub sub -> oshallow_sub sub.
Proof.
  introv all i.
  unfold allvars_sub, sub_range_sat in all.
  apply in_range_iff in i; exrepnd.
  apply all in i0.
  unfold isvarc in i0; exrepnd; subst; allsimpl; auto.
Qed.
Hint Resolve allvars_sub_implies_oshallow_sub : slow.

Lemma oshallow_sub_combine_range {o} :
  forall (sub : @Sub o) (l : list NVar),
    oshallow_sub sub -> oshallow_sub (combine l (range sub)).
Proof.
  introv sh i.
  allrw @in_range_iff; exrepnd.
  apply in_combine in i0; repnd.
  allrw @in_range_iff; exrepnd.
  pose proof (sh t) as h.
  autodimp h hyp.
  apply in_range_iff; eexists; eauto.
Qed.
Hint Resolve oshallow_sub_combine_range : slow.

(*
Lemma change_bvars_bterm_alpha_vs {o} :
  forall (l lv : list NVar) (bt : @BTerm o),
    {t : NTerm
     $ disjoint lv (l ++ bound_vars t)
     # alpha_eq_bterm bt (bterm l t)}.
Proof.
  introv.
  SearchAbout alpha_eq_bterm var_ren.
  pose proof (change_bvars_alpha_wspec lv (oterm (Exc None) [bt])) as h.
  exrepnd.
  apply alpha_eq_oterm_implies_combine in h0; exrepnd; allsimpl; cpx; allsimpl.
  allrw app_nil_r.
  pose proof (h2 bt x) as k; clear h2; autodimp k hyp.
  exists x; sp.
Qed.
*)

Lemma get_utokens_lib_lsubst_aux_allvars {o} :
  forall lib (t : @NTerm o) (sub : Substitution),
    allvars_sub sub
    -> get_utokens_lib lib (lsubst_aux t sub) = get_utokens_lib lib t.
Proof.
  introv h.
  unfold get_utokens_lib; f_equal.
  apply get_utokens_lsubst_aux_allvars; auto.
Qed.

Lemma get_utokens_lib_lsubst_allvars {o} :
  forall lib (t : @NTerm o) (sub : Substitution),
    allvars_sub sub
    -> get_utokens_lib lib (lsubst t sub) = get_utokens_lib lib t.
Proof.
  introv avs.
  unfold get_utokens_lib; f_equal.
  apply get_utokens_lsubst_allvars; auto.
Qed.

(* lemma 0.6 in annotated paper/
  This proof is rather long.
  But this lemma will simplify some of the reasoning required in this proof
  It will enable us to prove lemmas for destructing approx_star(_bterm)
  hypotheses
  so that the bound variables are picked nicely.
 Even now, approx_ot_change can be used to simplify the proof.
 *)

Theorem approx_star_lsubst_vars {p} :
  forall lib a b lvi lvo,
    length lvi = length lvo ->
    let sub := @var_ren p lvi lvo in
    approx_star lib a b
    -> approx_star lib (lsubst a sub) (lsubst b sub).
Proof.
  nterm_ind1s a as [?| o lbta Hind] Case; introv len Hap; auto.

  - Case "vterm".
    invertsn Hap.
    apply approx_open_implies_approx_star.
    apply approx_open_lsubst; sp.

  - Case "oterm".
    apply (approx_ot_change _ lvo) in Hap; exrepnd.

    pose proof (unfold_lsubst (var_ren lvi lvo) (oterm o lbta)) as h1; exrepnd.
    apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst.
    rw h0; clear h0.

    pose proof (unfold_lsubst (var_ren lvi lvo) b) as k1; exrepnd.
    rw k0; clear k0.

    eapply approx_open_alpha_rw_r_aux in Hap0;[|exact k1].
    clear b k1.
    rename t' into b.

    assert (length bs' = length lbtcv) as eql.
    { unfold alpha_eq_bterms in h3; repnd; omega. }

    eapply approx_star_berms_alpha_fun_l in Hap2;
      [|apply alpha_eq_bterms_sym;exact h3].

    allsimpl.
    repeat (onerw @sub_free_vars_var_ren; auto).
    apply disjoint_sym in Hap1.
    apply (apso _ _ _ _ (map (fun t : BTerm => lsubst_bterm_aux t (var_ren lvi lvo)) lbtcv));
      allrw map_length; auto;
      [|apply (approx_open_lsubst _ _ _ lvi lvo) in Hap0;
         unfold lsubst in Hap0;
         allrw <- @sub_free_vars_is_flat_map_free_vars_range;
         allsimpl;
         repeat (onerw @sub_free_vars_var_ren; auto);
         boolvar; tcsp;
         provefalse; destruct n; eauto with slow].

    apply lblift_sub_eq; allrw map_length; dands; auto.
    introv i.
    allrw <- @map_combine.
    rw in_map_iff in i; exrepnd; cpx; allsimpl.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2].
    allsimpl.
    applydup in_combine in i1 as ib; repnd.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.
    unfold blift_sub.
    unfold approx_starbts in Hap2.
    apply lblift_sub_eq in Hap2; repnd; GC.
    applydup Hap2 in i1 as bl.

    unfold blift_sub in bl.
    exrepnd.

    pose proof (fresh_vars (length lv)
                           (lvo ++ lvi
                                ++ lv
                                ++ free_vars nt1
                                ++ free_vars nt2
                                ++ (remove_nvars l1 (free_vars t1))
                                ++ (remove_nvars l2 (free_vars t2)))) as d; exrepnd.
    allrw disjoint_app_r; repnd.

    pose proof (alpha_bterm_pair_change4
                  (bterm l1 t1) (bterm l2 t2)
                  lv nt1 nt2
                  lvn lvo) as aeq; simpl in aeq.
    repeat (autodimp aeq hyp).
    { allrw disjoint_app_r; dands; eauto 3 with slow. }
    exrepnd.
    remember (lsubst nt1n (var_ren lv lvn)) as u1.
    remember (lsubst nt2n (var_ren lv lvn)) as u2.
    allrw disjoint_app_l; allrw disjoint_app_r; repnd.
    assert (disjoint (bound_vars u1) lvo) as disj1.
    { subst; rw @boundvars_lsubst_vars; eauto with slow. }
    assert (disjoint (bound_vars u2) lvo) as disj2.
    { subst; rw @boundvars_lsubst_vars; eauto with slow. }

    dup aeq3 as aeqs1.
    apply (lsubst_alphabt_congr _ _ (var_ren lvi lvo)) in aeqs1;
      [|try (rw <- @sub_free_vars_is_flat_map_free_vars_range);
         try (rw @sub_free_vars_var_ren); auto; simpl;
         allrw disjoint_app_l; dands; complete (eauto 3 with slow)].
    dup aeq4 as aeqs2.
    apply (lsubst_alphabt_congr _ _ (var_ren lvi lvo)) in aeqs2;
      [|try (rw <- @sub_free_vars_is_flat_map_free_vars_range);
         try (rw @sub_free_vars_var_ren); auto; simpl;
         allrw disjoint_app_l; dands; complete (eauto 3 with slow)].
    allsimpl.

    exists lvn
           (lsubst_aux u1 (sub_filter (var_ren lvi lvo) lvn))
           (lsubst_aux u2 (sub_filter (var_ren lvi lvo) lvn)).
    dands; auto.

    repndors; exrepnd.

    + left; dands; auto.
      assert {l' : list NVar & {u' : NTerm & LIn (bterm l' u') lbta # alpha_eq_bterm (bterm l' u') (bterm l1 t1)}} as aeqb.
      { apply alpha_eq_bterms_sym in h3; unfold alpha_eq_bterms in h3; repnd.
        pose proof (combine_in_left _ _ bs' lbta) as k.
        autodimp k hyp; apply k in ib0; exrepnd.
        destruct u0 as [l' u'].
        applydup in_combine in ib5; repnd.
        apply h3 in ib5.
        eexists; eexists; dands; eauto with slow. }
      exrepnd.

      assert (approx_star lib nt1n nt2n) as apr by (eauto 3 with slow).

      pose proof (Hind u' nt1n l' aeqb0) as h.
      autodimp h hyp.
      { apply alpha_eq_bterm_preserves_osize in aeqb1; rw aeqb1.
        apply alpha_eq_bterm_preserves_osize in bl2; rw bl2; auto.
        apply alpha_eq_preserves_osize in aeq0; rw aeq0; eauto 3 with slow. }
      pose proof (h nt2n lv lvn) as aprs1; clear h; repeat (autodimp aprs1 hyp).

      pose proof (Hind u' (lsubst nt1n (var_ren lv lvn)) l' aeqb0) as h.
      autodimp h hyp.
      { rw @lsubst_allvars_preserves_osize2; auto.
        apply alpha_eq_bterm_preserves_osize in aeqb1; rw aeqb1.
        apply alpha_eq_bterm_preserves_osize in bl2; rw bl2; auto.
        apply alpha_eq_preserves_osize in aeq0; rw aeq0; eauto 3 with slow. }
      pose proof (@sub_filter_var_ren_implies p lvi lvo lvn) as vr; exrepnd.
      pose proof (h (lsubst nt2n (var_ren lv lvn)) vs3 vs4) as aprs2; clear h.
      repeat (autodimp aprs2 hyp).
      repeat (rw vr0).
      rw <- @lsubst_lsubst_aux2; eauto 3 with slow.
      rw <- @lsubst_lsubst_aux2; eauto 3 with slow.
      subst; auto.

    + right.

      pose proof (lsubst_nest_same_alpha nt1n (dom_sub sub) lvn (range sub)) as nest1.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest1 hyp).
      { subst; allrw @length_dom; allrw @length_range; auto. }
      { subst; allrw @length_dom; allrw @length_range; auto. }
      { apply alphaeq_preserves_free_vars in aeq0; rw <- aeq0; auto. }
      rw <- @sub_eta in nest1.

      pose proof (lsubst_nest_same_alpha nt2n (dom_sub sub) lvn (range sub)) as nest2.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest2 hyp).
      { subst; allrw @length_dom; allrw @length_range; auto. }
      { subst; allrw @length_dom; allrw @length_range; auto. }
      { apply alphaeq_preserves_free_vars in aeq2; rw <- aeq2; auto. }
      rw <- @sub_eta in nest2.

      pose proof (lsubst_alpha_congr2 nt1 nt1n sub aeq0) as as1.
      pose proof (lsubst_alpha_congr2 nt2 nt2n sub aeq2) as as2.

      remember (combine lvn (range sub)) as sub'.
      exists sub'; dands; auto;
      [| subst;
         apply (alphaeq_preserves_get_utokens_lib lib) in aeq0;
         apply (alphaeq_preserves_get_utokens_lib lib) in aeq2;
         repeat (rw @get_utokens_lib_lsubst_aux_allvars; eauto with slow);
         repeat (rw @get_utokens_lib_lsubst_allvars; eauto with slow);
         rw <- aeq0; rw <- aeq2;
         eapply nrut_sub_change_sub_same_range;[|exact bl5];
         rw @range_combine; auto; allrw @length_range; allrw @length_dom;
         complete auto
       | subst; rw @dom_sub_combine; auto;
         allrw @length_dom; allrw @length_range;
         complete auto].

      assert (approx_star
                lib
                (lsubst (lsubst nt1n (var_ren (dom_sub sub) lvn)) sub')
                (lsubst (lsubst nt2n (var_ren (dom_sub sub) lvn)) sub'))
             as apr.
      { eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym in nest2; exact nest2].
        eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym in nest1; exact nest1].
        eauto 3 with slow. }
      rw <- bl3 in apr.

      assert {l' : list NVar & {u' : NTerm & LIn (bterm l' u') lbta # alpha_eq_bterm (bterm l' u') (bterm l1 t1)}} as aeqb.
      { apply alpha_eq_bterms_sym in h3; unfold alpha_eq_bterms in h3; repnd.
        pose proof (combine_in_left _ _ bs' lbta) as k.
        autodimp k hyp; apply k in ib0; exrepnd.
        destruct u0 as [l' u'].
        applydup in_combine in ib5; repnd.
        apply h3 in ib5.
        eexists; eexists; dands; eauto with slow. }
      exrepnd.

      pose proof (Hind u' (lsubst (lsubst nt1n (var_ren lv lvn)) sub') l' aeqb0) as h.
      autodimp h hyp.
      { subst; repeat (rw @simple_osize_lsubst); eauto 4 with slow;[].
        apply alpha_eq_bterm_preserves_osize in aeqb1; rw aeqb1.
        apply alpha_eq_bterm_preserves_osize in bl2; rw bl2.
        apply alpha_eq_preserves_osize in aeq0; rw aeq0; eauto 3 with slow. }
      pose proof (@sub_filter_var_ren_implies p lvi lvo lvn) as vr; exrepnd.
      pose proof (h (lsubst (lsubst nt2n (var_ren lv lvn)) sub') vs3 vs4) as apr2.
      repeat (autodimp apr2 hyp).
      repeat (rw vr0).
      rw <- @lsubst_lsubst_aux2; eauto 3 with slow.
      rw <- @lsubst_lsubst_aux2; eauto 3 with slow.
      rw <- Hequ1 in apr2; rw <- Hequ2 in apr2.

      assert (sub_free_vars sub' = []) as em1.
      { subst; allrw @length_dom.
        rw @sub_free_vars_combine_range; auto.
        erewrite @sub_free_vars_nrut_sub; eauto. }

      assert (sub_bound_vars sub' = []) as em2.
      { subst; allrw @length_dom.
        rw @sub_bound_vars_combine_range; auto.
        erewrite @sub_bound_vars_nrut_sub; eauto. }

      pose proof (lsubst_nest_swap3 u1 (var_ren vs3 vs4) sub') as e1.
      rw em1 in e1; rw em2 in e1.
      rw @dom_sub_var_ren in e1; auto.
      rw @sub_bound_vars_var_ren in e1; auto.
      rw @sub_free_vars_var_ren in e1; auto.
      repeat (autodimp e1 hyp); eauto 3 with slow.
      { subst; allrw @length_dom.
        rw @dom_sub_combine; eauto with slow.
        rw @length_range; auto. }
      { subst; allrw @length_dom.
        rw @dom_sub_combine; allrw @length_range; auto.
        eapply eqvars_disjoint;[apply eqvars_sym; exact vr2|]; eauto with slow. }
      rw e1.

      pose proof (lsubst_nest_swap3 u2 (var_ren vs3 vs4) sub') as e2.
      rw em1 in e2; rw em2 in e2.
      rw @dom_sub_var_ren in e2; auto.
      rw @sub_bound_vars_var_ren in e2; auto.
      rw @sub_free_vars_var_ren in e2; auto.
      repeat (autodimp e2 hyp); eauto 3 with slow.
      { subst; allrw @length_dom.
        rw @dom_sub_combine; eauto with slow.
        rw @length_range; auto. }
      { subst; allrw @length_dom.
        rw @dom_sub_combine; allrw @length_range; auto.
        eapply eqvars_disjoint;[apply eqvars_sym; exact vr2|]; eauto with slow. }
      rw e2.

      auto.
Qed.

(* The key complication in prev. proof
    was that the approx_star hypothesis "picks"
    variables and terms which might cause problems(renaming)
    during substitution. We used the induction hypothesis
    to "replaces" them with alpha equal "nice" ones. Now, we can
    state a general purpose lemma for that effect. *)

Lemma approx_star_btermd {p} :
  forall lib op bt1 bt2 lva,
    op <> NCan NFresh
    -> approx_star_bterm lib op bt1 bt2
    -> {lvn : list NVar
        & {nt1',nt2' : @NTerm p
          $ approx_star lib nt1' nt2'
          # alpha_eq_bterm bt1 (bterm lvn nt1')
          # alpha_eq_bterm bt2 (bterm lvn nt2')
          # no_repeats lvn
          (* # disjoint lvn (all_vars (get_nt bt1) ++ all_vars (get_nt bt2)) *)
          # disjoint (lvn ++ (bound_vars nt1') ++ (bound_vars nt2')) lva   } }.
Proof.
  introv d Hab.
  unfold approx_star_bterm in Hab.
  repnud Hab. exrepnd.
  pose proof (alpha_bterm_pair_change _ _ _ _ _ lva Hab2 Hab0) as Hp.
  exrepnd.
  exists lvn.

  repndors; exrepnd; subst; tcsp.

  alpharwh_as Hp2 Hab1.
  alpharwh_as Hp3 Hab1.
  exists (lsubst nt1n (var_ren lv lvn)).
  exists (lsubst nt2n (var_ren lv lvn)).
  spc;[| disjoint_reasoningv;spcls;
         apply disjoint_bound_vars_lsubst; spcls;disjoint_reasoningv;fail].
  apply approx_star_lsubst_vars;spc.
Qed.

Lemma approx_star_samevar {p} :
  forall lib op a b lv,
    op <> NCan NFresh
    -> approx_star_bterm lib op (bterm lv a) (@bterm p lv b)
    -> approx_star lib a b.
Proof.
  introv d Has.
  apply (approx_star_btermd _ _ _ _ lv) in Has; auto.
  exrepnd.
  pose proof (change_bvars_alpha_wspec lv a) as Hfa.
  exrepnd. rename ntcv into a'.
  assert (approx_star lib a' b) ;[| eauto with slow].
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfa0.
  assert (alpha_eq_bterm (bterm lv a') (bterm lvn nt1'))
      as Xa by eauto with slow.

  pose proof (change_bvars_alpha_wspec lv b) as Hfb.
  exrepnd. rename ntcv into b'.
  assert (approx_star lib a' b') ;[| eauto with slow].
  apply @alpha_eq_bterm_congr with (lv:=lv) in Hfb0.
  assert (alpha_eq_bterm (bterm lv b') (bterm lvn nt2'))
      as Xb by eauto with slow.
  clear dependent a.
  clear dependent b.
  invertsna Xa Hb.
  invertsna Xb Ha.
  apply lsubst_alpha_congr2 with (sub:=var_ren lv3 lv) in Ha3.
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Ha3;spc; disjoint_reasoningv;[].
  apply lsubst_alpha_congr2 with (sub:=var_ren lv0 lv) in Hb3.
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  rw @lsubst_nest_vars_same in Hb3;spc; disjoint_reasoningv;[].
  Hint Resolve lsubst_trivial_alpha : slow.
  assert (alpha_eq b' (lsubst nt2' (var_ren lvn lv))) as Xa by eauto with slow.
  assert (alpha_eq a' (lsubst nt1' (var_ren lvn lv))) as Xb by eauto with slow.
  clear Ha3 Hb3.
  apply approx_star_lsubst_vars with (lvi:=lvn) (lvo:=lv) in Has1;spc;[].
  eauto with slow.
Qed.

Lemma blift_sub_numbvars {o} :
  forall lib op R (bt1 bt2 : @BTerm o),
    blift_sub lib op R bt1 bt2
    -> num_bvars bt1 = num_bvars bt2.
Proof.
  introv Hr.
  repnud Hr.
  exrepnd.
  inverts Hr0.
  inverts Hr2.
  unfold num_bvars. simpl. spc.
Qed.

Lemma approx_star_bterm_nobnd {p} : forall lib op a bt,
  approx_star_bterm lib op (bterm [] a) bt
  -> {b : @NTerm p
      $ bt = (bterm [] b)
      # approx_star lib a b}.
Proof.
  introv Has.
  applydup @blift_sub_numbvars in Has.
  unfold num_bvars in Has0. simpl in Has0.
  destruct bt as [lv b]; allsimpl; cpx.
  exists b; dands; eauto.
  unfold approx_star_bterm, blift_sub in Has; exrepnd.
  apply alphaeqbt_nilv in Has2; exrepnd; ginv.
  apply alphaeqbt_nilv in Has0; exrepnd; ginv.
  repndors; exrepnd; subst; cpx; eauto 5 with slow.
  destruct sub; allsimpl; ginv.
  allrw @lsubst_nil.
  eauto with slow.
Qed.

Lemma approx_star_btermd_1var {p} :
  forall lib op v a bt,
    approx_star_bterm lib op (bterm [v] a) bt
    -> {vr : NVar
        $ {b : @NTerm p
        $ bt = (bterm [vr] b)
        # approx_star_bterm lib op (bterm [v] a) (bterm [vr] b)}}.
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

(* end hide *)
