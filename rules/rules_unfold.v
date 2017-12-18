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

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export lsubst_hyps.
Require Export per_can.


Definition get_abstraction_name_op {o} (op : @Opid o) : option opname :=
  match op with
  | Can _ => None
  | NCan _ => None
  | Exc => None
  | Abs abs => Some (opabs_name abs)
  end.

Definition get_abstraction_name {o} (t : @NTerm o) : option opname :=
  match t with
  | vterm _ => None
  | sterm _ => None
  | oterm op _ => get_abstraction_name_op op
  end.

Definition maybe_unfold {o} lib abstractions (t : @NTerm o) :=
  match get_abstraction_name t with
  | Some name =>
    if in_deq _ String.string_dec name abstractions then
      match unfold lib t with
      | Some u => u
      | None => t
      end
    else t
  | None => t
  end.

Fixpoint unfold_abstractions {o} lib abstractions (t : @NTerm o) :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm f
  | oterm op bs =>
    maybe_unfold lib abstractions (oterm op (map (unfold_abstractions_b lib abstractions) bs))
  end
with unfold_abstractions_b {o} lib abstractions (b : @BTerm o) :=
       match b with
       | bterm vs t => bterm vs (unfold_abstractions lib abstractions t)
       end.

Hint Resolve matching_entry_implies_matching_bterms : slow.

Lemma unfold_abs_some_implies_unfold_abs_entry_some {o} :
  forall lib abs bs (t : @NTerm o),
    unfold_abs lib abs bs = Some t
    -> {entry : library_entry & unfold_abs_entry entry abs bs = Some t}.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  remember (unfold_abs_entry a abs bs) as uae; symmetry in Hequae.
  destruct uae; ginv.
  exists a; auto.
Qed.

Lemma free_vars_unfold_abs_entry {o} :
  forall entry abs (bs : list (@BTerm o)) t,
    unfold_abs_entry entry abs bs = Some t
    -> subset (free_vars t) (free_vars_bterms bs).
Proof.
  introv h; destruct entry; simpl in *; boolvar; ginv.
  pose proof (subvars_free_vars_mk_instance vars bs rhs) as q.
  unfold free_vars_bterms.
  rw subvars_eq in q.
  apply q; eauto 2 with slow.
Qed.

Lemma free_vars_unfold_abs {o} :
  forall lib abs (bs : list (@BTerm o)) t,
    unfold_abs lib abs bs = Some t
    -> subset (free_vars t) (free_vars_bterms bs).
Proof.
  introv h; apply unfold_abs_some_implies_unfold_abs_entry_some in h; exrepnd.
  eapply free_vars_unfold_abs_entry; eauto.
Qed.

Lemma unfold_abstractions_preserves_free_vars {o} :
  forall lib abs (t : @NTerm o),
    subset (free_vars (unfold_abstractions lib abs t)) (free_vars t).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv i; simpl in *; auto.

  Case "oterm".
  unfold maybe_unfold in i; simpl in *.
  destruct op; simpl in *; auto; allrw lin_flat_map; exrepnd;
    allrw in_map_iff; exrepnd; subst; simpl in *.

  - destruct a as [l t]; simpl in *.
    apply in_remove_nvars in i0; repnd.
    applydup ind in i1.
    applydup i3 in i2.
    eexists; dands; eauto.
    simpl.
    apply in_remove_nvars; dands; auto.

  - destruct a as [l t]; simpl in *.
    apply in_remove_nvars in i0; repnd.
    applydup ind in i1.
    applydup i3 in i2.
    eexists; dands; eauto.
    simpl.
    apply in_remove_nvars; dands; auto.

  - destruct a as [l t]; simpl in *.
    apply in_remove_nvars in i0; repnd.
    applydup ind in i1.
    applydup i3 in i2.
    eexists; dands; eauto.
    simpl.
    apply in_remove_nvars; dands; auto.

  - boolvar.

    + rename o0 into a.
      remember (unfold_abs lib a (map (unfold_abstractions_b lib abs) bs)) as uop.
      symmetry in Hequop; destruct uop.

      * apply free_vars_unfold_abs in Hequop.
        apply Hequop in i.
        unfold free_vars_bterms in i.
        apply lin_flat_map in i; exrepnd.
        apply in_map_iff in i1; exrepnd; subst.
        destruct a0 as [vs t]; simpl in *.
        apply in_remove_nvars in i0; repnd.
        applydup ind in i1.
        applydup i3 in i2.
        eexists; dands; eauto.
        simpl.
        apply in_remove_nvars; dands; auto.

      * simpl in *.
        apply lin_flat_map in i; exrepnd.
        apply in_map_iff in i1; exrepnd; subst; simpl in *.
        destruct a0 as [vs t]; simpl in *.
        apply in_remove_nvars in i0; repnd.
        applydup ind in i1.
        applydup i3 in i2.
        eexists; dands; eauto.
        simpl.
        apply in_remove_nvars; dands; auto.

    + simpl in *.
      apply lin_flat_map in i; exrepnd.
      apply in_map_iff in i1; exrepnd; subst; simpl in *.
      destruct a as [vs t]; simpl in *.
      apply in_remove_nvars in i0; repnd.
      applydup ind in i1.
      applydup i3 in i2.
      eexists; dands; eauto.
      simpl.
      apply in_remove_nvars; dands; auto.
Qed.

Lemma unfold_abs_implies_find_entry {o} :
  forall lib abs bs (t : @NTerm o),
    unfold_abs lib abs bs = Some t
    ->
    {abs' : opabs
     & {vars : list sovar_sig
     & {rhs : SOTerm
     & {correct : correct_abs abs' vars rhs
     & matching_entry abs abs' vars bs
     # t = mk_instance vars bs rhs
     # find_entry lib abs bs = Some (lib_abs abs' vars rhs correct)}}}}.
Proof.
  induction lib; introv h; simpl in *; ginv.
  destruct a; simpl in *; boolvar; ginv; tcsp.
  eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma unfold_abstractions_preserves_nt_wf {o} :
  forall lib abs (t : @NTerm o),
    nt_wf t
    -> nt_wf (unfold_abstractions lib abs t).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv wf; simpl in *; auto.

  Case "oterm".

  unfold maybe_unfold; simpl in *.
  destruct op; simpl in *; auto; allrw @nt_wf_oterm_iff; repnd; dands; auto;
    allrw map_map; unfold compose in *; simpl in *; tcsp.

  - rewrite <- wf0.
    apply eq_maps; introv i.
    destruct x; unfold num_bvars; simpl; auto.

  - introv i.
    apply in_map_iff in i; exrepnd; subst.
    destruct a as [l t]; simpl in *.
    applydup wf in i1.
    allrw @bt_wf_iff.
    eapply ind; eauto.

  - rewrite <- wf0.
    apply eq_maps; introv i.
    destruct x; unfold num_bvars; simpl; auto.

  - introv i.
    apply in_map_iff in i; exrepnd; subst.
    destruct a as [l t]; simpl in *.
    applydup wf in i1.
    allrw @bt_wf_iff.
    eapply ind; eauto.

  - rewrite <- wf0.
    apply eq_maps; introv i.
    destruct x; unfold num_bvars; simpl; auto.

  - introv i.
    apply in_map_iff in i; exrepnd; subst.
    destruct a as [l t]; simpl in *.
    applydup wf in i1.
    allrw @bt_wf_iff.
    eapply ind; eauto.

  - boolvar.

    + rename o0 into a.
      remember (unfold_abs lib a (map (unfold_abstractions_b lib abs) bs)) as uop.
      symmetry in Hequop; destruct uop.

      * apply unfold_abs_implies_find_entry in Hequop; exrepnd; subst.
        apply nt_wf_eq.
        eapply wf_mk_instance; eauto.
        introv i.
        apply in_map_iff in i; exrepnd; subst.
        destruct a0 as [vs t]; simpl in *.
        applydup wf in i1.
        apply bt_wf_eq.
        allrw @bt_wf_iff.
        eapply ind; eauto.

      * allrw @nt_wf_oterm_iff.
        allrw map_map; unfold compose; simpl.
        allrw <- .
        dands.

        { apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

        introv i; allrw in_map_iff; exrepnd; subst.
        applydup wf in i1.
        destruct a0 as [vs t].
        allrw @bt_wf_iff.
        eapply ind; eauto.

    + allrw @nt_wf_oterm_iff.
      allrw map_map; unfold compose; simpl.
      allrw <- .
      dands.

      { apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

      introv i; allrw in_map_iff; exrepnd; subst.
      applydup wf in i1.
      destruct a as [vs t].
      allrw @bt_wf_iff.
      eapply ind; eauto.
Qed.
Hint Resolve unfold_abstractions_preserves_nt_wf : slow.

Lemma isprog_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o),
    isprog t
    -> isprog (unfold_abstractions lib abs t).
Proof.
  introv isp.
  allrw @isprog_eq.
  destruct isp as [cl wf].
  split; eauto 2 with slow;[].

  pose proof (unfold_abstractions_preserves_free_vars lib abs t) as h.
  rewrite cl in h.
  apply closed_iff.
  introv i; apply h in i; simpl in i; tcsp.
Qed.

Definition unfold_abstractions_c {o} lib abs (t : @CTerm o) : CTerm :=
  let (a,p) := t in
  exist isprog (unfold_abstractions lib abs a) (isprog_unfold_abstractions lib abs a p).

(*Lemma lsubst_aux_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o) s,
    cl_sub s
    -> lsubst_aux (unfold_abstractions lib abs t) s
       = unfold_abstractions lib abs (lsubst_aux t s).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv cls; simpl in *; tcsp.

  -
Qed.*)

(*Lemma lsubstc_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o) w s c (w' : wf_term t) (c' : cover_vars t s),
    lsubstc (unfold_abstractions lib abs t) w s c
    = unfold_abstractions_c lib abs (lsubstc t w' s c').
Proof.
  introv.
  apply cterm_eq; simpl.

Qed.*)

Lemma isprogram_lsubst_aux_implies_subvars_free_vars_dom_sub {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> isprogram (lsubst_aux t sub)
    -> subvars (free_vars t) (dom_sub sub).
Proof.
  introv cls isp; apply subvars_eq.
  destruct isp as [cl wf].
  introv i.

  pose proof (cl_lsubst_aux_trivial2 t sub) as q; autodimp q hyp.
  rw cl in q.
  symmetry in q.
  rw @nil_remove_nvars_iff in q.
  applydup q in i; auto.
Qed.
Hint Resolve isprogram_lsubst_aux_implies_subvars_free_vars_dom_sub : slow.

(* This improves [reduces_to_implies_approx_open] by only requiring
   the term to be well-formed and not necessarily closed *)
Lemma reduces_to_implies_approx_open2 {o} :
  forall lib (t x : @NTerm o),
    wf_term t
    -> reduces_to lib t x
    -> approx_open lib x t # approx_open lib t x.
Proof.
  introv wf r.
  applydup @reduces_to_preserves_wf in r; auto.

  dands; apply approx_open_simpler_equiv; unfold simpl_olift;
    dands; eauto 2 with slow; introv psub isp1 isp2.

  - repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
    rewrite cl_lsubst_lsubst_aux in isp1; eauto 2 with slow.
    rewrite cl_lsubst_lsubst_aux in isp2; eauto 2 with slow.

    pose proof (reduces_to_lsubst_aux lib t x sub) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.
    apply reduces_to_implies_approx in q1; auto; repnd.
    applydup @approx_relates_only_progs in q2; repnd.
    eapply approx_trans;[|eauto].
    eapply approx_alpha_rw_l_aux;[eauto|].
    apply approx_refl; auto.

  - repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
    rewrite cl_lsubst_lsubst_aux in isp1; eauto 2 with slow.
    rewrite cl_lsubst_lsubst_aux in isp2; eauto 2 with slow.

    pose proof (reduces_to_lsubst_aux lib t x sub) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.
    apply reduces_to_implies_approx in q1; auto; repnd.
    applydup @approx_relates_only_progs in q2; repnd.
    eapply approx_trans;[eauto|].
    eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;eauto|].
    apply approx_refl; auto.
Qed.

Lemma approx_star_preserves_reduces_to_left {o} :
  forall lib (a b c : @NTerm o),
    wf_term a
    -> reduces_to lib a b
    -> approx_star lib a c
    -> approx_star lib b c.
Proof.
  introv ispa r apr.
  allrw @approx_star_iff_approx_open.
  eapply approx_open_trans;[|eauto].
  apply reduces_to_implies_approx_open2 in r; tcsp.
Qed.

Lemma approx_star_preserves_reduces_to_right {o} :
  forall lib (a b c : @NTerm o),
    wf_term a
    -> reduces_to lib a b
    -> approx_star lib c a
    -> approx_star lib c b.
Proof.
  introv ispa r apr.
  allrw @approx_star_iff_approx_open.
  eapply approx_open_trans;[eauto|].
  apply reduces_to_implies_approx_open2 in r; tcsp.
Qed.

Lemma sub_find_nrut_sub_some_implies {o} :
  forall (sub : @Sub o) l t v,
    nrut_sub l sub
    -> sub_find sub v = Some t
    -> {a : get_patom_set o & t = mk_utoken a}.
Proof.
  induction sub; introv nrut sf; simpl in *; ginv.
  destruct a; simpl in *; boolvar; ginv; tcsp.

  - apply nrut_sub_cons in nrut; exrepnd; subst.
    eexists; eauto.

  - apply nrut_sub_cons in nrut; exrepnd; subst.
    eapply IHsub; eauto.
Qed.

Lemma matching_bterms_map_unfold_abstractions_b {o} :
  forall vars lib abs (bs : list (@BTerm o)),
    matching_bterms vars (map (unfold_abstractions_b lib abs) bs)
    <-> matching_bterms vars bs.
Proof.
  introv.
  unfold matching_bterms.
  allrw map_map; unfold compose.
  split; intro h; repnd; dands; auto; allrw; apply eq_maps;
    introv i; destruct x; unfold num_bvars; simpl; auto.
Qed.
Hint Rewrite @matching_bterms_map_unfold_abstractions_b : slow.

Lemma matching_entry_map_unfold_abstractions_b {o} :
  forall abs opabs vars lib' abs' (bs : list (@BTerm o)),
    matching_entry abs opabs vars (map (unfold_abstractions_b lib' abs') bs)
    <-> matching_entry abs opabs vars bs.
Proof.
  introv; unfold matching_entry.
  split; intro h; repnd; dands; autorewrite with slow in *; auto.
Qed.
Hint Rewrite @matching_entry_map_unfold_abstractions_b : slow.

Lemma find_entry_map_unfold_abstractions_b_eq {o} :
  forall lib abs (bs : list (@BTerm o)) lib' abs',
    find_entry lib abs (map (unfold_abstractions_b lib' abs') bs)
    = find_entry lib abs bs.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; boolvar; auto; allrw @not_matching_entry_iff;
    allrw @matching_entry_map_unfold_abstractions_b; tcsp.
  destruct n.
  allrw @matching_entry_map_unfold_abstractions_b; tcsp.
Qed.
Hint Rewrite @find_entry_map_unfold_abstractions_b_eq : slow.

Lemma matching_bterm_lsubst_bterms_aux {o} :
  forall vars (bs : list (@BTerm o)) sub,
    matching_bterms vars (lsubst_bterms_aux bs sub)
    <-> matching_bterms vars bs.
Proof.
  introv.
  unfold matching_bterms, lsubst_bterms_aux.
  allrw map_map; unfold compose.
  split; intro h; repnd; dands; auto; allrw; apply eq_maps;
    introv i; destruct x; unfold num_bvars; simpl; auto.
Qed.
Hint Rewrite @matching_bterm_lsubst_bterms_aux : slow.

Lemma matching_entry_lsubst_bterms_aux {o} :
  forall abs opabs vars sub (bs : list (@BTerm o)),
    matching_entry abs opabs vars (lsubst_bterms_aux bs sub)
    <-> matching_entry abs opabs vars bs.
Proof.
  introv; unfold matching_entry.
  split; intro h; repnd; dands; auto; autorewrite with slow in *; auto.
Qed.
Hint Rewrite @matching_entry_lsubst_bterms_aux : slow.

Lemma find_entry_lsubst_bterms_aux {o} :
  forall lib abs sub (bs : list (@BTerm o)),
    find_entry lib abs (lsubst_bterms_aux bs sub)
    = find_entry lib abs bs.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; boolvar; auto; allrw @not_matching_entry_iff;
    allrw @matching_entry_lsubst_bterms_aux; tcsp.
  destruct n.
  allrw @matching_entry_lsubst_bterms_aux; tcsp.
Qed.
Hint Rewrite @find_entry_lsubst_bterms_aux : slow.

Lemma alpha_eq_lsubst_mk_abs_subst2 {o} :
  forall rhs vars (bs1 bs2 : list (@BTerm o)),
    length vars = length bs1
    -> length vars = length bs2
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered rhs vars
    -> map num_bvars bs1 = map num_bvars bs2
    -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> alpha_eq_bterm b1 b2)
    -> alpha_eq (mk_instance vars bs1 rhs) (mk_instance vars bs2 rhs).
Proof.
  introv lbs1 lbs2 m1 m2 cov eqmaps imp.
  apply alphaeq_eq.
  apply mk_instance_alpha_congr; auto.

  unfold bin_rel_bterm.
  unfold binrel_list.
  applydup map_eq_length_eq in eqmaps; dands; auto.
  introv i.
  apply alphaeqbt_eq.
  apply imp.
  apply in_nth_combine; auto.
Qed.

Lemma length_lsubst_bterms_aux {o} :
  forall (bs : list (@BTerm o)) sub,
    length (lsubst_bterms_aux bs sub) = length bs.
Proof.
  introv; unfold lsubst_bterms_aux; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_lsubst_bterms_aux : slow.

Lemma matching_entry_implies_eq_lengths {o} :
  forall abs1 abs2 vars (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> length vars = length bs.
Proof.
  introv m; unfold matching_entry in m; repnd.
  unfold matching_bterms in m.
  match goal with
  | [ H : map ?a ?b = map ?c ?d |- _ ] =>
    assert (length (map a b) = length (map c d)) as q; allrw; auto
  end.
  autorewrite with slow in *; auto.
Qed.
Hint Resolve matching_entry_implies_eq_lengths : slow.

Hint Rewrite @fold_lsubst_bterms_aux : slow.

Lemma unfold_abs_map_unfold_abstractions_b_none_implies {o} :
  forall lib abs lib' abs' (bs : list (@BTerm o)),
    unfold_abs lib abs (map (unfold_abstractions_b lib' abs') bs) = None
    -> unfold_abs lib abs bs = None.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  remember (unfold_abs_entry a abs (map (unfold_abstractions_b lib' abs') bs)) as q.
  symmetry in Heqq; destruct q; ginv.
  apply IHlib in h; allrw.
  destruct a; simpl in *; boolvar; auto; ginv.
  allrw @not_matching_entry_iff.
  destruct n.
  autorewrite with slow in *; auto.
Qed.

Lemma implies_unfold_abs_map_unfold_abstractions_b_none {o} :
  forall lib abs lib' abs' (bs : list (@BTerm o)),
    unfold_abs lib abs bs = None
    -> unfold_abs lib abs (map (unfold_abstractions_b lib' abs') bs) = None.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  remember (unfold_abs_entry a abs bs) as q.
  symmetry in Heqq; destruct q; ginv.
  eapply IHlib in h.
  allrw.
  destruct a; simpl in *; boolvar; auto; ginv.
  allrw @not_matching_entry_iff.
  destruct n.
  autorewrite with slow in *; auto.
Qed.

Lemma implies_unfold_abs_lsubst_bterms_aux_none {o} :
  forall lib abs sub (bs : list (@BTerm o)),
    unfold_abs lib abs bs = None
    -> unfold_abs lib abs (lsubst_bterms_aux bs sub) = None.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  remember (unfold_abs_entry a abs bs) as q.
  symmetry in Heqq; destruct q; ginv.
  eapply IHlib in h.
  allrw.
  destruct a; simpl in *; boolvar; auto; ginv.
  allrw @not_matching_entry_iff.
  destruct n.
  autorewrite with slow in *; auto.
Qed.

Lemma lsubst_aux_nrut_sub_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o) sub l,
    nrut_sub l sub
    -> alpha_eq
         (lsubst_aux (unfold_abstractions lib abs t) sub)
         (unfold_abstractions lib abs (lsubst_aux t sub)).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv nrut; simpl in *; tcsp.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl in *; tcsp.
    eapply sub_find_nrut_sub_some_implies in Heqsf;[|eauto]; exrepnd; subst; simpl; tcsp.

  - Case "oterm".
    unfold maybe_unfold; simpl.
    dopid op as [can|ncan|exc|abs'] SCase; simpl in *; tcsp.

    + allrw map_map; unfold compose.
      apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a as [vs t]; simpl.
      apply alpha_eq_bterm_congr.
      eapply ind; eauto 2 with slow.

    + allrw map_map; unfold compose.
      apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a as [vs t]; simpl.
      apply alpha_eq_bterm_congr.
      eapply ind; eauto 2 with slow.

    + allrw map_map; unfold compose.
      apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a as [vs t]; simpl.
      apply alpha_eq_bterm_congr.
      eapply ind; eauto 2 with slow.

    + boolvar.

      * remember (unfold_abs lib abs' (map (unfold_abstractions_b lib abs) bs)) as u.
        symmetry in Hequ; destruct u.

        {
          apply unfold_abs_implies_find_entry in Hequ; exrepnd; subst.
          autorewrite with slow in *.
          erewrite find_entry_implies_unfold_abs;
            [|rewrite <- Hequ1; autorewrite with slow in *; auto].

          eapply alpha_eq_trans;
            [apply alpha_eq_sym;
             apply alpha_eq_lsubst_aux_mk_instance|];
            autorewrite with slow in *;
            eauto 3 with slow.

          apply alpha_eq_lsubst_mk_abs_subst2;
            autorewrite with slow in *; eauto 2 with slow.

          { unfold lsubst_bterms_aux; allrw map_map; unfold compose.
            apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

          introv i.
          unfold lsubst_bterms_aux in i.
          allrw map_map; unfold compose in i.
          rewrite <- map_combine in i.
          apply in_map_iff in i; exrepnd; ginv.
          apply in_combine_same in i1; repnd; subst.
          destruct a as [vs t]; simpl.
          apply alpha_eq_bterm_congr.
          eapply ind; eauto 2 with slow.
        }

        {
          apply unfold_abs_map_unfold_abstractions_b_none_implies in Hequ.
          rewrite implies_unfold_abs_map_unfold_abstractions_b_none;
            [|autorewrite with slow;rewrite implies_unfold_abs_lsubst_bterms_aux_none;auto].
          simpl.

          allrw map_map; unfold compose.
          apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
          introv i.
          rewrite <- map_combine in i.
          apply in_map_iff in i; exrepnd; ginv.
          apply in_combine_same in i1; repnd; subst.
          destruct a as [vs t]; simpl.
          apply alpha_eq_bterm_congr.
          eapply ind; eauto 2 with slow.
        }

      * simpl.
        allrw map_map; unfold compose.
        apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a as [vs t]; simpl.
        apply alpha_eq_bterm_congr.
        eapply ind; eauto 2 with slow.
Qed.

Lemma approx_star_unfold_abstractions_left {o} :
  forall lib abs (t : @NTerm o),
    nt_wf t
    -> approx_star lib (unfold_abstractions lib abs t) t.
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv wf; simpl; auto;
    try (complete (apply approx_star_refl; auto)).

  Case "oterm".

  allrw @nt_wf_oterm_iff; repnd.

  unfold maybe_unfold; simpl.
  destruct op; simpl in *.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).

    destruct (@dec_op_eq_fresh o (NCan n)) as [d|d]; ginv.

    + right.
      pose proof (exists_nrut_sub l (get_utokens (unfold_abstractions lib abs t) ++ get_utokens t)) as q.
      exrepnd.
      exists sub; dands; auto.
      repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).

      eapply approx_star_alpha_fun_l;
        [|apply alpha_eq_sym;eapply lsubst_aux_nrut_sub_unfold_abstractions;eauto].

      applydup wf in i0.
      allrw @bt_wf_iff.

      eapply ind; eauto 2 with slow.

      { rewrite simple_osize_lsubst_aux; eauto 2 with slow. }

      { apply implies_wf_lsubst_aux; eauto 2 with slow. }

    + left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto with slow.

  - rename o0 into a.
    boolvar.

    + remember (unfold_abs lib a (map (unfold_abstractions_b lib abs) bs)) as ua.
      symmetry in Hequa; destruct ua.

      * apply (approx_star_preserves_reduces_to_left
                 _ (oterm (Abs a) (map (unfold_abstractions_b lib abs) bs)));
          [|apply reduces_to_if_step; csunf; simpl; unfold compute_step_lib; allrw; auto|].

        {
          apply wf_term_eq.
          apply nt_wf_oterm_iff.
          allrw map_map; unfold compose; simpl.
          allrw <- .
          dands.

          - apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

          - introv i; allrw in_map_iff; exrepnd; subst.
            destruct a0 as [vs t].
            applydup wf in i1.
            allrw @bt_wf_iff; eauto 2 with slow.
        }

        econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_left in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto with slow.

      * econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_left in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto with slow.

    + econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
      apply lblift_sub_eq; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine_left in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a0 as [vs t]; simpl in *.
      eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
      left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto with slow.
Qed.

Lemma lblift_sub_approx_star_refl {o} :
  forall op lib (bs : list (@BTerm o)),
    (forall b, LIn b bs -> bt_wf b)
    -> lblift_sub op (approx_star lib) bs bs.
Proof.
  introv imp.
  apply lblift_sub_eq; dands; auto.
  introv i.
  apply in_combine_same in i; repnd; subst.
  unfold blift_sub.
  destruct b2 as [l t].
  applydup imp in i0.
  allrw @bt_wf_iff.

  eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
  destruct (dec_op_eq_fresh op) as [d|d]; subst; tcsp.

  - right.
    pose proof (exists_nrut_sub l (get_utokens t ++ get_utokens t)) as q.
    exrepnd.
    exists sub; dands; auto.
    apply approx_star_refl.
    rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[].
    apply implies_wf_lsubst_aux; eauto 2 with slow.

  - left; dands; tcsp; try (intro xx; inversion xx).
    apply approx_star_refl; eauto 2 with slow.
Qed.

Lemma map_combine_right :
  forall {T1 T2 T3} (f : T2 -> T3) (l1 : list T1) (l2 : list T2),
    map (fun x => (fst x, f (snd x))) (combine l1 l2)
    = combine l1 (map f l2).
Proof.
  induction l1; introv; allsimpl; auto.
  destruct l2; allsimpl; auto.
  rw IHl1; auto.
Qed.

Lemma approx_star_unfold_abstractions_right {o} :
  forall lib abs (t : @NTerm o),
    nt_wf t
    -> approx_star lib t (unfold_abstractions lib abs t).
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv wf; simpl; auto;
    try (complete (apply approx_star_refl; auto)).

  Case "oterm".

  allrw @nt_wf_oterm_iff; repnd.

  unfold maybe_unfold; simpl.
  destruct op; simpl in *.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).

    destruct (@dec_op_eq_fresh o (NCan n)) as [d|d]; ginv.

    + right.
      pose proof (exists_nrut_sub l (get_utokens t ++ get_utokens (unfold_abstractions lib abs t))) as q.
      exrepnd.
      exists sub; dands; auto.
      repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).

      eapply approx_star_alpha_fun_r;
        [|apply alpha_eq_sym;eapply lsubst_aux_nrut_sub_unfold_abstractions;eauto].

      applydup wf in i0.
      allrw @bt_wf_iff.

      eapply ind; eauto 2 with slow.

      { rewrite simple_osize_lsubst_aux; eauto 2 with slow. }

      { apply implies_wf_lsubst_aux; eauto 2 with slow. }

    + left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - rename o0 into a.
    boolvar.

    + remember (unfold_abs lib a (map (unfold_abstractions_b lib abs) bs)) as ua.
      symmetry in Hequa; destruct ua.

      * apply (approx_star_preserves_reduces_to_right
                 _ (oterm (Abs a) (map (unfold_abstractions_b lib abs) bs)));
          [|apply reduces_to_if_step; csunf; simpl; unfold compute_step_lib; allrw; auto|].

        {
          apply wf_term_eq.
          apply nt_wf_oterm_iff.
          allrw map_map; unfold compose; simpl.
          allrw <- .
          dands.

          - apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

          - introv i; allrw in_map_iff; exrepnd; subst.
            destruct a0 as [vs t].
            applydup wf in i1.
            allrw @bt_wf_iff; eauto 2 with slow.
        }

        econstructor; autorewrite with slow;[| |apply approx_open_refl];
          autorewrite with slow; auto;
            [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
              [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
              |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [vs t]; simpl;
               applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
            ].

        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_right in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto 2 with slow.

      * econstructor; autorewrite with slow;[| |apply approx_open_refl];
          autorewrite with slow; auto;
            [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
              [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
              |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [vs t]; simpl;
               applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
            ].

        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_right in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto 2 with slow.

    + econstructor; autorewrite with slow;[| |apply approx_open_refl];
        autorewrite with slow; auto;
          [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
            [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
            |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [l t]; simpl;
             applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
          ].

      apply lblift_sub_eq; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine_right in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a0 as [l t]; simpl in *.
      eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
      left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.
Qed.

Lemma cequivc_lsubstc_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o) s w' c' w c,
    cequivc lib (lsubstc (unfold_abstractions lib abs t) w' s c') (lsubstc t w s c).
Proof.
  introv.
  unfold cequivc; simpl.
  apply lsubst_cequiv_congr; eauto 2 with slow.

  - apply olift_approx_cequiv; apply approx_star_implies_approx_open.

    + apply approx_star_unfold_abstractions_left; eauto 2 with slow.

    + apply approx_star_unfold_abstractions_right; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.
Qed.
Hint Resolve cequivc_lsubstc_unfold_abstractions : slow.

Lemma implies_covered_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o) l,
    covered t l
    -> covered (unfold_abstractions lib abs t) l.
Proof.
  introv cov; unfold covered in *; allrw subvars_eq.
  introv i.
  apply unfold_abstractions_preserves_free_vars in i; apply cov in i; auto.
Qed.
Hint Resolve implies_covered_unfold_abstractions : slow.


Lemma approx_star_unfold_abstractions_left_ext {o} :
  forall lib1 lib2 abs (t : @NTerm o),
    nt_wf t
    -> lib_extends lib2 lib1
    -> approx_star lib2 (unfold_abstractions lib1 abs t) t.
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv wf ext; simpl; auto;
    try (complete (apply approx_star_refl; auto)).

  Case "oterm".

  allrw @nt_wf_oterm_iff; repnd.

  unfold maybe_unfold; simpl.
  destruct op; simpl in *.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).

    destruct (@dec_op_eq_fresh o (NCan n)) as [d|d]; ginv.

    + right.
      pose proof (exists_nrut_sub l (get_utokens (unfold_abstractions lib1 abs t) ++ get_utokens t)) as q.
      exrepnd.
      exists sub; dands; auto.
      repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).

      eapply approx_star_alpha_fun_l;
        [|apply alpha_eq_sym;eapply lsubst_aux_nrut_sub_unfold_abstractions;eauto].

      applydup wf in i0.
      allrw @bt_wf_iff.

      eapply ind; eauto 2 with slow.

      { rewrite simple_osize_lsubst_aux; eauto 2 with slow. }

      { apply implies_wf_lsubst_aux; eauto 2 with slow. }

    + left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_left in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto with slow.

  - rename o0 into a.
    boolvar.

    + remember (unfold_abs lib1 a (map (unfold_abstractions_b lib1 abs) bs)) as ua.
      symmetry in Hequa; destruct ua.

      * pose proof (reduces_to_if_step
                      lib1
                      (oterm (Abs a) (map (unfold_abstractions_b lib1 abs) bs))
                      n) as q.
        autodimp q hyp.

        { csunf; simpl; unfold compute_step_lib; allrw; auto. }

        eapply reduces_to_preserves_lib_extends in q;[|eauto].

        eapply approx_star_preserves_reduces_to_left;[|eauto|].

        {
          apply wf_term_eq.
          apply nt_wf_oterm_iff.
          allrw map_map; unfold compose; simpl.
          allrw <- .
          dands.

          - apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

          - introv i; allrw in_map_iff; exrepnd; subst.
            destruct a0 as [vs t].
            applydup wf in i1.
            allrw @bt_wf_iff; eauto 2 with slow.
        }

        econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_left in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto with slow.

      * econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_left in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto with slow.

    + econstructor; autorewrite with slow;[| |apply approx_open_refl]; auto.
      apply lblift_sub_eq; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine_left in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a0 as [vs t]; simpl in *.
      eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
      left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto with slow.
Qed.

Lemma approx_star_unfold_abstractions_right_ext {o} :
  forall lib1 lib2 abs (t : @NTerm o),
    nt_wf t
    -> lib_extends lib2 lib1
    -> approx_star lib2 t (unfold_abstractions lib1 abs t).
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv wf ext; simpl; auto;
    try (complete (apply approx_star_refl; auto)).

  Case "oterm".

  allrw @nt_wf_oterm_iff; repnd.

  unfold maybe_unfold; simpl.
  destruct op; simpl in *.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).

    destruct (@dec_op_eq_fresh o (NCan n)) as [d|d]; ginv.

    + right.
      pose proof (exists_nrut_sub l (get_utokens t ++ get_utokens (unfold_abstractions lib1 abs t))) as q.
      exrepnd.
      exists sub; dands; auto.
      repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).

      eapply approx_star_alpha_fun_r;
        [|apply alpha_eq_sym;eapply lsubst_aux_nrut_sub_unfold_abstractions;eauto].

      applydup wf in i0.
      allrw @bt_wf_iff.

      eapply ind; eauto 2 with slow.

      { rewrite simple_osize_lsubst_aux; eauto 2 with slow. }

      { apply implies_wf_lsubst_aux; eauto 2 with slow. }

    + left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.

  - econstructor; autorewrite with slow;[| |apply approx_open_refl];
      autorewrite with slow; auto;
        [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
          [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
          |introv i; apply in_map_iff in i; exrepnd; subst; destruct a as [l t]; simpl;
           applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
        ].

    apply lblift_sub_eq; autorewrite with slow; dands; auto.
    introv i.
    rewrite <- map_combine_right in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; simpl in *.
    eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
    left; dands; tcsp; try (intro xx; inversion xx).
    applydup wf in i0.
    allrw @bt_wf_iff.
    eapply ind; eauto 2 with slow.

  - rename o0 into a.
    boolvar.

    + remember (unfold_abs lib1 a (map (unfold_abstractions_b lib1 abs) bs)) as ua.
      symmetry in Hequa; destruct ua.

      * pose proof (reduces_to_if_step
                      lib1
                      (oterm (Abs a) (map (unfold_abstractions_b lib1 abs) bs))
                      n) as q.
        autodimp q hyp.

        { csunf; simpl; unfold compute_step_lib; allrw; auto. }

        eapply reduces_to_preserves_lib_extends in q;[|eauto].

        eapply approx_star_preserves_reduces_to_right;[|eauto|].

        {
          apply wf_term_eq.
          apply nt_wf_oterm_iff.
          allrw map_map; unfold compose; simpl.
          allrw <- .
          dands.

          - apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

          - introv i; allrw in_map_iff; exrepnd; subst.
            destruct a0 as [vs t].
            applydup wf in i1.
            allrw @bt_wf_iff; eauto 2 with slow.
        }

        econstructor; autorewrite with slow;[| |apply approx_open_refl];
          autorewrite with slow; auto;
            [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
              [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
              |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [vs t]; simpl;
               applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
            ].

        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_right in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto 2 with slow.

      * econstructor; autorewrite with slow;[| |apply approx_open_refl];
          autorewrite with slow; auto;
            [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
              [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
              |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [vs t]; simpl;
               applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
            ].

        apply lblift_sub_eq; autorewrite with slow; dands; auto.
        introv i.
        rewrite <- map_combine_right in i.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        destruct a0 as [vs t]; simpl in *.
        eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
        left; dands; tcsp; try (intro xx; inversion xx).
        applydup wf in i0.
        allrw @bt_wf_iff.
        eapply ind; eauto 2 with slow.

    + econstructor; autorewrite with slow;[| |apply approx_open_refl];
        autorewrite with slow; auto;
          [|apply nt_wf_oterm_iff; allrw map_map; unfold compose; simpl; allrw <-;dands;
            [apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto
            |introv i; apply in_map_iff in i; exrepnd; subst; destruct a0 as [l t]; simpl;
             applydup wf in i1; allrw @bt_wf_iff; eauto 2 with slow]
          ].

      apply lblift_sub_eq; autorewrite with slow; dands; auto.
      introv i.
      rewrite <- map_combine_right in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      destruct a0 as [l t]; simpl in *.
      eexists; eexists; eexists; dands; try (apply alphaeqbt_refl).
      left; dands; tcsp; try (intro xx; inversion xx).
      applydup wf in i0.
      allrw @bt_wf_iff.
      eapply ind; eauto 2 with slow.
Qed.

Lemma cequivc_lsubstc_unfold_abstractions_ext {o} :
  forall lib1 lib2 abs (t : @NTerm o) s w' c' w c,
    lib_extends lib2 lib1
    -> cequivc lib2 (lsubstc (unfold_abstractions lib1 abs t) w' s c') (lsubstc t w s c).
Proof.
  introv ext.
  unfold cequivc; simpl.
  apply lsubst_cequiv_congr; eauto 2 with slow.

  - apply olift_approx_cequiv; apply approx_star_implies_approx_open.

    + apply approx_star_unfold_abstractions_left_ext; eauto 2 with slow.

    + apply approx_star_unfold_abstractions_right_ext; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.
Qed.
Hint Resolve cequivc_lsubstc_unfold_abstractions_ext : slow.




(**

<<
   H |- a ext e

     By unfoldAbstractionsConcl abs

     H |- (unfold_abstractions lib abs a) ext e
>>
 *)

Definition rule_unfold_abstractions_concl {o} a e (H : @bhyps o) :=
  mk_baresequent H (mk_concl a e).

Definition rule_unfold_abstractions_hyp {o} lib abs a e (H : @bhyps o) :=
  mk_baresequent H (mk_concl (unfold_abstractions lib abs a) e).

Definition rule_unfold_abstractions {o}
           (lib : library)
           (abs : list opname)
           (a e : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_unfold_abstractions_concl a e H)
    [rule_unfold_abstractions_hyp lib abs a e H]
    [].

Lemma rule_unfold_abstractions_true3 {o} :
  forall lib abs (a e : NTerm) (H : @barehypotheses o),
    rule_true3 lib (rule_unfold_abstractions lib abs a e H).
Proof.
  unfold rule_unfold_abstractions, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_unfold_abstractions_concl a e H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2 eqh sim) as q; clear hyp1.
  exrepnd.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact q0] ];
      eauto 2 with slow.

  - eapply cequivc_preserving_equality; try (exact q1); eauto 2 with slow.
Qed.

Lemma rule_unfold_abstractions_wf2 {o} :
  forall lib abs (a e : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_unfold_abstractions lib abs a e H).
Proof.
  introv wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
    allrw <- @wf_approx_iff; repnd; auto;
      allrw @covered_approx; repnd; auto; eauto 4 with slow.
Qed.

Lemma rule_unfold_abstractions_true_ext_lib {o} :
  forall lib abs
         (a e : NTerm)
         (H : @barehypotheses o),
    rule_true_ext_lib lib (rule_unfold_abstractions lib abs a e H).
Proof.
  unfold rule_unfold_abstractions, rule_true_ext_lib, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  introv wf cargs hyps.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_unfold_abstractions_concl a e H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  seq_true_ext_lib.
  seq_true_ext_lib in hyp1.

  pose proof (hyp1 lib0 s1 s2 extlib eqh sim) as q; clear hyp1.
  exrepnd.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact q0] ];
      eauto 2 with slow.

  - eapply cequivc_preserving_equality; try (exact q1); eauto 2 with slow.
Qed.

Lemma lib_extends_trans {o} :
  forall (lib1 lib2 lib3 : @library o),
    lib_extends lib1 lib2
    -> lib_extends lib2 lib3
    -> lib_extends lib1 lib3.
Proof.
  introv ext1 ext2 i.
  apply ext2 in i; tcsp.
Qed.
Hint Resolve lib_extends_trans : slow.

Lemma rule_unfold_abstractions_ext_true_ext_lib {o} :
  forall lib1 lib2 abs
         (a e : NTerm)
         (H : @barehypotheses o)
         (ext : lib_extends lib2 lib1),
    rule_true_ext_lib lib2 (rule_unfold_abstractions lib1 abs a e H).
Proof.
  unfold rule_unfold_abstractions, rule_true_ext_lib, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  introv ext wf cargs hyps.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_unfold_abstractions_concl a e H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  seq_true_ext_lib.
  seq_true_ext_lib in hyp1.

  pose proof (hyp1 lib s1 s2 extlib eqh sim) as q; clear hyp1.
  exrepnd.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact q0] ];
      eauto 3 with slow.

  - eapply cequivc_preserving_equality; try (exact q1); eauto 3 with slow.
Qed.

(*Fixpoint find_opname {o} lib abs : option (@library_entry o) :=
  match lib with
  | [] => None
  | (lib_abs oa vars rhs correct as entry) :: l =>
    if String.string_dec abs (opabs_name oa)
    then Some entry
    else find_opname l abs
  end.

Fixpoint select_library {o} (lib : @library o) (abs : list opname) : library :=
  match abs with
  | [] => []
  | x :: xs =>
    match find_opname lib x with
    | Some entry => entry :: select_library lib xs
    | None => select_library lib xs
    end
  end.*)



(**

<<
   H |- (unfold_abstractions lib abs b) ext e

     By unfoldAbstractionsConcl abs

     H |- b ext e
>>
 *)

Definition rule_rev_unfold_abstractions {o}
           lib abs
           (a e : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_unfold_abstractions_hyp lib abs a e H)
    [rule_unfold_abstractions_concl a e H]
    [].

Lemma rule_rev_unfold_abstractions_true3 {o} :
  forall lib abs (a e : NTerm) (H : @barehypotheses o),
    rule_true3 lib (rule_rev_unfold_abstractions lib abs a e H).
Proof.
  unfold rule_rev_unfold_abstractions, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_unfold_abstractions_hyp lib abs a e H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2 eqh sim) as q; clear hyp1.
  exrepnd.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact q0] ];
      apply cequivc_sym; eauto 3 with slow.

  - eapply cequivc_preserving_equality; try (exact q1);
      apply cequivc_sym; eauto 2 with slow.
Qed.

Lemma rule_rev_unfold_abstractions_wf2 {o} :
  forall lib abs (a e : NTerm) (H : @barehypotheses o),
    wf_term a
    -> covered a (vars_hyps H)
    -> wf_rule2 (rule_rev_unfold_abstractions lib abs a e H).
Proof.
  introv wfa cova wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq.
Qed.

Lemma rule_rev_unfold_abstractions_true_ext_lib {o} :
  forall lib abs
         (a e : NTerm)
         (H : @barehypotheses o),
    rule_true_ext_lib lib (rule_rev_unfold_abstractions lib abs a e H).
Proof.
  unfold rule_rev_unfold_abstractions, rule_true_ext_lib, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  introv wf cargs hyps.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_unfold_abstractions_hyp lib abs a e H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  seq_true_ext_lib.
  seq_true_ext_lib in hyp1.

  pose proof (hyp1 lib0 s1 s2 extlib eqh sim) as q; clear hyp1.
  exrepnd.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;[|exact q0] ];
      apply cequivc_sym;
      eauto 2 with slow.

  - eapply cequivc_preserving_equality; try (exact q1);
      apply cequivc_sym; eauto 2 with slow.
Qed.
