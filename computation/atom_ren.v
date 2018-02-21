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

  Authors: Vincent Rahli

*)


Require Export computation5.
Require Export computation_preserve5.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(* !! MOVE *)
Hint Resolve blift_alpha_fun_r : slow.
Hint Resolve sub_find_some_none_contra : slow.
Hint Unfold le_bin_rel indep_bin_rel : slow.
Hint Unfold wf_sub sub_range_sat : slow.
Hint Resolve subvars_disjoint_r : slow.
Hint Resolve subvars_disjoint_l : slow.
Hint Resolve subset_sub_free_vars_sub_filter : slow.
Hint Resolve subset_disjoint_r : slow.
Hint Resolve disjoint_remove_nvars : slow.

Lemma dec_op_eq_fresh {o} :
  forall (op : @Opid o),
    decidable (op = NCan NFresh).
Proof.
  introv; unfold decidable.
  destruct op; try (complete (right; sp; ginv)).
  destruct n; tcsp; try (complete (right; sp; ginv)).
Qed.

Definition isutoken {o} (t : @NTerm o) :=
  {a : get_patom_set o & t = mk_utoken a}.

Lemma isutoken_implies_closed {o} :
  forall (t : @NTerm o),
    isutoken t -> closed t.
Proof.
  introv i.
  unfold isutoken in i; exrepnd; subst; eauto with slow.
Qed.
Hint Resolve isutoken_implies_closed : slow.

Lemma isutoken_implies_nt_wf {o} :
  forall (t : @NTerm o),
    isutoken t -> nt_wf t.
Proof.
  introv i.
  unfold isutoken in i; exrepnd; subst; eauto with slow.
Qed.
Hint Resolve isutoken_implies_nt_wf : slow.

Definition ut_sub {o} (sub : @Sub o) := sub_range_sat sub isutoken.

Lemma ut_sub_nil {o} : @ut_sub o [].
Proof.
  introv; simpl; sp.
Qed.
Hint Resolve ut_sub_nil : slow.

Lemma ut_sub_cons {o} :
  forall v t (s : @Sub o),
    ut_sub ((v,t) :: s) <=> (isutoken t # ut_sub s).
Proof.
  introv; unfold ut_sub, sub_range_sat; simpl; split; intro k; repnd; dands; tcsp.
  - eapply k; eauto.
  - introv i; eapply k; eauto.
  - introv i; repndors; cpx; auto.
    eapply k; eauto.
Qed.

Lemma implies_ut_sub_cons {o} :
  forall v t (s : @Sub o),
    isutoken t
    -> ut_sub s
    -> ut_sub ((v,t) :: s).
Proof.
  introv i u.
  apply ut_sub_cons; auto.
Qed.
Hint Resolve implies_ut_sub_cons : slow.

Lemma ut_sub_implies_cl_sub {o} :
  forall (s : @Sub o),
    ut_sub s -> cl_sub s.
Proof.
  introv ut.
  unfold ut_sub in ut; unfold cl_sub.
  eapply sub_range_sat_implies;[|exact ut].
  introv i; eauto with slow.
Qed.
Hint Resolve ut_sub_implies_cl_sub : slow.

Lemma ut_sub_implies_wf_sub {o} :
  forall (s : @Sub o),
    ut_sub s -> wf_sub s.
Proof.
  introv ut.
  unfold ut_sub in ut; unfold wf_sub.
  eapply sub_range_sat_implies;[|exact ut].
  introv i; eauto with slow.
Qed.
Hint Resolve ut_sub_implies_wf_sub : slow.

Lemma ut_sub_implies_shallow_sub {o} :
  forall (s : @Sub o),
    ut_sub s -> shallow_sub s.
Proof.
  introv ut.
  unfold ut_sub in ut; unfold shallow_sub.
  unfold sub_range_sat in ut; introv i.
  apply in_range_iff in i; exrepnd.
  apply ut in i0.
  unfold isutoken in i0; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve ut_sub_implies_shallow_sub : slow.

Lemma prog_sub_nil {o} : @prog_sub o [].
Proof.
  unfold prog_sub, sub_range_sat; simpl; sp.
Qed.
Hint Resolve prog_sub_nil : slow.

Lemma ut_sub_implies_prog_sub {o} :
  forall (sub : @Sub o),
    ut_sub sub -> prog_sub sub.
Proof.
  induction sub; introv nrut; eauto with slow.
  destruct a.
  apply ut_sub_cons in nrut; exrepnd; subst.
  allunfold @isutoken; exrepnd; subst.
  apply prog_sub_cons; dands; eauto 2 with slow.
Qed.
Hint Resolve ut_sub_implies_prog_sub : slow.

Lemma nr_ut_sub_implies_wf_sub {o} :
  forall (sub : @Sub o) t,
    nr_ut_sub t sub -> wf_sub sub.
Proof.
  induction sub; introv nrut; eauto with slow.
Qed.
Hint Resolve nr_ut_sub_implies_wf_sub : slow.

Lemma nr_ut_sub_implies_prog_sub {o} :
  forall (sub : @Sub o) t,
    nr_ut_sub t sub -> prog_sub sub.
Proof.
  induction sub; introv nrut; eauto with slow.
  destruct a.
  apply nr_ut_sub_cons_iff in nrut; exrepnd; subst.
  apply prog_sub_cons; dands; eauto 2 with slow.
Qed.
Hint Resolve nr_ut_sub_implies_prog_sub : slow.

Lemma ut_sub_sub_find_some {o} :
  forall (sub : @Sub o) v t,
    ut_sub sub
    -> sub_find sub v = Some t
    -> isutoken t.
Proof.
  induction sub; introv ut sf; allsimpl; ginv.
  destruct a; boolvar; ginv; allrw @ut_sub_cons; repnd; auto.
  eapply IHsub; eauto.
Qed.

Definition nrut_sub {o} (l : list (@get_patom_set o)) (sub : @Sub o) :=
  ut_sub sub
  # no_repeats (get_utokens_sub sub)
  # disjoint l (get_utokens_sub sub).

Lemma nrut_sub_nil {o} :
  forall l, @nrut_sub o l [].
Proof.
  introv.
  unfold nrut_sub; unfold get_utokens_sub; simpl; dands; eauto with slow.
Qed.
Hint Resolve nrut_sub_nil : slow.

Lemma nrut_sub_implies_cl_sub {o} :
  forall l (s : @Sub o),
    nrut_sub l s -> cl_sub s.
Proof.
  introv ut.
  unfold nrut_sub in ut; repnd; eauto with slow.
Qed.
Hint Resolve nrut_sub_implies_cl_sub : slow.

Lemma nrut_sub_implies_wf_sub {o} :
  forall l (s : @Sub o),
    nrut_sub l s -> wf_sub s.
Proof.
  introv ut.
  unfold nrut_sub in ut; repnd; eauto with slow.
Qed.
Hint Resolve nrut_sub_implies_wf_sub : slow.

Lemma nrut_sub_implies_shallow_sub {o} :
  forall l (s : @Sub o),
    nrut_sub l s -> shallow_sub s.
Proof.
  introv ut.
  unfold nrut_sub in ut; repnd; eauto with slow.
Qed.
Hint Resolve nrut_sub_implies_shallow_sub : slow.

Lemma nrut_sub_implies_prog_sub {o} :
  forall l (s : @Sub o),
    nrut_sub l s -> prog_sub s.
Proof.
  introv ut.
  unfold nrut_sub in ut; repnd; eauto with slow.
Qed.
Hint Resolve nrut_sub_implies_prog_sub : slow.

Lemma nrut_sub_cons {o} :
  forall l v t (sub : @Sub o),
    nrut_sub l ((v,t) :: sub)
    <=>
    {a : get_patom_set o
     & t = mk_utoken a
     # !LIn a (get_utokens_sub sub)
     # !LIn a l
     # nrut_sub l sub}.
Proof.
  introv.
  unfold nrut_sub; simpl.
  rw @ut_sub_cons.
  unfold get_utokens_sub; simpl.
  fold (get_utokens_sub sub).
  rw no_repeats_app.
  rw disjoint_app_r.
  split; intro k; exrepnd.

  - allunfold @isutoken; exrepnd; subst.
    allsimpl; allrw disjoint_singleton_l.
    allrw disjoint_singleton_r.
    eexists; dands; eauto.

  - subst; allsimpl.
    allrw disjoint_singleton_r; allrw disjoint_singleton_l.
    dands; auto.
    eexists; eauto.
Qed.

Lemma nrut_sub_sub_filter {o} :
  forall (sub : @Sub o) l vs,
    nrut_sub l sub
    -> nrut_sub l (sub_filter sub vs).
Proof.
  induction sub; introv nrut; allsimpl; auto.
  destruct a as [v t]; allsimpl.
  boolvar; allrw @nrut_sub_cons; exrepnd; subst; auto.
  eexists; dands; eauto.
  intro k.
  apply get_utokens_sub_filter_subset in k; sp.
Qed.
Hint Resolve nrut_sub_sub_filter : slow.

Lemma in_nrut_sub {o} :
  forall (s : @Sub o) v t l,
    LIn (v,t) s
    -> nrut_sub l s
    -> {a : get_patom_set o
        & t = mk_utoken a
        # !LIn a l}.
Proof.
  induction s; introv i nr; allsimpl; tcsp.
  destruct a; allrw @nrut_sub_cons; exrepnd.
  repndors; cpx; subst; tcsp.
  - eexists; dands; eauto.
  - eapply IHs; eauto.
Qed.

Lemma bound_vars_lsubst_aux_nrut_sub {o} :
  forall (t : @NTerm o) (sub : Sub) l,
  nrut_sub l sub
  -> bound_vars (lsubst_aux t sub) = bound_vars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv nrut; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.
    apply sub_find_some in Heqsf.
    eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst; simpl; auto.

  - Case "oterm".
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x as [vs t]; allsimpl.
    apply app_if; auto.
    apply (ind t vs i (sub_filter sub vs) l).
    eauto with slow.
Qed.

Definition utok_ren {o} := list (get_patom_set o # get_patom_set o).

Fixpoint utok_ren_find {o} (ren : @utok_ren o) (a : get_patom_set o) : option (get_patom_set o) :=
  match ren with
    | nil => None
    | (a1,a2) :: xs =>
      if get_patom_deq o a a1
      then Some a2
      else utok_ren_find xs a
  end.

Definition ren_atom {o} (ren : @utok_ren o) a :=
  match utok_ren_find ren a with
    | Some b => b
    | None => a
  end.

Definition ren_utok_op {o} (ren : utok_ren) (op : @Opid o) : Opid :=
  match op with
    | Can (NUTok a) => Can (NUTok (ren_atom ren a))
    | _ => op
  end.

Fixpoint ren_utokens {o} (ren : utok_ren) (t : @NTerm o) : NTerm :=
  match t with
    | vterm v => t
    | sterm f => sterm f
    | oterm op bs => oterm (ren_utok_op ren op) (map (ren_utokens_b ren) bs)
  end
with ren_utokens_b {o} (ren : utok_ren) (b : @BTerm o) : BTerm :=
       match b with
         | bterm vs t => bterm vs (ren_utokens ren t)
       end.

Fixpoint nrut_subs_to_utok_ren {o} (sub1 sub2 : @Sub o) : utok_ren :=
  match sub1, sub2 with
    | [], [] => []
    | ((_,oterm (Can (NUTok a1)) _) :: s1), ((_,oterm (Can (NUTok a2)) _) :: s2) =>
      (a1,a2) :: nrut_subs_to_utok_ren s1 s2
    | _, _ => []
  end.

Definition ren_utokens_sub {o} (ren : utok_ren) (sub : @Sub o) : Sub :=
  map (fun x => match x with | (v,t) => (v,ren_utokens ren t) end) sub.

Ltac assertdimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      let h := fresh hyp in
      assert T1 as h;
        [ clear H; try (complete auto)
        | let XX := fresh "XX" in
          pose proof (H h) as XX;
            clear H;
            rename XX into H;
            try (complete auto)
        ]
  end.

Lemma nt_wf_ren_utokens {o} :
  forall ren (t : @NTerm o),
    nt_wf t
    -> nt_wf (ren_utokens ren t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; allsimpl; auto.
  Case "oterm".
  allrw @nt_wf_oterm_iff; repnd; dands; auto.

  - allrw map_map; unfold compose.
    destruct op; allsimpl;
    try (complete (rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto)).
    destruct c; allsimpl;
    try (complete (rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto)).

  - introv i; allrw in_map_iff; exrepnd; subst.
    destruct a as [l t]; allsimpl.
    constructor.
    eapply ind; eauto.
    apply wf in i1; inversion i1; subst; auto.
Qed.
Hint Resolve nt_wf_ren_utokens : slow.

Lemma free_vars_ren_utokens {o} :
  forall ren (t : @NTerm o),
    free_vars (ren_utokens ren t) = free_vars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; allsimpl; auto.
  Case "oterm".
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  f_equal.
  eapply ind; eauto.
Qed.

Lemma isprogram_ren_utokens {o} :
  forall ren (t : @NTerm o),
    isprogram t
    -> isprogram (ren_utokens ren t).
Proof.
  introv isp.
  allunfold @isprogram; allunfold @closed.
  rw @free_vars_ren_utokens.
  repnd; dands; eauto with slow.
Qed.
Hint Resolve isprogram_ren_utokens : slow.

Lemma prog_sub_ren_utokens_sub {o} :
  forall ren (sub : @Sub o),
    prog_sub sub
    -> prog_sub (ren_utokens_sub ren sub).
Proof.
  induction sub; introv p; allsimpl; auto.
  destruct a as [v t].
  allrw @prog_sub_cons; repnd; dands; tcsp; eauto with slow.
Qed.
Hint Resolve prog_sub_ren_utokens_sub : slow.

Lemma dom_sub_ren_utokens_sub {o} :
  forall ren (sub : @Sub o),
    dom_sub (ren_utokens_sub ren sub) = dom_sub sub.
Proof.
  induction sub; allsimpl; auto.
  destruct a as [l t]; allsimpl.
  f_equal; auto.
Qed.

Lemma free_vars_cl_lsubst {o} :
  forall (t : @NTerm o) (sub : Sub),
    cl_sub sub
    -> free_vars (lsubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  introv cl; unflsubst.
  apply free_vars_lsubst_aux_cl; auto.
Qed.

Lemma sub_keep_first_ren_utokens_sub {o} :
  forall ren (sub : @Sub o) vs,
    sub_keep_first (ren_utokens_sub ren sub) vs
    = ren_utokens_sub ren (sub_keep_first sub vs).
Proof.
  induction sub; introv; simpl; auto.
  destruct a as [l t]; simpl; boolvar; auto.
  simpl; f_equal; tcsp.
Qed.

Lemma sub_free_vars_ren_utokens_sub {o} :
  forall ren (sub : @Sub o),
    sub_free_vars (ren_utokens_sub ren sub) = sub_free_vars sub.
Proof.
  induction sub; introv; simpl; auto.
  destruct a as [l t]; simpl.
  rw @free_vars_ren_utokens; f_equal; auto.
Qed.

Hint Resolve no_utokens_implies_get_utokens_so_nil : slow.

Lemma no_utokens_lib {o} :
  forall (lib : @library o),
    get_utokens_library lib =  [].
Proof.
  induction lib; simpl; auto.
  rw IHlib; rw app_nil_r.
  destruct a; simpl.
  unfold correct_abs in correct; repnd; eauto 3 with slow.
Qed.

Lemma nrut_sub_cons_l {o} :
  forall a l (sub : @Sub o),
    !LIn a (get_utokens_sub sub)
    -> !LIn a l
    -> nrut_sub l sub
    -> nrut_sub (a :: l) sub.
Proof.
  induction sub as [|x sub]; introv ni1 ni2 nrut; eauto with slow.
  destruct x as [v t].
  allrw @nrut_sub_cons; exrepnd; subst.
  eexists; dands; eauto.
  - simpl; intro k; repndors; subst; tcsp.
    unfold get_utokens_sub in ni1; allsimpl.
    allrw not_over_or; sp.
  - apply IHsub; auto.
    unfold get_utokens_sub in ni1; allsimpl.
    rw not_over_or in ni1; sp.
Qed.

Lemma nrut_sub_implies_nr_ut_sub {o} :
  forall (sub : @Sub o) l t,
    subset (get_utokens t) l
    -> nrut_sub l sub
    -> nr_ut_sub t sub.
Proof.
  induction sub; introv ss nrut; auto.
  destruct a as [v u].
  allrw @nrut_sub_cons; exrepnd; subst.
  rw @nr_ut_sub_cons_iff.
  eexists; dands; eauto; tcsp.
  apply (IHsub (a :: l)).
  - introv i.
    apply get_utokens_subst in i.
    boolvar; allsimpl; allrw in_app_iff; allsimpl; repndors; subst; tcsp.
  - apply nrut_sub_cons_l; auto.
Qed.
Hint Resolve nrut_sub_implies_nr_ut_sub : slow.

(*
Lemma reduces_to_vterm_nrut_sub_change {o} :
  forall lib t (sub1 sub2 : @Sub o) l v,
    subset (get_utokens t) l
    -> nrut_sub l sub1
    -> nrut_sub l sub2
    -> dom_sub sub1 = dom_sub sub2
    -> reduces_to lib (lsubst_aux t sub1) (vterm v)
    -> reduces_to lib (lsubst_aux t sub2) (vterm v).
Proof.
  introv ss nrut1 nrut2 eqdoms r.
  allunfold @reduces_to.
  exrepnd.
  exists k.
  pose proof (reduces_in_atmost_k_steps_change_utok_sub
                lib k t (vterm v) sub1 sub2) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  - unflsubst.
  - unfold nrut_sub in nrut1; repnd.
    eapply subset_disjoint_r;[|eauto]; eauto with slow.
  - unfold nrut_sub in nrut2; repnd.
    eapply subset_disjoint_r;[|eauto]; eauto with slow.
  - exrepnd.
    inversion h0 as [? y x|]; subst.
    unflsubst in x.
    destruct w as [z|op bs]; allsimpl.
    + remember (sub_find sub1 z) as sf; symmetry in Heqsf; destruct sf; subst.
      * apply sub_find_some in Heqsf.
        eapply in_nrut_sub in Heqsf; eauto.
        exrepnd; ginv.
      * ginv.
        apply sub_find_none_iff in Heqsf.
        unflsubst in h1; allsimpl.
        rw @sub_find_none_if in h1;[|rw <- eqdoms; auto].
        inversion h1; subst.
        unflsubst in h5.
    + unflsubst in h0; allsimpl.
      inversion h0.
Qed.
 *)

Definition range_utok_ren {o} (ren : @utok_ren o) :=
  map (fun x => snd x) ren.

Definition dom_utok_ren {o} (ren : @utok_ren o) :=
  map (fun x => fst x) ren.

Lemma OpBindings_ren_utok_op {o} :
  forall ren (op : @Opid o),
    OpBindings (ren_utok_op ren op)
    = OpBindings op.
Proof.
  destruct op; allsimpl; auto.
  destruct c; allsimpl; auto.
Qed.

Lemma wf_term_ren_utokens {o} :
  forall ren (t : @NTerm o),
    wf_term (ren_utokens ren t) <=> wf_term t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; allsimpl; auto; tcsp.

  - Case "oterm".
    allsimpl.
    allrw @wf_oterm_iff.
    allrw map_map; allunfold @compose.
    rw @OpBindings_ren_utok_op.
    split; introv k; repnd; dands; auto.

    + rw <- k0.
      apply eq_maps; introv i; destruct x as [l t]; simpl.
      unfold num_bvars; simpl; auto.

    + introv i.
      pose proof (k (ren_utokens_b ren b)) as h.
      autodimp h hyp.
      { rw in_map_iff; eexists; dands; eauto. }
      destruct b as [l t].
      allsimpl.
      allrw @wf_bterm_iff.
      apply ind in i; apply i; auto.

    + rw <- k0.
      apply eq_maps; introv i; destruct x as [l t]; simpl.
      unfold num_bvars; simpl; auto.

    + introv i.
      rw in_map_iff in i; exrepnd; subst.
      destruct a as [l t]; simpl.
      applydup k in i1.
      allrw @wf_bterm_iff.
      apply ind in i1; apply i1; auto.
Qed.

Lemma sub_find_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren v,
    sub_find (ren_utokens_sub ren sub) v
    = match sub_find sub v with
        | Some t => Some (ren_utokens ren t)
        | None => None
      end.
Proof.
  induction sub; introv; simpl; auto.
  destruct a as [x t]; allsimpl; boolvar; tcsp.
Qed.

Lemma sub_filter_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren l,
    sub_filter (ren_utokens_sub ren sub) l
    = ren_utokens_sub ren (sub_filter sub l).
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a as [v t]; allsimpl.
  boolvar; allsimpl; tcsp.
  f_equal; tcsp.
Qed.

Lemma lsubst_aux_ren_utokens {o} :
  forall (t : @NTerm o) sub ren,
    ren_utokens ren (lsubst_aux t sub)
    = lsubst_aux (ren_utokens ren t) (ren_utokens_sub ren sub).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; tcsp.

  - Case "vterm".
    rw @sub_find_ren_utokens_sub.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    rw @sub_filter_ren_utokens_sub.
    eapply ind; eauto.
Qed.

Lemma bound_vars_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    bound_vars (ren_utokens ren t) = bound_vars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; tcsp.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x as [l t]; allsimpl.
  apply app_if; tcsp.
  eapply ind; eauto.
Qed.

Lemma all_vars_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    all_vars (ren_utokens ren t) = all_vars t.
Proof.
  unfold all_vars; introv.
  rw @free_vars_ren_utokens.
  rw @bound_vars_ren_utokens.
  auto.
Qed.

Lemma ren_utokens_sub_var_ren {o} :
  forall (ren : @utok_ren o) vs1 vs2,
    ren_utokens_sub ren (var_ren vs1 vs2) = var_ren vs1 vs2.
Proof.
  induction vs1; introv; allsimpl.
  - unfold var_ren; simpl; auto.
  - destruct vs2; simpl.
    + rw @var_ren_nil_r; auto.
    + rw @var_ren_cons.
      f_equal; fold (@var_ren o vs1 vs2); auto.
Qed.

Lemma change_bvars_alpha_ren_utokens {o} :
  forall (t : @NTerm o) ren l,
    change_bvars_alpha l (ren_utokens ren t)
    = ren_utokens ren (change_bvars_alpha l t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x as [vs t]; simpl.
  pose proof (ind t vs i ren l) as h.
  rw h.
  rw @all_vars_ren_utokens.
  f_equal.
  rw @lsubst_aux_ren_utokens.
  rw @ren_utokens_sub_var_ren.
  auto.
Qed.

Lemma lsubst_ren_utokens {o} :
  forall (t : @NTerm o) sub ren,
    ren_utokens ren (lsubst t sub)
    = lsubst (ren_utokens ren t) (ren_utokens_sub ren sub).
Proof.
  introv.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_ren_utokens_sub.
  rw @bound_vars_ren_utokens.
  rw @change_bvars_alpha_ren_utokens.
  boolvar; apply lsubst_aux_ren_utokens.
Qed.

Lemma subst_ren_utokens {o} :
  forall (t : @NTerm o) v u ren,
    ren_utokens ren (subst t v u)
    = subst (ren_utokens ren t) v (ren_utokens ren u).
Proof.
  introv.
  apply @lsubst_ren_utokens.
Qed.

Lemma dec_op_eq_ntok {o} :
  forall (op : @Opid o),
    decidable ({a : get_patom_set o & op = Can (NUTok a)}).
Proof.
  introv; unfold decidable.
  destruct op; try (complete (right; sp; ginv)).
  destruct c; tcsp; try (complete (right; sp; ginv)).
  left; exists g; sp.
Qed.

Lemma ren_utokens_oterm {o} :
  forall op bs (ren : @utok_ren o),
    ren_utokens ren (oterm op bs)
    = oterm (match get_utok op with
               | Some a => Can (NUTok (ren_atom ren a))
               | None => op
             end) (map (ren_utokens_b ren) bs).
Proof.
  introv.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl;
  allapply @get_utok_some; subst; allsimpl; auto.
  destruct op as [can|ncan|exc|abs]; tcsp.
  destruct can; tcsp; allsimpl; ginv.
Qed.

Lemma ren_utokens_bterm {o} :
  forall ren l (t : @NTerm o),
    ren_utokens_b ren (bterm l t)
    = bterm l (ren_utokens ren t).
Proof. sp. Qed.

Definition get_utok_c {o} (c : @CanonicalOp o) :=
  match c with
    | NUTok a => Some a
    | _ => None
  end.

Lemma get_utok_can {o} :
  forall (can : @CanonicalOp o),
    get_utok (Can can) = get_utok_c can.
Proof.
  sp.
Qed.

Lemma ren_utokens_can {o} :
  forall c bs (ren : @utok_ren o),
    ren_utokens ren (oterm (Can c) bs)
    = oterm (Can (match get_utok_c c with
                    | Some a => NUTok (ren_atom ren a)
                    | None => c
                  end)) (map (ren_utokens_b ren) bs).
Proof.
  introv.
  rw @ren_utokens_oterm; f_equal.
  destruct c; tcsp.
Qed.

Ltac rw_ren_utok :=
  match goal with
    | [ H : _ |- _ ] =>
      first [ rewrite @ren_utokens_bterm in H
            | rewrite @ren_utokens_can in H
            | rewrite @ren_utokens_oterm in H
            | rewrite map_cons in H
            | rewrite map_nil in H
            ]
    | [ |- _ ] =>
      first [ rewrite @ren_utokens_bterm
            | rewrite @ren_utokens_can
            | rewrite @ren_utokens_oterm
            | rewrite map_cons
            | rewrite map_nil
            ]
  end.

Lemma ren_atom_cons {o} :
  forall a1 a2 (ren : @utok_ren o) a,
    ren_atom ((a1,a2) :: ren) a
    = if get_patom_deq o a a1
      then a2
      else ren_atom ren a.
Proof.
  introv; unfold ren_atom; simpl; boolvar; tcsp.
Qed.

Lemma in_dom_in_range {o} :
  forall (ren : @utok_ren o) a,
    LIn a (dom_utok_ren ren)
    -> LIn (ren_atom ren a) (range_utok_ren ren).
Proof.
  induction ren; introv i; allsimpl; tcsp.
  destruct a; allsimpl; repndors; subst; tcsp;
  allrw @ren_atom_cons; boolvar; subst; GC; tcsp.
Qed.

Lemma ren_atom_eq1 {o} :
  forall (ren : @utok_ren o) a1 a2,
    LIn a1 (dom_utok_ren ren)
    -> LIn a2 (dom_utok_ren ren)
    -> no_repeats (range_utok_ren ren)
    -> ren_atom ren a1 = ren_atom ren a2
    -> a1 = a2.
Proof.
  induction ren; introv i1 i2 norep e; allsimpl.
  - allsimpl; auto.
  - destruct a as [x y]; allsimpl.
    allrw no_repeats_cons; repnd.
    allrw @ren_atom_cons; boolvar; subst; repndors; GC; tcsp.
    + apply in_dom_in_range in i2; sp.
    + apply in_dom_in_range in i2; sp.
    + apply in_dom_in_range in i1; sp.
    + apply in_dom_in_range in i1; sp.
Qed.

Lemma ren_atom_not_in {o} :
  forall (ren : @utok_ren o) a,
    !LIn a (dom_utok_ren ren)
    -> ren_atom ren a = a.
Proof.
  induction ren; introv ni; allsimpl; tcsp.
  destruct a; allsimpl; allrw not_over_or; repnd.
  allrw @ren_atom_cons; boolvar; tcsp.
Qed.

Lemma ren_atom_or {o} :
  forall (ren : @utok_ren o) a,
    (ren_atom ren a = a) [+] (LIn (ren_atom ren a) (range_utok_ren ren)).
Proof.
  induction ren; introv; allsimpl; tcsp.
  destruct a; allsimpl; allrw @ren_atom_cons; boolvar; subst; tcsp.
  pose proof (IHren a0); sp.
Qed.

Definition ren_utokens_bs {p} (ren : utok_ren) (bs : list (@BTerm p)) :=
  map (ren_utokens_b ren) bs.

Definition ren_utokens_sk {o} (ren : utok_ren) (sk : @sosub_kind o) :=
  match sk with
    | sosk vs t => sosk vs (ren_utokens ren t)
  end.

Fixpoint ren_utokens_sosub {o} (ren : utok_ren) (sub : @SOSub o) :=
  match sub with
    | [] => []
    | (v,sk) :: s => (v, ren_utokens_sk ren sk) :: ren_utokens_sosub ren s
  end.

Lemma sosub_find_ren_utokens_sosub {o} :
  forall (sub : @SOSub o) ren v,
    sosub_find (ren_utokens_sosub ren sub) v
    = match sosub_find sub v with
        | Some sk => Some (ren_utokens_sk ren sk)
        | None => None
      end.
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  destruct s; allsimpl.
  boolvar; subst; tcsp.
Qed.

Lemma ren_utokens_sub_combine {o} :
  forall vs (ts : list (@NTerm o)) ren,
    ren_utokens_sub ren (combine vs ts)
    = combine vs (map (ren_utokens ren) ts).
Proof.
  induction vs; introv; allsimpl; tcsp.
  destruct ts; allsimpl; tcsp.
  f_equal; tcsp.
Qed.

Lemma oapp_eq_onil {T} :
  forall (o1 o2 : OList T),
    oapp o1 o2 = onil <=> (oappl [o1] = onil # oappl [o2] = onil).
Proof.
  induction o1 as [|l ind|f ind] using olist_better_ind;
  introv; split; introv h; allsimpl; repnd; subst; tcsp.
  - unfold onil, oapp, oappl in h.
    allsimpl; autorewrite with slow in *.
    destruct (oflatten o2); ginv.
  - unfold oapp, oappl in h; allsimpl; autorewrite with slow in *.
    remember (oflatten o2) as k; destruct k; allsimpl; ginv; GC.
  - destruct l; allsimpl; ginv.
    + dands; auto.
    + unfold oapp, oappl in h; allsimpl.
      unfold oappl; simpl.
      autorewrite with slow in *.
      remember (oflatten o) as l1.
      remember (flat_map oflatten l) as l2.
      remember (oflatten o2) as l3.
      destruct l1; allsimpl; auto; ginv.
      * destruct l2; allsimpl; auto; ginv.
        destruct l2; allsimpl; auto; ginv.
        destruct l3; allsimpl; auto; ginv.
      * destruct l1; allsimpl; auto; ginv.
        destruct l2; allsimpl; auto; ginv.
        destruct l3; allsimpl; auto; ginv.
  - unfold oapp, oappl; simpl.
    unfold oappl in h0; allsimpl.
    autorewrite with slow in *.
    remember (flat_map oflatten l) as l1.
    destruct l1; allsimpl; auto; ginv.
    + unfold oappl in h; allsimpl.
      autorewrite with slow in *.
      remember (oflatten o2) as l2.
      destruct l2; allsimpl; auto; ginv.
    + destruct l1; allsimpl; auto; ginv.
      unfold oappl in h; allsimpl.
      autorewrite with slow in *.
      remember (oflatten o2) as l2.
      destruct l2; allsimpl; auto; ginv.
      destruct l2; allsimpl; auto; ginv.
      subst; allsimpl.
      pose proof (@subset_flat_map_oflatten_singleton T [onil] l) as h; allsimpl.
      autodimp h hyp; ginv.
  - unfold oapp, oappl in h; allsimpl; autorewrite with slow in *.
    remember (oflatten o2) as l1.
    destruct l1; allsimpl; auto; ginv.
  - unfold oappl in h0; allsimpl; ginv.
Qed.

Lemma get_cutokens_so_onil {o} :
  forall (t : @SOTerm o),
    oapp (get_cutokens_so t) onil = get_cutokens_so t.
Proof.
  destruct t; introv; allsimpl.

  - unfold oapp, onil.
    autorewrite with slow.
    rw <- @oappl_nil.
    rw @oappl_app_oappl; autorewrite with slow; auto.

  - unfold oapp, onil.
    autorewrite with slow.
    rw <- @oappl_nil.
    rw cons_as_app.
    rw @oappl_app_oappl; autorewrite with slow; auto.

  - unfold oapp, onil.
    autorewrite with slow.
    rw <- @oappl_nil.
    rw @oappl_app_oappl; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_cutokens_so_onil : slow.

Lemma oappl_get_cutokens_so_singleton {o} :
  forall (t : @SOTerm o), oappl [get_cutokens_so t] = get_cutokens_so t.
Proof.
  introv.
  rewrite <- @get_cutokens_so_onil at 2.
  unfold oapp.
  unfold onil.
  rw <- @oappl_nil.
  rw @oappl_cons_oappl2; simpl; auto.
Qed.
Hint Rewrite @oappl_get_cutokens_so_singleton : slow.

Lemma no_utokens_sovar {o} :
  forall v (ts : list (@SOTerm o)),
    no_utokens (sovar v ts)
    <=> (forall t, LIn t ts -> no_utokens t).
Proof.
  introv.
  unfold no_utokens; simpl.
  rw flat_map_empty; sp.
Qed.

Definition no_utokens_b {o} (b : @SOBTerm o) :=
  match b with
    | sobterm _ t => no_utokens t
  end.

Lemma oappl_map_onil {T A} :
  forall (l : list A) (f : A -> OList T),
    oappl (map f l) = onil
    <=> (forall a, LIn a l -> oappl [f a] = onil).
Proof.
  induction l; allsimpl; introv; split; intro h; tcsp.
  - introv i.
    rw @oeqset_oappl_cons in h.
    apply oapp_eq_onil in h; repnd; autorewrite with slow in *.
    rw IHl in h.
    repndors; subst; tcsp.
  - rw @oeqset_oappl_cons.
    apply oapp_eq_onil; autorewrite with slow in *.
    rw IHl.
    dands; tcsp.
Qed.

Lemma oappl_map_OLO_onil {T} :
  forall (l : list T),
    oappl (map (fun x => OLO x) l) = onil <=> l = [].
Proof.
  introv; split; intro h; subst; allsimpl; auto.
  destruct l; allsimpl; ginv.
  unfold oappl in h; allsimpl.
  allrw flat_map_map; allunfold @compose.
  destruct l; allsimpl; auto; ginv.
Qed.

Lemma no_utokens_soterm {o} :
  forall op (bs : list (@SOBTerm o)),
    no_utokens (soterm op bs)
    <=> (get_utokens_o op = [] # forall b, LIn b bs -> no_utokens_b b).
Proof.
  introv.
  unfold no_utokens; simpl.
  rw app_eq_nil_iff.
  rw flat_map_empty.
  split; intro k; repnd; dands; auto; introv i; apply k in i.
  - destruct b; allsimpl; tcsp.
  - destruct a; allsimpl; tcsp.
Qed.

Lemma ren_utokens_apply_list {o} :
  forall (ts : list (@NTerm o)) t ren,
    ren_utokens ren (apply_list t ts)
    = apply_list (ren_utokens ren t) (map (ren_utokens ren) ts).
Proof.
  induction ts; introv; simpl; tcsp.
  rw IHts; simpl; auto.
Qed.

Lemma implies_ren_utok_op_id {o} :
  forall (op : @Opid o) ren,
    get_utokens_o op = []
    -> ren_utok_op ren op = op.
Proof.
  introv e.
  destruct op; tcsp.
  destruct c; tcsp.
  allsimpl; ginv.
Qed.

Lemma sosub_filter_ren_utokens_sosub {o} :
  forall (sub : @SOSub o) ren l,
    sosub_filter (ren_utokens_sosub ren sub) l
    = ren_utokens_sosub ren (sosub_filter sub l).
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  destruct s; allsimpl.
  boolvar; allsimpl; tcsp.
  f_equal; tcsp.
Qed.

Lemma ren_utokens_sosub_aux {o} :
  forall (t : @SOTerm o) ren sub,
    no_utokens t
    -> ren_utokens ren (sosub_aux sub t)
       = sosub_aux (ren_utokens_sosub ren sub) t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv nu; allsimpl; auto.

  - Case "sovar".
    rw @sosub_find_ren_utokens_sosub.
    remember (sosub_find sub (v,length ts)) as sf; symmetry in Heqsf; destruct sf.

    + destruct s; allsimpl.
      rw @lsubst_aux_ren_utokens.
      apply sosub_find_some in Heqsf; repnd.
      rw @ren_utokens_sub_combine; auto.
      f_equal; f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      rw @no_utokens_sovar in nu.
      applydup nu in i.
      eapply ind; eauto.

    + rw @ren_utokens_apply_list; simpl.
      f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      rw @no_utokens_sovar in nu.
      applydup nu in i.
      eapply ind; eauto.

  - Case "soterm".
    rw @no_utokens_soterm in nu; repnd.
    f_equal.

    + apply implies_ren_utok_op_id; auto.

    + allrw map_map; unfold compose.
      apply eq_maps; introv i.
      applydup nu in i.
      destruct x as [l t]; allsimpl.
      f_equal.
      erewrite ind; eauto.
      rw @sosub_filter_ren_utokens_sosub; auto.
Qed.

Lemma free_vars_sk_ren_utokens_sk {o} :
  forall (s : @sosub_kind o) ren,
    free_vars_sk (ren_utokens_sk ren s) = free_vars_sk s.
Proof.
  introv; destruct s; simpl.
  f_equal.
  rw @free_vars_ren_utokens; auto.
Qed.

Lemma bound_vars_sk_ren_utokens_sk {o} :
  forall (s : @sosub_kind o) ren,
    bound_vars_sk (ren_utokens_sk ren s) = bound_vars_sk s.
Proof.
  introv; destruct s; simpl.
  f_equal.
  rw @bound_vars_ren_utokens; auto.
Qed.

Lemma free_vars_sosub_ren_utokens_sosub {o} :
  forall (sub : @SOSub o) ren,
    free_vars_sosub (ren_utokens_sosub ren sub)
    = free_vars_sosub sub.
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  f_equal; tcsp.
  rw @free_vars_sk_ren_utokens_sk; auto.
Qed.

Lemma bound_vars_sosub_ren_utokens_sosub {o} :
  forall (sub : @SOSub o) ren,
    bound_vars_sosub (ren_utokens_sosub ren sub)
    = bound_vars_sosub sub.
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  f_equal; tcsp.
  rw @bound_vars_sk_ren_utokens_sk; auto.
Qed.

Lemma allvars_ren_utokens {o} :
  forall ren (t : @NTerm o),
    allvars (ren_utokens ren t) = allvars t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; allsimpl; auto.
  Case "oterm".
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  f_equal.
  eapply ind; eauto.
Qed.

Lemma allvars_sk_ren_utokens_sk {o} :
  forall (s : @sosub_kind o) ren,
    allvars_sk (ren_utokens_sk ren s) = allvars_sk s.
Proof.
  introv; destruct s; simpl.
  f_equal.
  apply allvars_ren_utokens.
Qed.

Lemma allvars_range_sosub_ren_utokens_sosub {o} :
  forall (sub : @SOSub o) ren,
    allvars_range_sosub (ren_utokens_sosub ren sub)
    = allvars_range_sosub sub.
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  f_equal; tcsp.
  apply allvars_sk_ren_utokens_sk.
Qed.

Lemma sk_change_bvars_alpha_ren_utokens_sk {o} :
  forall l ren (s : @sosub_kind o),
    sk_change_bvars_alpha l (ren_utokens_sk ren s)
    = ren_utokens_sk ren (sk_change_bvars_alpha l s).
Proof.
  introv; destruct s; simpl.
  unfold sk_change_bvars_alpha; simpl.
  rw @change_bvars_alpha_ren_utokens.
  allrw @all_vars_ren_utokens.
  rw @lsubst_aux_ren_utokens.
  rw @ren_utokens_sub_var_ren; auto.
Qed.

Lemma sosub_change_bvars_alpha_ren_utokens_sosub {o} :
  forall l ren (sub : @SOSub o),
    sosub_change_bvars_alpha l (ren_utokens_sosub ren sub)
    = ren_utokens_sosub ren (sosub_change_bvars_alpha l sub).
Proof.
  induction sub; introv; allsimpl; tcsp.
  destruct a; allsimpl.
  f_equal; tcsp.
  f_equal.
  apply sk_change_bvars_alpha_ren_utokens_sk.
Qed.

Lemma get_utokens_so_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) l ren,
    get_utokens_so (fo_change_bvars_alpha l ren t)
    = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv; simpl; auto.

  - Case "sovar".
    boolvar; subst; simpl; auto.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    apply ind; auto.

  - Case "soterm".
    f_equal.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [vs t]; simpl.
    eapply ind; eauto.
Qed.

Lemma get_cutokens_so_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) l ren,
    get_cutokens_so (fo_change_bvars_alpha l ren t)
    = get_cutokens_so t.
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; introv; simpl; auto.

  - Case "sovar".
    boolvar; subst; simpl; auto.
    allrw map_map; unfold compose.
    f_equal.
    apply eq_maps; introv i.
    apply ind; auto.

  - Case "soterm".
    f_equal.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [vs t]; simpl.
    eapply ind; eauto.
Qed.

Lemma ren_utokens_sosub_eq {o} :
  forall (t : @SOTerm o) ren sub,
    no_utokens t
    -> ren_utokens ren (sosub sub t)
       = sosub (ren_utokens_sosub ren sub) t.
Proof.
  introv nu.
  unfold sosub.
  allrw @free_vars_sosub_ren_utokens_sosub.
  allrw @bound_vars_sosub_ren_utokens_sosub.
  allrw @allvars_range_sosub_ren_utokens_sosub.
  rw @sosub_change_bvars_alpha_ren_utokens_sosub.
  boolvar; tcsp;
  try (complete (apply ren_utokens_sosub_aux; auto)).
  - rw @ren_utokens_sosub_aux; auto.
    unfold no_utokens.
    rw @get_utokens_so_fo_change_bvars_alpha; auto.
  - rw @ren_utokens_sosub_aux; auto.
    + rw @sosub_change_bvars_alpha_ren_utokens_sosub; auto.
    + unfold no_utokens; rw @get_utokens_so_fo_change_bvars_alpha; auto.
Qed.

Lemma ren_utokens_sosub_mk_abs_subst {o} :
  forall vars (bs : list (@BTerm o)) ren,
    ren_utokens_sosub ren (mk_abs_subst vars bs)
    = mk_abs_subst vars (map (ren_utokens_b ren) bs).
Proof.
  induction vars; introv; allsimpl; tcsp.
  destruct a; destruct bs; allsimpl; tcsp.
  destruct b; allsimpl; boolvar; tcsp.
  subst; allsimpl; f_equal; tcsp.
Qed.

Lemma ren_utokens_mk_instance {o} :
  forall ren vars bs (rhs : @SOTerm o),
    no_utokens rhs
    -> ren_utokens ren (mk_instance vars bs rhs)
       = mk_instance vars (map (ren_utokens_b ren) bs) rhs.
Proof.
  introv nu.
  unfold mk_instance.
  rewrite ren_utokens_sosub_eq; auto.
  rw @ren_utokens_sosub_mk_abs_subst; auto.
Qed.

Lemma canonical_form_test_nutok_ren {o} :
  forall c (ren : @utok_ren o) a,
    canonical_form_test_for c (NUTok (ren_atom ren a))
    = canonical_form_test_for c (NUTok a).
Proof.
  introv.
  destruct c; simpl; tcsp.
Qed.

Lemma isvalue_like_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    isvalue_like t
    -> isvalue_like (ren_utokens ren t).
Proof.
  introv isv.
  allunfold @isvalue_like; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; allsimpl; tcsp;
    destruct c; allsimpl; tcsp.
  - apply isexc_implies2 in isv; exrepnd; subst; allsimpl; tcsp.
Qed.
Hint Resolve isvalue_like_ren_utokens : slow.

Lemma isnoncan_like_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    isnoncan_like t
    -> isnoncan_like (ren_utokens ren t).
Proof.
  introv isv.
  allunfold @isnoncan_like; repndors.
  - apply isnoncan_implies in isv; exrepnd; subst; allsimpl; tcsp.
  - apply isabs_implies in isv; exrepnd; subst; allsimpl; tcsp.
Qed.
Hint Resolve isnoncan_like_ren_utokens : slow.

Lemma ren_utokens_pushdown_fresh {o} :
  forall ren v (t : @NTerm o),
    ren_utokens ren (pushdown_fresh v t)
    = pushdown_fresh v (ren_utokens ren t).
Proof.
  introv.
  unfold pushdown_fresh.
  destruct t; simpl; auto.
  f_equal.
  unfold mk_fresh_bterms; allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [vs t]; simpl.
  f_equal; fold_terms.
  f_equal.
  unfold maybe_new_var, newvar.
  rw @free_vars_ren_utokens; auto.
Qed.

Lemma ren_utokens_utoken_not_in_dom {o} :
  forall (ren : @utok_ren o) a,
    !LIn a (dom_utok_ren ren)
    -> ren_utokens ren (mk_utoken a) = mk_utoken a.
Proof.
  introv ni; simpl.
  unfold mk_utoken.
  rw @ren_atom_not_in; auto.
Qed.

Lemma ren_utokens_trivial {o} :
  forall ren (t : @NTerm o),
    disjoint (dom_utok_ren ren) (get_utokens t)
    -> ren_utokens ren t = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv disj; allsimpl; auto.
  Case "oterm".
  allrw disjoint_app_r; repnd.
  f_equal.
  - destruct op; tcsp.
    destruct c; tcsp.
    allsimpl; allrw disjoint_singleton_r.
    rw @ren_atom_not_in; auto.
  - apply eq_map_l; introv i.
    destruct x as [l t]; simpl.
    f_equal.
    eapply ind; eauto.
    disj_flat_map; allsimpl; auto.
Qed.

Lemma size_ren_utokens {o} :
  forall ren (t : @NTerm o),
    size (ren_utokens ren t) = size t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; allsimpl; tcsp.
  f_equal; f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x as [l t]; simpl.
  eapply ind; eauto.
Qed.

Lemma osize_ren_utokens {o} :
  forall ren (t : @NTerm o),
    osize (ren_utokens ren t) = osize t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; allsimpl; tcsp.
  f_equal; f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x as [l t]; simpl.
  eapply ind; eauto.
Qed.

Fixpoint compose_ren_utokens {o} (ren1 ren2 : @utok_ren o) :=
  match ren2 with
    | [] => []
    | (a1,a2) :: r => (a1,ren_atom ren1 a2) :: compose_ren_utokens ren1 r
  end.

Lemma utok_ren_find_app {o} :
  forall (ren1 ren2 : @utok_ren o) v,
    utok_ren_find (ren1 ++ ren2) v
    = match utok_ren_find ren1 v with
        | Some a => Some a
        | None => utok_ren_find ren2 v
      end.
Proof.
  induction ren1; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; subst; tcsp.
Qed.

Lemma utok_ren_find_compose_ren_utokens {o} :
  forall (ren1 ren2 : @utok_ren o) a,
    utok_ren_find (compose_ren_utokens ren1 ren2) a
    = match utok_ren_find ren2 a with
        | Some a => Some (ren_atom ren1 a)
        | None => None
      end.
Proof.
  induction ren2; introv; simpl; auto.
  destruct a; allsimpl; boolvar; tcsp.
Qed.

Lemma ren_utokens_ren_utokens {o} :
  forall (t : @NTerm o) ren1 ren2,
    ren_utokens ren1 (ren_utokens ren2 t)
    = ren_utokens (compose_ren_utokens ren1 ren2 ++ ren1) t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  f_equal.
  - destruct op; tcsp.
    destruct c; tcsp.
    allsimpl.
    unfold ren_atom.
    rw @utok_ren_find_app.
    rw @utok_ren_find_compose_ren_utokens.
    remember (utok_ren_find ren2 g) as ur; symmetry in Hequr; destruct ur; tcsp.
  - allrw map_map; unfold compose.
    apply eq_maps; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
Qed.

Lemma compose_ren_utokens_trivial {o} :
  forall (ren1 ren2 : @utok_ren o),
    disjoint (dom_utok_ren ren1) (range_utok_ren ren2)
    -> compose_ren_utokens ren1 ren2 = ren2.
Proof.
  induction ren2; introv disj; allsimpl; auto.
  destruct a; allsimpl.
  allrw disjoint_cons_r; repnd.
  repeat f_equal; tcsp.
  apply ren_atom_not_in; auto.
Qed.

Lemma ren_atom_app_weak_r {o} :
  forall (ren1 ren2 : @utok_ren o) a,
    !LIn a (dom_utok_ren ren1)
    -> ren_atom (ren1 ++ ren2) a = ren_atom ren2 a.
Proof.
  induction ren1; introv ni; allsimpl; auto.
  destruct a; allsimpl; allrw not_over_or; repnd.
  rw @ren_atom_cons; boolvar; tcsp.
Qed.

Lemma utok_ren_find_none_if_not_in {o} :
  forall a (ren : @utok_ren o),
    !LIn a (dom_utok_ren ren)
    -> utok_ren_find ren a = None.
Proof.
  induction ren; introv i; allsimpl; auto.
  destruct a0; allsimpl; allrw not_over_or; repnd.
  boolvar; tcsp.
Qed.

Lemma ren_atom_app_weak_l {o} :
  forall (ren1 ren2 : @utok_ren o) a,
    !LIn a (dom_utok_ren ren2)
    -> ren_atom (ren1 ++ ren2) a = ren_atom ren1 a.
Proof.
  introv ni.
  unfold ren_atom.
  rw @utok_ren_find_app.
  remember (utok_ren_find ren1 a) as f; symmetry in Heqf; destruct f; auto.
  rw @utok_ren_find_none_if_not_in; auto.
Qed.

Lemma ren_utokens_app_weak_l {o} :
  forall (t : @NTerm o) ren1 ren2,
    disjoint (dom_utok_ren ren2) (get_utokens t)
    -> ren_utokens (ren1 ++ ren2) t
       = ren_utokens ren1 t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv disj; allsimpl; tcsp.
  f_equal.
  - destruct op; tcsp.
    destruct c; tcsp.
    allsimpl.
    allrw disjoint_cons_r; repnd.
    rw @ren_atom_app_weak_l; auto.
  - apply eq_maps; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    allrw disjoint_app_r; repnd.
    disj_flat_map; allsimpl.
    eapply ind; eauto.
Qed.

Lemma ren_utokens_app_weak_r {o} :
  forall (t : @NTerm o) ren1 ren2,
    disjoint (dom_utok_ren ren1) (get_utokens t)
    -> ren_utokens (ren1 ++ ren2) t
       = ren_utokens ren2 t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv disj; allsimpl; tcsp.
  f_equal.
  - destruct op; tcsp.
    destruct c; tcsp.
    allsimpl.
    allrw disjoint_cons_r; repnd.
    rw @ren_atom_app_weak_r; auto.
  - apply eq_maps; introv i; destruct x as [l t]; allsimpl.
    f_equal.
    allrw disjoint_app_r; repnd.
    disj_flat_map; allsimpl.
    eapply ind; eauto.
Qed.

Lemma get_utokens_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    get_utokens (ren_utokens ren t)
    = map (ren_atom ren) (get_utokens t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; tcsp.
  allrw map_app; allrw map_flat_map; allrw flat_map_map; unfold compose.
  f_equal.
  - destruct op; tcsp.
    destruct c; tcsp.
  - apply eq_flat_maps; introv i.
    destruct x as [l t]; allsimpl.
    eapply ind; eauto.
Qed.

Lemma simple_ren_utokens_subst_utokens_aux_eq1 {o} :
  forall (t : @NTerm o) ren a a' x atoms,
    subset (get_utokens t) (a :: atoms)
    -> (forall b, LIn b atoms -> a' <> ren_atom ren b)
    -> subst_utokens_aux (ren_utokens ((a, a') :: ren) t) [(a',mk_var x)]
       = ren_utokens ren (subst_utokens_aux t [(a,mk_var x)]).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv ss d; tcsp.
  Case "oterm".
  rw @ren_utokens_oterm.
  allrw @subst_utokens_aux_oterm.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

  - apply get_utok_some in Heqguo; subst; allsimpl.
    allrw map_map; unfold compose.
    allrw subset_cons_l; repnd; allsimpl.
    allrw @ren_atom_cons; allsimpl; boolvar; subst; tcsp.

    + unfold subst_utok; simpl; boolvar; GC; tcsp.

    + repndors; tcsp.
      unfold subst_utok; simpl; boolvar; subst; allsimpl; tcsp; GC.

      * applydup d in ss0; tcsp.

      * f_equal.
        allrw map_map; unfold compose.
        apply eq_maps; introv i; destruct x0 as [l t]; allsimpl.
        f_equal.
        eapply ind; eauto.
        rw subset_flat_map in ss.
        apply ss in i; allsimpl; auto.

  - allrw Heqguo.
    allrw subset_app; repnd.
    applydup @get_utok_none in Heqguo.
    rw @implies_ren_utok_op_id; auto.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i; destruct x0 as [l t]; allsimpl.
    rw subset_flat_map in ss.
    applydup ss in i; allsimpl.
    f_equal.
    eapply ind; eauto.
Qed.

Lemma simple_ren_utokens_subst_utokens_eq1 {o} :
  forall (t : @NTerm o) ren a a' x atoms,
    subset (get_utokens t) (a :: atoms)
    -> (forall b, LIn b atoms -> a' <> ren_atom ren b)
    -> subst_utokens (ren_utokens ((a, a') :: ren) t) [(a',mk_var x)]
       = ren_utokens ren (subst_utokens t [(a,mk_var x)]).
Proof.
  introv ss d.
  unfold subst_utokens; simpl.
  rw @bound_vars_ren_utokens.
  rw @change_bvars_alpha_ren_utokens.
  boolvar.
  - eapply simple_ren_utokens_subst_utokens_aux_eq1; eauto.
  - eapply simple_ren_utokens_subst_utokens_aux_eq1; eauto.
    t_change t'.
    apply alphaeq_preserves_utokens in h.
    rw <- h; auto.
Qed.

Definition get_utok_pk {o} (pk : @param_kind o) : option (get_patom_set o) :=
  match pk with
    | PKa a => Some a
    | _ => None
  end.

Lemma get_utok_c_pk2can {o} :
  forall (pk : @param_kind o),
    get_utok_c (pk2can pk) = get_utok_pk pk.
Proof.
  introv; destruct pk; simpl; auto.
Qed.

Definition ren_atom_pk {o} ren (pk : @param_kind o) :=
  match pk with
    | PKa a => PKa (ren_atom ren a)
    | _ => pk
  end.

Lemma match_get_utok_pk {o} :
  forall (pk : @param_kind o) ren,
    match get_utok_pk pk with
      | Some a => NUTok (ren_atom ren a)
      | None => pk2can pk
    end
    = pk2can (ren_atom_pk ren pk).
Proof.
  introv.
  destruct pk; allsimpl; auto.
Qed.

Definition get_utokens_pk {o} (pk : @param_kind o) : list (get_patom_set o) :=
  match pk with
    | PKa a => [a]
    | _ => []
  end.

Lemma ren_atom_pk_eq1 {o} :
  forall (ren : utok_ren) (pk1 pk2 : @param_kind o),
    subset (get_utokens_pk pk1) (dom_utok_ren ren)
    -> subset (get_utokens_pk pk2) (dom_utok_ren ren)
    -> no_repeats (range_utok_ren ren)
    -> ren_atom_pk ren pk1 = ren_atom_pk ren pk2
    -> pk1 = pk2.
Proof.
  introv ss1 ss2 norep e.
  destruct pk1, pk2; allsimpl; ginv.
  allrw singleton_subset.
  f_equal.
  eapply ren_atom_eq1; eauto.
  inversion e; auto.
Qed.

Lemma get_utok_c_some {o} :
  forall (can : @CanonicalOp o) a,
    get_utok_c can = Some a -> can = NUTok a.
Proof.
  introv e.
  destruct can; allsimpl; ginv; tcsp.
Qed.

Lemma co_wf_map {o} :
  forall c can f (l : list (@BTerm o)),
    co_wf c can (map f l) = co_wf c can l.
Proof.
  introv; unfold co_wf; destruct can, l; simpl; auto.
Qed.
Hint Rewrite @co_wf_map : slow.

Lemma ca_wf_map {o} :
  forall can f (l : list (@BTerm o)),
    ca_wf can (map f l) = ca_wf can l.
Proof.
  introv; unfold ca_wf; destruct can, l; simpl; auto.
Qed.
Hint Rewrite @ca_wf_map : slow.

Lemma iscan_ren_utokens {o} :
  forall ren (t : @NTerm o),
    iscan t -> iscan (ren_utokens ren t).
Proof.
  introv isc.
  apply iscan_implies in isc.
  repndors; exrepnd; subst; simpl; auto.
  destruct c; auto.
Qed.
Hint Resolve iscan_ren_utokens : slow.

Lemma nt_wf_oterm_snd {o} :
  forall b (op : @Opid o) (t : NTerm) (vs : list NVar) (bs : list BTerm),
    nt_wf (oterm op (b :: bterm vs t :: bs)) -> nt_wf t.
Proof.
  introv w.
  apply nt_wf_oterm_iff in w; repnd; allsimpl.
  pose proof (w (bterm vs t)) as h; autodimp h hyp.
  allrw @bt_wf_iff; auto.
Qed.

Lemma compute_step_ren_utokens {o} :
  forall lib (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> compute_step lib t = csuccess u
    -> compute_step lib (ren_utokens ren t) = csuccess (ren_utokens ren u).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf norep disj comp; auto.

  - Case "vterm".
    allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    csunf; simpl; auto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; simpl in comp; ginv.
      csunf; destruct can; tcsp.

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [v|f|op bts]; try (complete (allsimpl; ginv)).

        { csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          - SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            csunf; simpl; auto.

          - SSCase "NEApply".
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
            repndors; exrepnd; subst.

            + apply compute_step_eapply2_success in comp1; repnd; subst; allsimpl.
              repndors; exrepnd; subst; allsimpl; ginv; GC.
              csunf; simpl; dcwf h; simpl; boolvar; try omega; auto.
              allrw @Znat.Nat2Z.id.
              rw @ren_utokens_trivial; auto.

              apply nt_wf_oterm_fst in wf.
              rw @nt_wf_sterm_iff in wf.
              pose proof (wf n) as h; clear wf; repnd.
              rw h; auto.

            + csunf; simpl.
              apply isexc_implies2 in comp0; exrepnd; subst; allsimpl.
              dcwf h; auto.

            + allrw @nt_wf_eapply_iff; exrepnd; allunfold @nobnd; ginv; allsimpl.
              autorewrite with slow in *.
              pose proof (ind b b []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              pose proof (h x ren) as ih; clear h.
              repeat (autodimp ih hyp).
              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
              rw ih; auto.

          - SSCase "NFix".
            apply compute_step_fix_success in comp; repnd; subst; allsimpl.
            autorewrite with slow in *.
            csunf; simpl; auto.

          - SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
            autorewrite with slow in *.
            csunf; simpl; auto.
            unfold apply_bterm; simpl.
            rw @subst_ren_utokens; auto.

          - SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
            autorewrite with slow in *.
            csunf; simpl; auto.

          - SSCase "NCanTest".
            allrw @nt_wf_NCanTest; exrepnd; allunfold @nobnd; ginv; allsimpl.
            autorewrite with slow in *.
            csunf; simpl; auto.
        }

        dopid op as [can2|ncan2|exc2|abs2] SSCase.

        * SSCase "Can".
          dopid_noncan ncan SSSCase.

          { SSSCase "NApply".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; simpl; auto.
            rw @subst_ren_utokens; auto.
          }

          { SSSCase "NEApply".

            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
            repndors; exrepnd; subst; allsimpl.

            - apply compute_step_eapply2_success in comp1.
              repnd; subst; allsimpl; autorewrite with slow in *.
              repndors; exrepnd; subst; ginv;[|].

              { allunfold @mk_lam; ginv; simpl; fold_terms; unfold mk_eapply.
                rw @compute_step_eapply_lam_iscan; eauto 3 with slow.
                unfold apply_bterm; simpl; allrw @fold_subst.
                rw @subst_ren_utokens; auto. }

              { allunfold @mk_nseq; ginv; allsimpl; fold_terms; GC.
                csunf; simpl; dcwf h; simpl; boolvar; try omega.
                rw Znat.Nat2Z.id; auto. }

            - apply isexc_implies2 in comp0; exrepnd; subst; allsimpl.
              csunf; simpl.
              unfold eapply_wf_def in comp2; repndors; exrepnd; ginv; subst.
              { allunfold @mk_nseq; ginv; allsimpl.
                autorewrite with slow in *; dcwf h; auto. }
              { allunfold @mk_lam; ginv; allsimpl; autorewrite with slow in *;
                dcwf h; auto. }

            - allrw @nt_wf_eapply_iff; exrepnd; allunfold @nobnd; ginv; allsimpl.
              autorewrite with slow in *.
              pose proof (ind b b []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.

              allrw @diff_app_r.
              allrw disjoint_app_r; repnd.

              pose proof (h x ren) as ih; clear h.
              repeat (autodimp ih hyp).
              fold_terms; unfold mk_eapply;[].
              unfold eapply_wf_def in comp2; repndors; exrepnd; subst; ginv.
              { allunfold @mk_nseq; ginv; allsimpl; autorewrite with slow in *.
                rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
                { rw ih; auto. }
                { apply eapply_wf_true; simpl; auto. } }
              { allunfold @mk_lam; ginv; allsimpl; autorewrite with slow in *.
                rw @compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
                { rw ih; auto. }
                { apply eapply_wf_true; simpl; auto. } }
          }

(*          { SSSCase "NApseq".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_apseq_success in comp; exrepnd; subst; allsimpl.
            rw @Znat.Nat2Z.id.
            boolvar; try omega; auto.
          }*)

          { SSSCase "NFix".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_fix_success in comp; repnd; subst.
            unfold mk_apply, nobnd.
            repeat rw_ren_utok.
            remember (get_utok (Can can2)) as gu; destruct gu; simpl; auto.
          }

          { SSSCase "NSpread".

            clear ind; csunf comp; simpl in comp.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl; fold_terms.
            csunf; allsimpl; rw @lsubst_ren_utokens; auto.
          }

          { SSSCase "NDsup".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl; fold_terms.
            rw @lsubst_ren_utokens; auto.
          }

          { SSSCase "NDecide".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_decide_success in comp; exrepnd; subst.
            repndors; repnd; subst; simpl; rw @subst_ren_utokens; auto.
          }

          { SSSCase "NCbv".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_cbv_success in comp; exrepnd; subst.
            repeat rw_ren_utok.
            remember (get_utok_c can2) as gu; destruct gu; simpl; auto;
            unfold apply_bterm; simpl; rw @subst_ren_utokens; auto; auto;
            repeat rw_ren_utok; rw <- Heqgu; auto.
          }

          { SSSCase "NSleep".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl; fold_terms.
            unfold compute_step_sleep; simpl; auto.
          }

          { SSSCase "NTUni".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl; fold_terms.
            unfold compute_step_tuni; simpl.
            boolvar; try omega.
            rw Znat.Nat2Z.id; auto.
          }

          { SSSCase "NMinus".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl; fold_terms.
            unfold compute_step_minus; simpl; auto.
          }

          { SSSCase "NFresh".

            csunf comp; allsimpl; ginv.
          }

          { SSSCase "NTryCatch".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_try_success in comp; exrepnd; subst.
            unfold mk_atom_eq, nobnd.
            repeat rw_ren_utok.
            remember (get_utok (Can can2)) as gu; symmetry in Heqgu; destruct gu;
            allapply @get_utok_some; ginv; tcsp.
          }

          { SSSCase "NParallel".
            csunf comp; simpl in comp.
            apply compute_step_parallel_success in comp; subst.
            csunf; simpl.
            destruct can2; allsimpl; tcsp.
          }

          { SSSCase "NCompOp".

            destruct bs; try (complete (csunf comp; allsimpl; dcwf h)).
            destruct b as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            - SSSSCase "Can".
              csunf comp; csunf; simpl in comp; boolvar; tcsp; ginv.
              dcwf h;[].
              apply compute_step_compop_success_can_can in comp; exrepnd; subst.
              repndors; exrepnd;
              allrw @get_param_from_cop_some; subst;
              repeat rw_ren_utok; allsimpl;
              dcwf h; allsimpl; GC; tcsp;
              allrw @get_utok_c_pk2can;
              allrw @match_get_utok_pk;
              unfold compute_step_comp; simpl;
              allrw @get_param_from_cop_pk2can;
              boolvar; subst; tcsp;
              try (complete (allunfold @co_wf; allsimpl; allrw @get_param_from_cop_pk2can; ginv));[].

              allrw app_nil_r.
              allrw diff_cons_r; allrw diff_app_r.
              allrw disjoint_cons_r; allrw disjoint_app_r; repnd.

              destruct pk1, pk2; allsimpl; ginv; tcsp;[].
              inversion e as [e']; clear e.
              assert (g <> g0) as d by (intros xx; subst; tcsp).
              allrw diff_cons_r; allrw diff_nil; boolvar; allrw disjoint_singleton_r.

              + apply ren_atom_eq1 in e'; tcsp.

              + apply ren_atom_not_in in n0; rw n0 in e'.
                pose proof (ren_atom_or ren g0) as h; repndors.
                * rw h in e'; sp.
                * rw <- e' in h; sp.

              + apply ren_atom_not_in in n0; rw n0 in e'.
                pose proof (ren_atom_or ren g) as h; repndors.
                * rw h in e'; sp.
                * rw e' in h; sp.

              + apply ren_atom_not_in in n0; rw n0 in e'.
                apply ren_atom_not_in in n1; rw n1 in e'.
                sp.

            - SSSSCase "NCan".
              rw @compute_step_ncompop_ncan2 in comp; boolvar; tcsp; ginv;[].
              dcwf h;[].
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1; destruct comp1; ginv.
              simphyps.
              allrw diff_app_r; allrw disjoint_app_r; repnd.
              applydup @nt_wf_oterm_snd in wf as w2.
              eapply ind in Heqcomp1; eauto; simphyps; eauto 3 with slow;[].
              repeat rw_ren_utok.
              csunf; simpl; dcwf h;
              remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu; simpl; auto;
              try (rw Heqcomp1); allsimpl; auto;
              allapply @get_utok_c_some; subst; allrw @co_wf_map;
              apply co_wf_false_implies_not in Heqh0; destruct Heqh0; tcsp.
              allunfold @co_wf_def; exrepnd; subst; exists (PKa (ren_atom ren g)); allsimpl;
              ginv; dands; tcsp; repndors; exrepnd; subst; ginv.

            - SSSSCase "Exc".
              csunf comp; csunf; simphyps; ginv; dcwf h;[]; ginv.
              repeat rw_ren_utok.
              remember (get_utok_c can2) as gu; destruct gu; symmetry in Heqgu;
              simpl; auto; dcwf h; tcsp;[].
              allapply @get_utok_c_some; subst; allrw @co_wf_map;
              apply co_wf_false_implies_not in Heqh0; destruct Heqh0; tcsp.
              allunfold @co_wf_def; exrepnd; subst; exists (PKa (ren_atom ren g)); allsimpl;
              ginv; dands; tcsp; repndors; exrepnd; subst; ginv; tcsp.

            - SSSSCase "Abs".
              csunf comp; csunf; simphyps; dcwf h; [].
              csunf comp; simphyps.
              remember (compute_step_lib lib abs3 bs2) as csl;
                symmetry in Heqcsl; destruct csl; ginv.
              repeat rw_ren_utok.
              applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
              pose proof (compute_step_lib_success_change_bs
                            lib abs3 oa2
                            bs2 (map (ren_utokens_b ren) bs2)
                            vars rhs correct) as h.
              repeat (autodimp h hyp).
              { allrw map_map; unfold compose; apply eq_maps; introv i;
                destruct x as [l t]; simpl; unfold num_bvars; auto. }

              unfold correct_abs in correct; repnd; allsimpl; dcwf q;
              remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu;
              allsimpl; tcsp; allapply @get_utok_c_some; subst;
              try (csunf; allsimpl; rw h); simpl; auto;
              allrw @ren_utokens_mk_instance; auto;
              allrw @co_wf_map;
              apply co_wf_false_implies_not in Heqq; destruct Heqq;
              allunfold @co_wf_def; exrepnd; subst; allsimpl; ginv;
              allrw @get_param_from_cop_some; subst;
              allrw @get_param_from_cop_pk2can;
              eexists; dands; eauto;
              repndors; exrepnd; subst; ginv; tcsp.
          }

          { SSSCase "NArithOp".

            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            - SSSSCase "Can".
              csunf comp; csunf; simphyps; dcwf h;[].
              apply compute_step_arithop_success_can_can in comp; exrepnd; subst.
              allrw @get_param_from_cop_some; subst.
              subst; allsimpl; auto.

            - SSSSCase "NCan".
              allrw @compute_step_narithop_ncan2.
              dcwf h.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1; destruct comp1; ginv.
              simphyps.
              allrw diff_app_r; allrw disjoint_app_r; repnd.
              applydup @nt_wf_oterm_snd in wf as w2.
              eapply ind in Heqcomp1; eauto; simphyps; eauto 3 with slow.
              csunf.
              repeat rw_ren_utok; allsimpl; dcwf h;
              remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu; simpl; auto;
              try (rw Heqcomp1); simpl; tcsp;
              allapply @get_utok_c_some; subst; allrw @ca_wf_map;
              apply ca_wf_false_implies_not in Heqh0; destruct Heqh0; tcsp.
              allunfold @ca_wf_def; exrepnd; subst; ginv.

            - SSSSCase "Exc".
              csunf comp; csunf; simphyps; ginv.
              dcwf h; ginv.
              repeat rw_ren_utok.
              remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu; simpl; auto;
              allapply @get_utok_c_some; subst; dcwf h; auto.
              allrw @ca_wf_map.
              apply ca_wf_false_implies_not in Heqh0; destruct Heqh0; tcsp.
              allunfold @ca_wf_def; exrepnd; subst; ginv.

            - SSSSCase "Abs".
              allrw @compute_step_narithop_abs2; boolvar; tcsp; ginv.
              dcwf h;[].
              remember (compute_step_lib lib abs3 bs2) as csl;
                symmetry in Heqcsl; destruct csl; ginv.
              repeat rw_ren_utok.
              applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
              pose proof (compute_step_lib_success_change_bs
                            lib abs3 oa2
                            bs2 (map (ren_utokens_b ren) bs2)
                            vars rhs correct) as h.
              repeat (autodimp h hyp).
              { allrw map_map; unfold compose; apply eq_maps; introv i;
                destruct x as [l t]; simpl; unfold num_bvars; auto. }
              unfold correct_abs in correct; repnd.
              remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu; simpl; auto;
              allapply @get_utok_c_some; subst;
              csunf; simpl; csunf; simpl; rw h; simpl; tcsp;
              dcwf q;
              rw @ren_utokens_mk_instance; auto;
              allrw @ca_wf_map.
              apply ca_wf_false_implies_not in Heqq; destruct Heqq; tcsp.
              allunfold @ca_wf_def; exrepnd; subst; ginv.
          }

          { SSSCase "NCanTest".

            clear ind; csunf comp; csunf.
            simphyps.
            apply compute_step_can_test_success in comp; exrepnd; subst.
            repeat rw_ren_utok.
            remember (get_utok_c can2) as gu; symmetry in Heqgu; destruct gu; simpl; auto;
            allapply @get_utok_c_some; subst; ginv;
            try (rw @canonical_form_test_nutok_ren).
            - remember (canonical_form_test_for c (NUTok g)) as cft; destruct cft; auto.
            - remember (canonical_form_test_for c can2) as cft; destruct cft; auto.
          }

        * SSCase "NCan".
          allsimpl.
          allrw @compute_step_ncan_ncan.
          remember (compute_step lib (oterm (NCan ncan2) bts)) as cs;
            symmetry in Heqcs; destruct cs; ginv.
          pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as h;
            repeat (autodimp h hyp); eauto 3 with slow.
          allrw diff_app_r; allrw disjoint_app_r; repnd.
          applydup @nt_wf_oterm_fst in wf as w1.
          eapply h in Heqcs; eauto; exrepnd; clear h; allsimpl;[].
          rw Heqcs; auto.

        * SSCase "Exc".
          csunf comp; csunf; allsimpl.
          apply compute_step_catch_success in comp; dorn comp; exrepnd; subst;
          allsimpl; tcsp.

          { boolvar; subst; tcsp; GC.
            rw @subst_ren_utokens; auto. }

          { rw @compute_step_catch_non_trycatch; auto. }

        * SSCase "Abs".
          allsimpl.
          allrw @compute_step_ncan_abs.

          remember (compute_step_lib lib abs2 bts) as csl;
            symmetry in Heqcsl; destruct csl; ginv; simpl.

          applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
          applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
          unfold matching_entry in Heqcsl0; repnd.

          pose proof (compute_step_lib_success_change_bs
                        lib abs2 oa2
                        bts (map (ren_utokens_b ren) bts)
                        vars rhs correct) as h.
          repeat (autodimp h hyp);
            [ rw map_map; unfold compose; apply eq_maps;
              introv i; destruct x; unfold num_bvars; auto
            | ].
          rw h; clear h.
          unfold correct_abs in correct; repnd.
          rw @ren_utokens_mk_instance; auto.
      }

      { (* fresh case *)

        csunf comp; csunf; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst.

        - allsimpl; boolvar; tcsp.

        - rw @compute_step_fresh_if_isvalue_like0; eauto 2 with slow.
          rw @ren_utokens_pushdown_fresh; auto.

        - rw @compute_step_fresh_if_isnoncan_like0; eauto with slow.
          allsimpl; fold_terms.

          remember (get_fresh_atom t) as a.
          pose proof (get_fresh_atom_prop t) as fa; rw <- Heqa in fa.

          destruct (fresh_atom o (get_utokens t
                                              ++ dom_utok_ren ren
                                              ++ range_utok_ren ren
                                              ++ get_utokens (ren_utokens ren t)
                                              ++ get_utokens x)) as [a' nia'].
          allrw in_app_iff; allrw not_over_or; repnd.

          remember (get_fresh_atom (ren_utokens ren t)) as a''.
          pose proof (get_fresh_atom_prop (ren_utokens ren t)) as fa''; rw <- Heqa'' in fa''.

          pose proof (ind t (subst t n (mk_utoken a)) [n]) as ih.
          repeat (autodimp ih hyp); eauto 3 with slow.
          { rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (ih x [(a,a')]) as h; clear ih.
          allrw @nt_wf_fresh.
          repeat (autodimp h hyp); allsimpl; eauto 3 with slow.
          { apply disjoint_singleton_l; intro k.
            rw in_remove in k; repnd.
            apply get_utokens_subst in k; boolvar; allsimpl; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp. }

          rw @subst_ren_utokens in h.
          simpl in h; unfold ren_atom in h; allsimpl; boolvar; fold_terms; tcsp; GC.

          rw @ren_utokens_trivial in h; allsimpl; allrw disjoint_singleton_l; auto.

          pose proof (ind t (subst t n (mk_utoken a')) [n]) as ih.
          repeat (autodimp ih hyp).
          { rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (ih (ren_utokens [(a,a')] x) ren) as ch; clear ih.
          repeat (autodimp ch hyp); allsimpl; eauto 3 with slow.
          { allrw <- disjoint_diff_l.
            eapply disjoint_eqset_r;[apply eqset_sym;apply get_utokens_subst|].
            boolvar; simpl; allrw app_nil_r; auto.
            apply disjoint_app_r; dands; auto.
            apply disjoint_singleton_r.
            rw in_diff; sp. }

          rw @subst_ren_utokens in ch.
          rw @ren_utokens_utoken_not_in_dom in ch; auto.

          pose proof (ind t (subst (ren_utokens ren t) n (mk_utoken a')) [n]) as ih.
          repeat (autodimp ih hyp); eauto 3 with slow.
          { rw @simple_osize_subst; eauto 3 with slow.
            rw @osize_ren_utokens; eauto 3 with slow. }
          pose proof (ih (ren_utokens ren (ren_utokens [(a,a')] x)) [(a',a'')]) as ch'; clear ih.
          repeat (autodimp ch' hyp); allsimpl; eauto 3 with slow.
          { apply disjoint_singleton_l; intro k.
            rw in_remove in k; repnd.
            apply get_utokens_subst in k; boolvar; allsimpl; allrw app_nil_r; tcsp.
            allrw in_app_iff; allsimpl; repndors; tcsp. }

          rw @subst_ren_utokens in ch'.
          allsimpl; unfold ren_atom in ch'; allsimpl; boolvar; tcsp; GC; fold_terms.
          rw @ren_utokens_trivial in ch'; allsimpl; allrw disjoint_singleton_l; auto.
          rw ch'; simpl.

          f_equal; f_equal.
          repeat (rw @ren_utokens_ren_utokens); simpl.
          rw (compose_ren_utokens_trivial [(a',a'')] ren); simpl; allrw disjoint_singleton_l; auto.
          rw (ren_atom_app_weak_r ren [(a',a'')] a'); auto.
          unfold ren_atom; simpl; boolvar; tcsp; GC.
          rw app_comm_cons.
          rw @ren_utokens_app_weak_l; simpl; allrw disjoint_singleton_l; auto.

          applydup @compute_step_preserves_utokens in comp2; eauto 3 with slow;[].
          eapply subset_eqset_r in comp0;[|apply get_utokens_subst].

          apply (simple_ren_utokens_subst_utokens_eq1 _ _ _ _ _ (get_utokens t)); auto.
          { eapply subset_trans;[exact comp0|]; boolvar; simpl; allrw app_nil_r;
            allrw subset_app; dands; eauto with slow. }
          { introv i j; destruct fa''.
            rw @get_utokens_ren_utokens; rw in_map_iff; eexists; dands; eauto. }
      }

    + SCase "Exc".
      csunf comp; csunf; allsimpl; ginv.
      eexists; dands; eauto.

    + SCase "Abs".
      csunf comp; allsimpl.
      csunf; simpl.

      applydup @compute_step_lib_success in comp; exrepnd; subst.
      applydup @found_entry_implies_matching_entry in comp1; auto.
      unfold matching_entry in comp0; repnd.

      pose proof (compute_step_lib_success_change_bs
                    lib abs oa2
                    bs (map (ren_utokens_b ren) bs)
                    vars rhs correct) as h.
      repeat (autodimp h hyp);
        [ rw map_map; unfold compose; apply eq_maps;
          introv i; destruct x; unfold num_bvars; auto
        | ].
      rw h; clear h.
      unfold correct_abs in correct; repnd.
      rw @ren_utokens_mk_instance; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ren_utokens {o} :
  forall lib k (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> reduces_in_atmost_k_steps lib t u k
    -> reduces_in_atmost_k_steps lib (ren_utokens ren t) (ren_utokens ren u) k.
Proof.
  induction k; introv wf norep disj r.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup (compute_step_ren_utokens lib t u0 ren) in r1; auto.
    applydup @preserve_nt_wf_compute_step in r1; auto.
    apply (IHk _ _ ren) in r0; auto;[|].
    + eexists; dands; eauto.
    + introv i j.
      apply disj in i.
      destruct i.
      allrw in_diff; repnd; dands; auto.
      apply compute_step_preserves_utokens in r1; auto.
Qed.

Lemma reduces_to_ren_utokens {o} :
  forall lib (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> reduces_to lib t u
    -> reduces_to lib (ren_utokens ren t) (ren_utokens ren u).
Proof.
  introv wf norep disj r.
  allunfold @reduces_to; exrepnd.
  exists k.
  eapply reduces_in_atmost_k_steps_ren_utokens; eauto.
Qed.

Lemma isvalue_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    isvalue t
    -> isvalue (ren_utokens ren t).
Proof.
  introv isv.
  apply isvalue_implies in isv; repnd.
  apply iscan_implies in isv0; repndors; exrepnd; subst.
  - rw @ren_utokens_oterm.
    remember (get_utok (Can c)) as guo; symmetry in Heqguo; destruct guo.
    + apply get_utok_some in Heqguo; ginv.
      constructor; simpl; auto.
      apply (isprogram_ren_utokens ren) in isv.
      allsimpl; auto.
    + constructor; simpl; auto.
      apply (isprogram_ren_utokens ren) in isv.
      rw @ren_utokens_oterm in isv; rw Heqguo in isv; auto.
  - simpl; eauto 3 with slow.
Qed.
Hint Resolve isvalue_ren_utokens : slow.

Lemma computes_to_value_ren_utokens {o} :
  forall lib (t u : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_to_value lib t u
    -> computes_to_value lib (ren_utokens ren t) (ren_utokens ren u).
Proof.
  introv wf norep disj r.
  allunfold @computes_to_value; repnd; dands; eauto 2 with slow.
  eapply reduces_to_ren_utokens; auto.
Qed.

Fixpoint inv_utok_ren {o} (ren : @utok_ren o) : utok_ren :=
  match ren with
    | [] => []
    | (a,b) :: r => (b,a) :: inv_utok_ren r
  end.

Lemma inv_ren_atom {o} :
  forall (ren : @utok_ren o) a,
    no_repeats (range_utok_ren ren)
    -> !LIn a (diff (get_patom_deq o) (dom_utok_ren ren) (range_utok_ren ren))
    -> ren_atom (inv_utok_ren ren) (ren_atom ren a) = a.
Proof.
  induction ren; introv norep disj; allsimpl; tcsp.
  allrw no_repeats_cons; repnd; allsimpl.
  allrw @ren_atom_cons; boolvar; subst; tcsp.
  - pose proof (ren_atom_or ren a0) as x; repndors; tcsp.
  - pose proof (ren_atom_or ren a0) as x; repndors; tcsp.
    rw in_diff in disj; allsimpl.
    rw in_remove in disj.
    destruct (in_deq _ (get_patom_deq o) a0 (dom_utok_ren ren)) as [d|d].
    + apply in_dom_in_range in d; sp.
    + destruct disj; sp.
  - apply IHren; auto.
    intro k.
    destruct disj.
    allrw in_diff; repnd; dands; auto.
    allrw in_remove; sp.
  - apply IHren; auto.
    intro k.
    destruct disj.
    allrw in_diff; repnd; dands; auto.
    allsimpl.
    allrw in_remove; sp.
Qed.

Lemma inv_ren_utokens {o} :
  forall (t : @NTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> ren_utokens (inv_utok_ren ren) (ren_utokens ren t) = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; tcsp.
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

Lemma range_utok_ren_inv_utok_ren {o} :
  forall (ren : @utok_ren o),
    range_utok_ren (inv_utok_ren ren)
    = dom_utok_ren ren.
Proof.
  induction ren; allsimpl; tcsp.
  destruct a; allsimpl; f_equal; tcsp.
Qed.

Lemma dom_utok_ren_inv_utok_ren {o} :
  forall (ren : @utok_ren o),
    dom_utok_ren (inv_utok_ren ren)
    = range_utok_ren ren.
Proof.
  induction ren; allsimpl; tcsp.
  destruct a; allsimpl; f_equal; tcsp.
Qed.

Lemma disjoint_dom_diff_range_map_ren_atom {o} :
  forall atoms (ren : @utok_ren o),
    disjoint (dom_utok_ren ren)
             (diff (get_patom_deq o) (range_utok_ren ren)
                   (map (ren_atom ren) atoms)).
Proof.
  induction atoms; introv; allsimpl.
  - rw diff_nil; auto.
  - rw diff_cons_r; boolvar; tcsp.
    apply disjoint_cons_r; dands; tcsp.
    intro i; destruct n.
    pose proof (ren_atom_or ren a) as h; repndors; tcsp.
    rw h in i.
    apply in_dom_in_range in i; auto.
Qed.

Lemma inv_ren_atom2 {o} :
  forall (ren : @utok_ren o) a,
    no_repeats (dom_utok_ren ren)
    -> !LIn a (diff (get_patom_deq o) (range_utok_ren ren) (dom_utok_ren ren))
    -> ren_atom ren (ren_atom (inv_utok_ren ren) a) = a.
Proof.
  induction ren; introv norep disj; allsimpl; tcsp.
  allrw no_repeats_cons; repnd; allsimpl.
  allrw @ren_atom_cons; boolvar; subst; tcsp.
  - pose proof (ren_atom_or (inv_utok_ren ren) a0) as x; repndors; tcsp.
    allrw @range_utok_ren_inv_utok_ren; tcsp.
  - pose proof (ren_atom_or (inv_utok_ren ren) a0) as x; repndors; tcsp;
    allrw @range_utok_ren_inv_utok_ren; tcsp.
    rw in_diff in disj; allsimpl.
    rw in_remove in disj.
    destruct (in_deq _ (get_patom_deq o) a0 (range_utok_ren ren)) as [d|d]; tcsp.
    + rw <- @dom_utok_ren_inv_utok_ren in d.
      apply in_dom_in_range in d; sp.
      allrw @range_utok_ren_inv_utok_ren; tcsp.
    + destruct disj; sp.
  - apply IHren; auto.
    intro k.
    destruct disj.
    allrw in_diff; repnd; dands; auto.
    allrw in_remove; sp.
  - apply IHren; auto.
    intro k.
    destruct disj.
    allrw in_diff; repnd; dands; auto.
    allsimpl.
    allrw in_remove; sp.
Qed.

Lemma inv_ren_utokens2 {o} :
  forall (t : @NTerm o) ren,
    no_repeats (dom_utok_ren ren)
    -> disjoint (dom_utok_ren ren) (diff (get_patom_deq o) (range_utok_ren ren) (get_utokens t))
    -> ren_utokens ren (ren_utokens (inv_utok_ren ren) t) = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep disj; tcsp.
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

Lemma inv_ren_utokens_b2 {o} :
  forall (b : @BTerm o) ren,
    no_repeats (dom_utok_ren ren)
    -> disjoint (dom_utok_ren ren) (diff (get_patom_deq o) (range_utok_ren ren) (get_utokens_b b))
    -> ren_utokens_b ren (ren_utokens_b (inv_utok_ren ren) b) = b.
Proof.
  introv norep disj.
  destruct b as [l t]; allsimpl.
  f_equal; apply inv_ren_utokens2; auto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_utokens {o} :
  forall lib k (t u : @NTerm o),
    nt_wf t
    -> reduces_in_atmost_k_steps lib t u k
    -> subset (get_utokens u) (get_utokens t).
Proof.
  induction k; introv wf r.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @preserve_nt_wf_compute_step in r1; auto.
    apply compute_step_preserves_utokens in r1; auto.
    apply IHk in r0; auto.
Qed.

Lemma reduces_to_preserves_utokens {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> reduces_to lib t u
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv wf r.
  allunfold @reduces_to; exrepnd.
  eapply reduces_in_atmost_k_steps_preserves_utokens; eauto.
Qed.

Lemma computes_to_value_preserves_utokens {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> computes_to_value lib t u
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv wf r.
  allunfold @computes_to_value; repnd; dands; eauto 2 with slow.
  eapply reduces_to_preserves_utokens; eauto.
Qed.

Lemma alpha_eq_ren_utokens {o} :
  forall (t1 t2 : @NTerm o) ren,
    alpha_eq t1 t2
    -> alpha_eq (ren_utokens ren t1) (ren_utokens ren t2).
Proof.
  nterm_ind1s t1 as [v|f ind| op bs ind] Case; introv aeq.

  - Case "vterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "sterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst.
    allsimpl.
    apply alpha_eq_oterm_combine2; allrw map_length; dands; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
    applydup aeq0 in i1; allsimpl.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2]; allsimpl.
    inversion i0 as [? ? ? ? ? disj len1 len2 norep a]; subst; clear i0.
    apply (al_bterm _ _ lv); auto.
    + allrw @all_vars_ren_utokens; auto.
    + pose proof (lsubst_ren_utokens t1 (var_ren l1 lv) ren) as h1.
      rw @ren_utokens_sub_var_ren in h1.
      pose proof (lsubst_ren_utokens t2 (var_ren l2 lv) ren) as h2.
      rw @ren_utokens_sub_var_ren in h2.
      rw <- h1; rw <- h2.
      applydup in_combine in i1; repnd.
      pose proof (ind t1 (lsubst t1 (var_ren l1 lv)) l1 i2) as h; clear ind.
      autodimp h hyp.
      { rw @lsubst_allvars_preserves_osize; eauto with slow. }
Qed.

Lemma alpha_eq_bterm_ren_utokens_b {o} :
  forall (b1 b2 : @BTerm o) ren,
    alpha_eq_bterm b1 b2
    -> alpha_eq_bterm (ren_utokens_b ren b1) (ren_utokens_b ren b2).
Proof.
  introv aeq.
  pose proof (alpha_eq_ren_utokens (oterm Exc [b1]) (oterm Exc [b2]) ren) as h.
  autodimp h hyp.
  - constructor; allsimpl; auto.
    introv i; destruct n; tcsp.
  - allsimpl.
    inversion h as [|?|? ? ? len imp]; subst; allsimpl; GC.
    pose proof (imp 0) as k; autodimp k hyp.
Qed.

Lemma nt_wf_ren_utokens_iff {o} :
  forall (ren : @utok_ren o) (t : NTerm),
    nt_wf (ren_utokens ren t) <=> nt_wf t.
Proof.
  introv; split; introv k; try (apply nt_wf_ren_utokens; auto).

  revert k.
  nterm_ind t as [v|f ind|op bs ind] Case; introv w; allsimpl; auto.
  Case "oterm".
  allrw @nt_wf_oterm_iff; repnd; dands; auto.

  - allrw map_map; allunfold @compose.
    destruct op; allsimpl;
    try (complete (rw <- w0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto)).
    destruct c; allsimpl;
    try (complete (rw <- w0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto)).

  - introv i.
    pose proof (w (ren_utokens_b ren b)) as h.
    rw in_map_iff in h; autodimp h hyp; tcsp.
    + eexists; dands; eauto.
    + destruct b as [l t]; allsimpl.
      inversion h; subst; constructor.
      eapply ind; eauto.
Qed.

Lemma ex_new_utok_ren {o} :
  forall (atoms avoid : list (@get_patom_set o)),
    {ren : utok_ren
     & dom_utok_ren ren = atoms
     # disjoint avoid (range_utok_ren ren)
     # no_repeats (range_utok_ren ren)}.
Proof.
  induction atoms; introv; allsimpl.
  - exists ([] : @utok_ren o); simpl; sp.
  - pose proof (IHatoms avoid) as h; exrepnd.
    destruct (fresh_atom o (avoid ++ range_utok_ren ren)).
    allrw in_app_iff; allrw not_over_or; repnd.
    exists ((a,x) :: ren); simpl; rw h1; rw disjoint_cons_r; rw no_repeats_cons.
    dands; auto.
Qed.

Lemma lsubst_aux_ren_utokens2 {o} :
  forall (t : @NTerm o) ren ren' sub,
    no_repeats (range_utok_ren ren')
    -> dom_utok_ren ren' = dom_utok_ren ren
    -> disjoint (range_utok_ren ren') (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren') (get_utokens_sub sub)
    -> disjoint (range_utok_ren ren') (get_utokens t)
    -> lsubst_aux (ren_utokens ren t) sub
       = ren_utokens (ren ++ inv_utok_ren ren')
                     (lsubst_aux t (ren_utokens_sub ren' sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep eqdoms disj1 disj2 disj3; tcsp.

  - Case "vterm".
    allsimpl.
    rw @sub_find_ren_utokens_sub.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
    rw @ren_utokens_app_weak_r;
      [|rw @get_utokens_ren_utokens;
         introv i j; rw in_map_iff in j; exrepnd; subst;
         apply sub_find_some in Heqsf;
         unfold get_utokens_sub in disj2; apply disjoint_sym in disj2;
         apply in_sub_eta in Heqsf; repnd;
         disj_flat_map; apply Heqsf1 in j1;
         apply disjoint_sym in disj1; applydup disj1 in i;
         destruct (ren_atom_or ren' a) as [d|d]; tcsp;
         rw d in i; rw <- eqdoms in i; apply in_dom_in_range in i;
         complete sp].

    rw @inv_ren_utokens; auto.
    introv i j; rw in_diff in j.
    apply sub_find_some in Heqsf; apply in_sub_eta in Heqsf; repnd.
    unfold get_utokens_sub in disj2; apply disjoint_sym in disj2.
    disj_flat_map.
    apply Heqsf1 in j0; sp.

  - Case "oterm".
    allrw @lsubst_aux_oterm.
    allrw @ren_utokens_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold lsubst_bterms_aux.
      allrw map_map; unfold compose.
      allrw disjoint_cons_r; repnd.

      f_equal.

      * rw @ren_atom_app_weak_l; auto.
        rw @dom_utok_ren_inv_utok_ren; auto.

      * apply eq_maps; introv i; destruct x as [l t]; allsimpl.
        f_equal.
        rw @sub_filter_ren_utokens_sub.
        disj_flat_map; allsimpl.
        eapply ind; eauto.

        eapply subset_disjoint_r;[exact disj2|].
        apply get_utokens_sub_filter_subset.

    + simpl; f_equal; allsimpl.
      allrw disjoint_app_r; repnd.
      unfold lsubst_bterms_aux.
      allrw map_map; unfold compose.

      apply eq_maps; introv i; destruct x as [l t]; allsimpl.
      f_equal.
      rw @sub_filter_ren_utokens_sub.
      disj_flat_map; allsimpl.
      eapply ind; eauto.

      eapply subset_disjoint_r;[exact disj2|].
      apply get_utokens_sub_filter_subset.
Qed.

Lemma lsubst_ren_utokens2 {o} :
  forall (t : @NTerm o) ren ren' sub,
    no_repeats (range_utok_ren ren')
    -> dom_utok_ren ren' = dom_utok_ren ren
    -> disjoint (range_utok_ren ren') (dom_utok_ren ren)
    -> disjoint (range_utok_ren ren') (get_utokens_sub sub)
    -> disjoint (range_utok_ren ren') (get_utokens t)
    -> lsubst (ren_utokens ren t) sub
       = ren_utokens (ren ++ inv_utok_ren ren')
                     (lsubst t (ren_utokens_sub ren' sub)).
Proof.
  introv norep eqdoms disj1 disj2 disj3.
  unfold lsubst; allsimpl.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_ren_utokens_sub.
  rw @bound_vars_ren_utokens.
  rw @change_bvars_alpha_ren_utokens.
  boolvar; try (apply lsubst_aux_ren_utokens2; auto).
  t_change t'.
  apply alphaeq_preserves_utokens in h.
  rw <- h; auto.
Qed.

Lemma wf_sub_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren,
    wf_sub sub
    -> wf_sub (ren_utokens_sub ren sub).
Proof.
  induction sub; introv w; allsimpl; auto.
  destruct a; allrw @wf_sub_cons_iff; repnd; dands; tcsp.
  apply wf_term_ren_utokens; auto.
Qed.
Hint Resolve wf_sub_ren_utokens_sub : slow.

Lemma nt_wf_lsubst_aux_iff {o} :
  forall (t : @NTerm o) sub,
    nt_wf (lsubst_aux t sub)
    <=> (nt_wf t
         # forall v u,
             LIn v (free_vars t)
             -> sub_find sub v = Some u
             -> nt_wf u).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
    split; intro k; exrepnd; dands; tcsp.

    + introv i e; repndors; subst; tcsp.
      rw e in Heqsf; ginv; auto.

    + pose proof (k v n) as h; repeat (autodimp h hyp); exrepnd.

    + introv i e; repndors; subst; tcsp.
      rw e in Heqsf; ginv.

  - Case "sterm".
    split; intro h; repnd; dands; tcsp.

  - Case "oterm".
    allrw @nt_wf_oterm_iff.
    allrw map_map; unfold compose; split; intro k; exrepnd; dands; tcsp.

    + rw <- k0.
      apply eq_maps; introv i; destruct x as [l t]; unfold num_bvars; simpl; tcsp.

    + introv i.
      pose proof (k (lsubst_bterm_aux b sub)) as h.
      autodimp h hyp.
      { rw in_map_iff; eexists; dands; eauto. }
      destruct b as [l t]; allsimpl.
      allrw @bt_wf_iff.
      apply (ind t l) in h; sp.


    + introv i e.
      allrw lin_flat_map; exrepnd.
      pose proof (k (lsubst_bterm_aux x sub)) as h.
      autodimp h hyp.
      { rw in_map_iff; eexists; dands; eauto. }
      destruct x as [l t]; allsimpl.
      allrw @bt_wf_iff.
      allrw in_remove_nvars; repnd.
      apply (ind t l) in h; auto; repnd.
      eapply h in i2; eauto.
      rw @sub_find_sub_filter_eq; boolvar; tcsp.

    + rw <- k1.
      apply eq_maps; introv i; destruct x as [l t]; unfold num_bvars; simpl; tcsp.

    + introv i.
      rw in_map_iff in i; exrepnd; subst.
      destruct a as [l t]; allsimpl.
      applydup k0 in i1.
      allrw @bt_wf_iff.
      apply (ind t l); auto; dands; auto.
      introv i e.
      allrw @sub_find_sub_filter_eq; boolvar; tcsp.
      apply k in e; auto.
      rw lin_flat_map; eexists; dands; eauto.
      simpl; rw in_remove_nvars; sp.
Qed.

Lemma nt_wf_lsubst_iff {o} :
  forall (t : @NTerm o) sub,
    nt_wf (lsubst t sub)
    <=> (nt_wf t
         # forall v u,
             LIn v (free_vars t)
             -> sub_find sub v = Some u
             -> nt_wf u).
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  rw @nt_wf_lsubst_aux_iff; split; introv k; exrepnd; dands; tcsp.

  - apply alphaeq_preserves_wf in h1; apply h1; auto.

  - introv i j.
    apply alphaeq_preserves_free_vars in h1; rw h1 in i.
    eapply k; eauto.

  - apply alphaeq_preserves_wf in h1; apply h1; auto.

  - introv i j.
    apply alphaeq_preserves_free_vars in h1; rw <- h1 in i.
    eapply k; eauto.
Qed.

Lemma isprogram_lsubst_iff {o} :
  forall (t : @NTerm o) sub,
    isprogram (lsubst t sub)
    <=> (nt_wf t
         # forall v,
             LIn v (free_vars t)
             -> {u : NTerm
                 & sub_find sub v = Some u
                 # nt_wf u
                 # closed u}).
Proof.
  introv; unfold isprogram; split; intro k; repnd; dands.

  - apply lsubst_nt_wf in k; auto.

  - introv i.
    unfold closed in k0.
    pose proof (eqvars_free_vars_disjoint t sub) as h.
    rw k0 in h.
    apply eq_vars_nil in h.
    rw <- null_iff_nil in h.
    apply null_app in h; repnd.
    rw null_remove_nvars in h0.
    applydup h0 in i.
    apply in_dom_sub_exists in i0; exrepnd.
    unfold null in h.
    exists t0; dands; auto.

    + rw @nt_wf_lsubst_iff in k; repnd.
      eapply k in i; eauto.

    + unfold closed.
      rw <- null_iff_nil.
      unfold null; introv j.
      pose proof (h x) as q; destruct q.
      apply in_sub_free_vars_iff.
      exists v t0; dands; auto.
      apply in_sub_keep_first; dands; auto.

  - unfold closed.
    pose proof (eqvars_free_vars_disjoint t sub) as h.
    rw <- null_iff_nil.
    unfold null; introv i.
    rw eqvars_prop in h; apply h in i; clear h.
    rw in_app_iff in i; rw in_remove_nvars in i; repndors; exrepnd.

    + applydup k in i0; exrepnd.
      apply sub_find_some in i1.
      apply in_sub_eta in i1; sp.

    + apply in_sub_free_vars in i; exrepnd.
      apply in_sub_keep_first in i0; repnd.
      applydup k in i0; exrepnd.
      rw i2 in i3; ginv.
      rw i4 in i1; allsimpl; tcsp.

  - apply nt_wf_lsubst_iff; dands; auto.
    introv i j.
    apply k in i; exrepnd.
    rw i1 in j; ginv; auto.
Qed.

Lemma range_utok_ren_app {o} :
  forall ren1 ren2 : @utok_ren o,
    range_utok_ren (ren1 ++ ren2)
    = range_utok_ren ren1 ++ range_utok_ren ren2.
Proof.
  introv.
  unfold range_utok_ren.
  rw map_app; sp.
Qed.

Lemma prog_sub_implies_cl_sub {o} :
  forall (sub : @Sub o),
    prog_sub sub -> cl_sub sub.
Proof.
  unfold prog_sub, cl_sub, sub_range_sat; introv k i.
  apply k in i.
  destruct i; auto.
Qed.
Hint Resolve prog_sub_implies_cl_sub : slow.

Lemma isprogram_lsubst_aux_prog {o} :
  forall (t : @NTerm o) (sub : Substitution),
    isprogram t
    -> prog_sub sub
    -> isprogram (lsubst_aux t sub).
Proof.
  introv ispt isps.
  rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
  apply isprogram_lsubst3; auto.
Qed.
Hint Resolve isprogram_lsubst_aux_prog : slow.

Lemma isvalue_lsubst_implies {o} :
  forall (t : @NTerm o) sub,
    isvalue (lsubst t sub)
    -> (
         (iscan t
          # nt_wf t
          # forall v,
              LIn v (free_vars t)
              -> {u : NTerm
                  & sub_find sub v = Some u
                  # isprogram u})
         [+]
         {v : NVar
          & {u : NTerm
          & t = mk_var v
          # sub_find sub v = Some u
          # isvalue u}}
       ).
Proof.
  introv isv.
  apply isvalue_implies in isv; repnd.
  apply isprogram_lsubst_iff in isv; allsimpl; repnd.
  destruct t as [v|f|op bs]; allsimpl.

  - right.
    allunfold @lsubst; allsimpl.
    pose proof (isv v) as h; clear isv; autodimp h hyp; exrepnd.
    allrw h1.
    exists v u; dands; auto.
    apply isvalue_iff; dands; auto.
    split; auto.

  - left; dands; eauto 3 with slow; tcsp.

  - dopid op as [can|ncan|exc|abs] Case; tcsp; GC;
    try (complete (unfold lsubst in isv0; allsimpl; boolvar; inversion isv0)).
    left; dands; auto.
    introv i; apply isv in i; exrepnd.
    exists u; dands; auto.
    split; auto.
Qed.

Lemma nt_wf_sterm_implies_isprogram {o} :
  forall (f : @ntseq o), nt_wf (sterm f) -> isprogram (sterm f).
Proof.
  introv wf.
  rw @nt_wf_sterm_iff in wf.
  repeat constructor; simpl; try (complete (pose proof (wf n) as h; tcsp)).
Qed.
Hint Resolve nt_wf_sterm_implies_isprogram : slow.

Lemma nt_wf_sterm_implies_isvalue {o} :
  forall (f : @ntseq o), nt_wf (sterm f) -> isvalue (sterm f).
Proof.
  introv wf.
  constructor; simpl; eauto 3 with slow.
Qed.
Hint Resolve nt_wf_sterm_implies_isvalue : slow.

Lemma isvalue_lsubst_iff {o} :
  forall (t : @NTerm o) sub,
    isvalue (lsubst t sub)
    <=> (
         (iscan t
          # nt_wf t
          # forall v,
              LIn v (free_vars t)
              -> {u : NTerm
                  & sub_find sub v = Some u
                  # isprogram u})
         [+]
         {v : NVar
          & {u : NTerm
          & t = mk_var v
          # sub_find sub v = Some u
          # isvalue u}}
       ).
Proof.
  introv; split; introv k; try (apply isvalue_lsubst_implies; auto).
  repndors; repnd.
  - apply iscan_implies in k0; repndors; exrepnd; subst; allsimpl.

    + apply isvalue_iff; dands.
      * unfold lsubst; simpl; boolvar; tcsp.
      * apply isprogram_lsubst_iff; dands; auto.
        introv i; allsimpl; apply k in i; exrepnd.
        destruct i0.
        exists u; dands; auto.

    + unfold lsubst; simpl; eauto 3 with slow.

  - exrepnd; subst.
    unfold lsubst; simpl; rw k2; auto.
Qed.

Lemma computes_to_value_change_utok_sub {o} :
  forall lib (t u : @NTerm o) (sub sub' : Sub),
    nt_wf t
    -> computes_to_value lib (lsubst t sub) u
    -> nr_ut_sub t sub
    -> nr_ut_sub t sub'
    -> dom_sub sub = dom_sub sub'
    -> disjoint (get_utokens_sub sub) (get_utokens t)
    -> disjoint (get_utokens_sub sub') (get_utokens t)
    -> {w, s : NTerm
        $ alpha_eq u (lsubst w sub)
        # disjoint (get_utokens_sub sub) (get_utokens w)
        # subvars (free_vars w) (free_vars t)
        # subset (get_utokens w) (get_utokens t)
        # computes_to_value lib (lsubst t sub') s
        # alpha_eq s (lsubst w sub')}.
Proof.
  introv wf comp nr1 nr2 e d1 d2.
  allunfold @computes_to_value; repnd.
  eapply reduces_to_change_utok_sub in comp0; eauto.
  exrepnd.
  eexists; eexists; dands; eauto.
  apply alpha_eq_sym in comp0; apply alpha_preserves_value in comp0; auto.
  apply alpha_preserves_value in comp1; auto.
  apply isvalue_lsubst_iff in comp1; apply isvalue_lsubst_iff.
  repndors; exrepnd; subst.
  - left; dands; auto.
    introv i; apply comp1 in i; exrepnd.
    pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v t nr2 e) as h.
    rw i1 in h; exrepnd.
    eexists; dands; eauto with slow.
  - right.
    pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v t nr2 e) as h.
    rw comp7 in h; exrepnd.
    exists v (mk_utoken a); dands; eauto with slow.
Qed.

 (*
 Lemma alpha_eq_swap_lsubst_aux_var_ren {o} :
   forall (t : @NTerm o) vs1 vs2,
@@ -3076,278 +473,6 @@ Proof.
 Qed.
 *)

Lemma in_nrut_sub_or {o} :
  forall l a (sub : @Sub o),
    nrut_sub l sub
    -> no_repeats (dom_sub sub)
    -> (
         {v : NVar & sub_find sub v = Some (mk_utoken a)}
         [+]
         !LIn a (get_utokens_sub sub)
       ).
Proof.
  induction sub; introv nrut nr; allsimpl; tcsp.
  - right; sp.
  - destruct a0 as [v t].
    allrw @nrut_sub_cons; exrepnd; subst.
    allsimpl.
    allrw no_repeats_cons; repnd.
    destruct (get_patom_deq o a a0) as [x|x]; subst; tcsp.
    + left; exists v; boolvar; tcsp.
    + repeat (autodimp IHsub hyp).
      repndors; exrepnd; tcsp; GC.
      * destruct (deq_nvar v v0) as [y|y]; subst; tcsp.
        { apply sub_find_some in IHsub0; apply in_sub_eta in IHsub0; sp. }
        left; exists v0; boolvar; tcsp.
      * right; intro k; repndors; tcsp.
Qed.

Definition bound_vars_bterms {o} (bs : list (@BTerm o)) :=
  flat_map bound_vars_bterm bs.

Definition alpha_eq_bterms {o} (bs1 bs2 : list (@BTerm o)) :=
  length bs1 = length bs2
  # forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> alpha_eq_bterm b1 b2.

Lemma alpha_eq_bterms_cons {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    alpha_eq_bterms (b1 :: bs1) (b2 :: bs2)
    <=> (alpha_eq_bterm b1 b2 # alpha_eq_bterms bs1 bs2).
Proof.
  introv.
  unfold alpha_eq_bterms; simpl; split; introv k; repnd; dands; cpx.
  introv i; repndors; cpx.
Qed.

Lemma alpha_eq_bterms_refl {o} :
  forall (bs : list (@BTerm o)),
    alpha_eq_bterms bs bs.
Proof.
  induction bs; auto.
  - unfold alpha_eq_bterms; simpl; sp.
  - apply alpha_eq_bterms_cons; dands; eauto with slow.
Qed.
Hint Resolve alpha_eq_bterms_refl : slow.

Lemma alpha_eq_bterms_sym {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2
    -> alpha_eq_bterms bs2 bs1.
Proof.
  induction bs1; destruct bs2; introv aeq; auto.
  - unfold alpha_eq_bterms in aeq; allsimpl; sp.
  - unfold alpha_eq_bterms in aeq; allsimpl; sp.
  - allrw @alpha_eq_bterms_cons; repnd; dands; eauto with slow.
Qed.
Hint Resolve alpha_eq_bterms_sym : slow.

Lemma alpha_eq_bterms_trans {o} :
  forall (bs1 bs2 bs3 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2
    -> alpha_eq_bterms bs2 bs3
    -> alpha_eq_bterms bs1 bs3.
Proof.
  induction bs1; destruct bs2; introv aeq1 aeq2; auto.
  - unfold alpha_eq_bterms in aeq1; allsimpl; sp.
  - unfold alpha_eq_bterms in aeq1; allsimpl; sp.
  - destruct bs3; allsimpl; tcsp.
    + unfold alpha_eq_bterms in aeq2; allsimpl; sp.
    + allrw @alpha_eq_bterms_cons; repnd; dands; eauto with slow.
Qed.
Hint Resolve alpha_eq_bterms_trans : slow.

Lemma pull_out_nrut_sub {o} :
  forall (t : @NTerm o) sub l,
    nrut_sub l sub
    -> no_repeats (dom_sub sub)
    -> wf_term t
    -> disjoint (free_vars t) (dom_sub sub)
    -> {u : NTerm
        & alpha_eq t (lsubst u sub)
        # disjoint (get_utokens_sub sub) (get_utokens u)
        # disjoint (bound_vars u) (dom_sub sub)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv nrut nr wf disj.

  - Case "vterm".
    allsimpl; allrw disjoint_singleton_l.
    exists (@mk_var o v); dands; allsimpl; tcsp.
    rw @cl_lsubst_lsubst_aux; simpl; eauto 2 with slow.
    rw @sub_find_none_if; auto.

  - Case "sterm".
    allsimpl.
    exists (sterm f); simpl; dands; auto.

  - Case "oterm".
    allsimpl.

    destruct (dec_op_eq_ntok op) as [x|x].

    {
      exrepnd; subst.
      apply wf_term_utok in wf; subst; allsimpl; fold_terms.
      pose proof (in_nrut_sub_or l a sub nrut nr) as h.
      repndors; exrepnd.
      - exists (@mk_var o v); simpl; dands; auto.
        rw @cl_lsubst_lsubst_aux; eauto 3 with slow.
        simpl; rw h0; auto.
      - exists (mk_utoken a).
        rw @cl_lsubst_lsubst_aux; eauto 3 with slow.
        simpl; dands; auto.
        apply disjoint_singleton_r; auto.
    }

    assert {bs' : list BTerm
            & alpha_eq_bterms bs (lsubst_bterms_aux bs' sub)
            # disjoint (get_utokens_sub sub) (get_utokens_bs bs')
            # disjoint (bound_vars_bterms bs') (dom_sub sub)}
      as h.
    {
      rw @wf_oterm_iff in wf; repnd.
      clear wf0.
      induction bs; allsimpl; tcsp.

      - exists ([] : list (@BTerm o)); simpl; dands; eauto with slow.

      - allrw disjoint_app_l; repnd.
        repeat (autodimp IHbs hyp).
        { introv j s nrut' nr' d; eapply ind; eauto. }
        exrepnd.
        destruct a as [vs t].
        pose proof (fresh_vars (length vs) (vs ++ dom_sub sub ++ all_vars t))
          as fvs; exrepnd.
        allrw disjoint_app_r; repnd.

        pose proof (ind t (lsubst t (var_ren vs lvn)) vs) as h; clear ind; repeat (autodimp h hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }
        pose proof (h sub l) as k; clear h.
        allsimpl.
        repeat (autodimp k hyp); eauto 3 with slow.
        { pose proof (wf (bterm vs t)) as w; autodimp w hyp.
          apply wf_bterm_iff in w.
          apply lsubst_preserves_wf_term; eauto with slow. }
        { introv i j.
          pose proof (eqvars_free_vars_disjoint t (var_ren vs lvn)) as e.
          rw eqvars_prop in e; apply e in i; clear e.
          rw @dom_sub_var_ren in i; auto.
          rw in_app_iff in i; repndors.
          - apply disj0 in i; sp.
          - apply in_sub_free_vars in i; exrepnd.
            apply in_sub_keep_first in i0; repnd.
            apply sub_find_some in i2.
            apply in_var_ren in i2; exrepnd; subst; allsimpl; repndors; tcsp; subst.
            apply fvs4 in i4; sp. }
        exrepnd.

        exists (bterm lvn u :: bs').
        simpl; dands; eauto 3 with slow.
        + apply alpha_eq_bterms_cons; dands; auto.
          pose proof (alpha_bterm_change (bterm vs t) vs t lvn) as h.
          repeat (autodimp h hyp).
          { allrw disjoint_app_l; dands; eauto with slow. }
          eapply alpha_eq_bterm_trans;[exact h|].
          apply alpha_eq_bterm_congr; auto.
          rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
          rw @sub_filter_disjoint1; eauto 2 with slow.

        + apply disjoint_app_r; dands; auto.

        + allrw disjoint_app_l; dands; eauto 2 with slow.
    }

    exrepnd.
    exists (oterm op bs').
    dands; auto.

    + rw @cl_lsubst_lsubst_aux; eauto 2 with slow.
      simpl.
      unfold alpha_eq_bterms, lsubst_bterms_aux in h1; repnd.
      apply alpha_eq_oterm_combine; allrw map_length; dands; auto.

    + simpl.
      rw disjoint_app_r; dands; auto.
      rw @get_utok_none; auto.
      destruct op; tcsp.
      destruct c; tcsp; allsimpl.
      destruct x; eexists; eauto.
Qed.

Ltac dgc :=
  repeat match goal with
           | [ H : subset [] _   |- _ ] => clear H
           | [ H : subvars [] _  |- _ ] => clear H
           | [ H : disjoint [] _ |- _ ] => clear H
           | [ H : disjoint _ [] |- _ ] => clear H
         end.

Lemma nrut_sub_sub_find_same {o} :
  forall (sub : @Sub o) v1 v2 t l,
    nrut_sub l sub
    -> sub_find sub v1 = Some t
    -> sub_find sub v2 = Some t
    -> {a : get_patom_set o
        & t = mk_utoken a
        # v1 = v2}.
Proof.
  induction sub; introv nr sf1 sf2; allsimpl; ginv.
  destruct a as [v u]; allrw @nrut_sub_cons; exrepnd; subst; allsimpl.
  boolvar; ginv; tcsp.
  - exists a; sp.
  - apply sub_find_some in sf2.
    dup sf2 as i.
    eapply in_nrut_sub in i; eauto; exrepnd; ginv.
    unfold get_utokens_sub in nr2.
    apply in_sub_eta in sf2; repnd.
    destruct nr2.
    rw lin_flat_map.
    exists (mk_utoken a0); simpl; sp.
  - apply sub_find_some in sf1.
    dup sf1 as i.
    eapply in_nrut_sub in i; eauto; exrepnd; ginv.
    unfold get_utokens_sub in nr2.
    apply in_sub_eta in sf1; repnd.
    destruct nr2.
    rw lin_flat_map.
    exists (mk_utoken a0); simpl; sp.
  - pose proof (IHsub v1 v2 t l); sp.
Qed.

Lemma in_nth_combine :
  forall A B (l1 : list A) (l2 : list B) n d1 d2,
    length l1 = length l2
    -> n < length l1
    -> LIn (nth n l1 d1, nth n l2 d2) (combine l1 l2).
Proof.
  induction l1; destruct l2; introv len k; allsimpl; tcsp.
  destruct n; cpx.
Qed.

Lemma in_nth_combine_iff :
  forall A B d1 d2 (l1 : list A) (l2 : list B) x1 x2,
    LIn (x1,x2) (combine l1 l2)
    <=> {n : nat
         & x1 = nth n l1 d1
         # x2 = nth n l2 d2
         # n < length l1
         # n < length l2}.
Proof.
  induction l1; destruct l2; introv; simpl; split; introv k; exrepnd; tcsp.
  - repndors; cpx.
    + exists 0; dands; auto; try omega.
    + rw IHl1 in k; exrepnd; subst.
      exists (S n); dands; auto; try omega.
  - destruct n; cpx; subst; tcsp.
    right.
    apply IHl1.
    exists n; dands; auto.
Qed.

Lemma length_lsubst_bterms_aux {o} :
  forall (bs : list (@BTerm o)) sub,
    length (lsubst_bterms_aux bs sub) = length bs.
Proof.
  introv; unfold lsubst_bterms_aux; rw map_length; auto.
Qed.

Lemma selectbt_lsubst_bterms_aux {o} :
  forall (bs : list (@BTerm o)) sub n,
    n < length bs
    -> selectbt (lsubst_bterms_aux bs sub) n
       = lsubst_bterm_aux (selectbt bs n) sub.
Proof.
  introv x.
  unfold lsubst_bterms_aux.
  rw @selectbt_map; auto.
Qed.

Lemma no_repeats_diff_if :
  forall T deq (l1 l2 : list T),
    no_repeats l2
    -> no_repeats (diff deq l1 l2).
Proof.
  induction l2; introv nr; allsimpl; tcsp.
  - rw diff_nil; auto.
  - allrw diff_cons_r; allrw no_repeats_cons; repnd.
    autodimp IHl2 hyp.
    boolvar; tcsp.
    apply no_repeats_cons; dands; auto.
    rw in_diff; tcsp.
Qed.

Lemma no_repeats_remove_nvars_if :
  forall (l1 l2 : list NVar),
    no_repeats l2
    -> no_repeats (diff deq_nvar l1 l2).
Proof.
  introv nr.
  apply no_repeats_diff_if; auto.
Qed.


Definition get_bound_vars {o} (b : @BTerm o) :=
  match b with
    | bterm vs _ => vs
  end.

Lemma pull_out_nrut_sub_b_aux {o} :
  forall (b : @BTerm o) sub l fvs,
    nrut_sub l sub
    -> no_repeats (dom_sub sub)
    -> wf_bterm b
    -> disjoint (free_vars_bterm b) (dom_sub sub)
    -> disjoint fvs (free_vars_bterm b)
    -> disjoint fvs (bound_vars_bterm b)
    -> disjoint fvs (dom_sub sub)
    -> length fvs = num_bvars b
    -> no_repeats fvs
    -> {u : BTerm
        & alpha_eq_bterm b (lsubst_bterm_aux u sub)
        # disjoint (get_utokens_sub sub) (get_utokens_b u)
        # disjoint (bound_vars_bterm u) (dom_sub sub)
        # get_bound_vars u = fvs}.
Proof.
  introv nrut norep wf disj disj1 disj2 disj3 len nr.
  destruct b as [vs t]; allsimpl.
  allrw disjoint_app_r; repnd.

  pose proof (pull_out_nrut_sub (lsubst t (var_ren vs fvs)) sub l) as h.
  repeat (autodimp h hyp).
  { apply wf_bterm_iff in wf.
    apply lsubst_preserves_wf_term; eauto with slow. }
  { introv i j.
    pose proof (eqvars_free_vars_disjoint t (var_ren vs fvs)) as e.
    rw eqvars_prop in e; apply e in i; clear e.
    rw @dom_sub_var_ren in i; auto.
    rw in_app_iff in i; repndors.
    - apply disj in i; sp.
    - apply in_sub_free_vars in i; exrepnd.
      apply in_sub_keep_first in i0; repnd.
      apply sub_find_some in i2.
      apply in_var_ren in i2; exrepnd; subst; allsimpl; repndors; tcsp; subst.
      apply disj3 in i4; sp. }
  exrepnd.

  exists (bterm fvs u).
  simpl; dands; eauto 3 with slow.

  - pose proof (alpha_bterm_change (bterm vs t) vs t fvs) as h.
    repeat (autodimp h hyp).
    { allrw disjoint_app_l; dands; eauto 3 with slow.
      introv i j.
      applydup disj1 in j; rw in_remove_nvars in j0; destruct j0; dands; auto. }
    eapply alpha_eq_bterm_trans;[exact h|].
    apply alpha_eq_bterm_congr; auto.
    rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
    rw @sub_filter_disjoint1; eauto 2 with slow.

  - allrw disjoint_app_l; dands; eauto 3 with slow.
Qed.

Lemma pull_out_nrut_sub_b {o} :
  forall (b : @BTerm o) sub l,
    nrut_sub l sub
    -> no_repeats (dom_sub sub)
    -> wf_bterm b
    -> disjoint (free_vars_bterm b) (dom_sub sub)
    -> {u : BTerm
        & alpha_eq_bterm b (lsubst_bterm_aux u sub)
        # disjoint (get_utokens_sub sub) (get_utokens_b u)
        # disjoint (bound_vars_bterm u) (dom_sub sub)}.
Proof.
  introv nrut norep wf disj.
  destruct b as [vs t]; allsimpl.

  pose proof (fresh_vars (length vs) (vs ++ dom_sub sub ++ all_vars t))
    as fvs; exrepnd.
  allrw disjoint_app_r; repnd.

  pose proof (pull_out_nrut_sub_b_aux (bterm vs t) sub l lvn) as h.
  allsimpl; repeat (autodimp h hyp).
  - introv i j; rw in_remove_nvars in j; repnd.
    apply fvs5 in i; sp.
  - apply disjoint_app_r; dands; auto.
  - exrepnd; eexists; eauto.
Qed.

Lemma alphaeqbt_preserves_nt_wf {o} :
  forall l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> (nt_wf t2 <=> nt_wf t1).
Proof.
  introv aeq.
  apply alphaeqbt_preserves_wf in aeq.
  allrw @bt_wf_iff; auto.
Qed.

Lemma alpha_eq_bterm_preserves_wf_bterm {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> wf_bterm b1
    -> wf_bterm b2.
Proof.
  introv aeq w.
  destruct b1 as [l1 t1].
  destruct b2 as [l2 t2].
  allrw @wf_bterm_iff.
  apply alphaeqbt_preserves_nt_wf in aeq.
  allrw @wf_term_eq.
  apply aeq; auto.
Qed.

Lemma wf_bterm_lsubst_bterm_aux {o} :
  forall (b : @BTerm o) sub,
    wf_sub sub
    -> wf_bterm b
    -> wf_bterm (lsubst_bterm_aux b sub).
Proof.
  introv ws wb.
  destruct b as [l t]; allsimpl.
  allrw @wf_bterm_iff.
  apply lsubst_aux_preserves_wf_term2; eauto with slow.
Qed.

Definition wf_bterms {o} (bs : list (@BTerm o)) :=
  forall b, LIn b bs -> wf_bterm b.

Lemma wf_bterm_default_bt {o} : @wf_bterm o default_bt.
Proof.
  unfold default_bt.
  rw @wf_bterm_iff; eauto with slow.
Qed.
Hint Resolve wf_bterm_default_bt : slow.

Lemma wf_bterms_cons {o} :
  forall (b : @BTerm o) bs,
    wf_bterms (b :: bs) <=> (wf_bterm b # wf_bterms bs).
Proof.
   introv; split; intro k; dands; auto.
   - unfold wf_bterms in k; simpl in k; eapply k; eauto.
   - unfold wf_bterms in k; simpl in k.
     unfold wf_bterms; introv i; eapply k; eauto.
   - repnd; allunfold @wf_bterms; introv i; allsimpl; repndors; subst; tcsp.
Qed.

Lemma wf_bterm_selectbt {o} :
  forall (bs : list (@BTerm o)) n,
    wf_bterms bs
    -> wf_bterm (selectbt bs n).
Proof.
  induction bs; introv w; allsimpl; tcsp.
  - unfold selectbt; simpl; destruct n; eauto with slow.
  - allrw @wf_bterms_cons; repnd.
    rw @selectbt_cons.
    destruct (beq_nat n 0); auto.
Qed.

Lemma wf_bterm_lsubst_bterm_aux_implies {o} :
  forall (b : @BTerm o) sub,
    wf_bterm (lsubst_bterm_aux b sub)
    -> wf_bterm b.
Proof.
  introv wb.
  destruct b as [l t]; allsimpl.
  allrw @wf_bterm_iff.
  remember (sub_filter sub l) as sub'; clear dependent sub; clear l.
  rename sub' into sub.
  revert sub wb.

  nterm_ind t as [v|f ind|op bs ind] Case; introv w; allsimpl; eauto 2 with slow.
  Case "oterm".
  allrw @wf_oterm_iff; allrw map_map; allunfold @compose; repnd.
  rw <- w0; dands.

  - apply eq_maps; introv i; destruct x as [l t]; unfold num_bvars; sp.

  - introv i.
    pose proof (w (lsubst_bterm_aux b sub)) as h; clear w w0.
    autodimp h hyp.
    { rw in_map_iff; eexists; dands; eauto. }
    destruct b as [l t]; allsimpl.
    allrw @wf_bterm_iff.
    eapply ind; eauto.
Qed.

Lemma wf_bterms_lsubst_bterms_aux_implies {o} :
  forall (bs : list (@BTerm o)) sub,
    wf_bterms (lsubst_bterms_aux bs sub)
    -> wf_bterms bs.
Proof.
  introv w i.
  apply (wf_bterm_lsubst_bterm_aux_implies b sub).
  apply w.
  unfold lsubst_bterms_aux; rw in_map_iff.
  eexists; dands; eauto.
Qed.

Lemma alpha_eq_bterms_preserves_wf_bterms {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2
    -> wf_bterms bs1
    -> wf_bterms bs2.
Proof.
  introv aeq w i.
  unfold alpha_eq_bterms in aeq; repnd.
  pose proof (combine_in_right _ _ bs2 bs1) as h.
  autodimp h hyp; try omega.
  applydup h in i; clear h; exrepnd.
  applydup in_combine in i1; repnd.
  pose proof (w u1) as k; autodimp k hyp.
  apply aeq in i1.
  apply alpha_eq_bterm_preserves_wf_bterm in i1; auto.
Qed.

Lemma free_vars_bterm_lsubst_bterm_aux_nrut_sub {o} :
  forall (b : @BTerm o) sub l,
    nrut_sub l sub
    -> free_vars_bterm (lsubst_bterm_aux b sub)
       = remove_nvars (dom_sub sub) (free_vars_bterm b).
Proof.
  introv nrut.
  destruct b; simpl.
  rw @free_vars_lsubst_aux_cl; eauto 3 with slow.
  rw <- @dom_sub_sub_filter.
  rw <- remove_nvars_comp.
  rw remove_nvars_comm; auto.
Qed.

Lemma free_vars_bterms_lsubst_bterms_aux_nrut_sub {o} :
  forall (bs : list (@BTerm o)) sub l,
    nrut_sub l sub
    -> free_vars_bterms (lsubst_bterms_aux bs sub)
       = remove_nvars (dom_sub sub) (free_vars_bterms bs).
Proof.
  induction bs; introv nrut; allsimpl.
  - rw remove_nvars_nil_r; auto.
  - rw remove_nvars_app_r; f_equal; tcsp.
    + eapply free_vars_bterm_lsubst_bterm_aux_nrut_sub; eauto.
    + eapply IHbs; eauto.
Qed.

Lemma alpha_eq_bterms_preserves_free_vars {o} :
  forall bs1 bs2 : list (@BTerm o),
    alpha_eq_bterms bs1 bs2
    -> free_vars_bterms bs1 = free_vars_bterms bs2.
Proof.
  induction bs1; destruct bs2; introv aeq; allsimpl; tcsp.
  - unfold alpha_eq_bterms in aeq; allsimpl; tcsp.
  - unfold alpha_eq_bterms in aeq; allsimpl; tcsp.
  - allrw @alpha_eq_bterms_cons; repnd.
    f_equal; tcsp.
    apply alpha_eq_bterm_preserves_free_vars; auto.
Qed.

Lemma closed_oterm_iff1 {o} :
  forall (op : @Opid o) (bs : list BTerm),
    closed (oterm op bs) <=> null (free_vars_bterms bs).
Proof.
  introv.
  rw @closed_nt.
  unfold null; split; intro k.
  - introv i.
    unfold free_vars_bterms in i.
    rw lin_flat_map in i; exrepnd.
    apply k in i1; rw i1 in i0; allsimpl; sp.
  - introv i.
    unfold closed_bt.
    apply null_iff_nil; unfold null; introv j.
    pose proof (k x) as h; destruct h.
    unfold free_vars_bterms; rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma lsubst_aux_bterm_ren_utokens_b {o} :
  forall (b : @BTerm o) (sub : Sub) (ren : utok_ren),
    ren_utokens_b ren (lsubst_bterm_aux b sub)
    = lsubst_bterm_aux (ren_utokens_b ren b) (ren_utokens_sub ren sub).
Proof.
  introv.
  destruct b as [l t]; simpl.
  f_equal.
  rw @lsubst_aux_ren_utokens.
  rw @sub_filter_ren_utokens_sub; auto.
Qed.

Lemma ren_utokens_b_trivial {o} :
  forall (ren : utok_ren) (b : @BTerm o),
    disjoint (dom_utok_ren ren) (get_utokens_b b)
    -> ren_utokens_b ren b = b.
Proof.
  introv d.
  destruct b as [l t]; allsimpl.
  rw @ren_utokens_trivial; auto.
Qed.

Lemma dom_utok_ren_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> length sub1 = length sub2
    -> dom_utok_ren (nrut_subs_to_utok_ren sub1 sub2)
       = get_utokens_sub sub1.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 e; tcsp.
  - allsimpl; tcsp.
  - destruct a as [v t].
    destruct p as [z u].
    allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx.
    erewrite IHsub1; eauto.
Qed.

Lemma ren_utok_op_cons_weak {o} :
  forall (op : @Opid o) a1 a2 ren,
    !LIn a1 (get_utokens_o op)
    -> ren_utok_op ((a1, a2) :: ren) op
       = ren_utok_op ren op.
Proof.
  introv ni.
  destruct op; tcsp.
  destruct c; tcsp.
  allsimpl; allrw not_over_or; repnd.
  unfold ren_atom; simpl; boolvar; tcsp.
Qed.

Lemma ren_utokens_cons_weak {o} :
  forall (t : @NTerm o) a1 a2 ren,
    !LIn a1 (get_utokens t)
    -> ren_utokens ((a1, a2) :: ren) t = ren_utokens ren t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv ni; allsimpl; auto.
  Case "oterm".
  allrw in_app_iff; allrw not_over_or; repnd.
  rw @ren_utok_op_cons_weak; auto.
  f_equal.
  apply eq_maps; introv i; destruct x as [l t]; allsimpl.
  f_equal; eapply ind; eauto.
  intro k.
  destruct ni.
  rw lin_flat_map; eexists; dands; eauto.
Qed.

Lemma ren_utokens_sub_cons_weak {o} :
  forall (sub : @Sub o) a1 a2 ren,
    !LIn a1 (get_utokens_sub sub)
    -> ren_utokens_sub ((a1, a2) :: ren) sub = ren_utokens_sub ren sub.
Proof.
  induction sub; introv i; allsimpl; tcsp.
  destruct a as [v t]; allsimpl.
  unfold get_utokens_sub in i; allsimpl; try (fold (get_utokens_sub sub) in i).
  allrw in_app_iff; allrw not_over_or; repnd.
  rw IHsub; auto.
  f_equal; f_equal.
  apply ren_utokens_cons_weak; auto.
Qed.

Lemma ren_utokens_sub_nrut_subs_to_utok_ren {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> dom_sub sub1 = dom_sub sub2
    -> ren_utokens_sub (nrut_subs_to_utok_ren sub1 sub2) sub1
       = sub2.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 eqdoms;
  try (complete (allsimpl; sp)).
  destruct a as [v1 t1].
  destruct p as [v2 t2].
  allrw @nrut_sub_cons; exrepnd; subst; allsimpl; cpx; fold_terms.
  f_equal.
  - unfold ren_atom; simpl; boolvar; tcsp.
  - rw @ren_utokens_sub_cons_weak; auto.
    eapply IHsub1; eauto.
Qed.

Lemma alpha_eq_bterm_preserves_isprogram_bt {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> isprogram_bt b1
    -> isprogram_bt b2.
Proof.
  introv aeq isp.
  destruct b1 as [l1 t1].
  destruct b2 as [l2 t2].
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst; clear aeq.
  allunfold @isprogram_bt; repnd; allsimpl.
  applydup @alphaeq_preserves_free_vars in a.
  applydup @alphaeq_preserves_wf in a.
  allrw <- @lsubst_wf_iff_vars.
  allrw @bt_wf_iff.
  rw a1; dands; auto.

  allunfold @closed_bt; allsimpl.
  rw disjoint_app_r in disj; repnd.
  rw @freevars_lsubst_allvars2 in a0; auto.
  rw @freevars_lsubst_allvars2 in a0; auto; try omega.
  apply lmap_lapply_eq_implies in a0; auto; try omega;
  [|rw disjoint_app_r; allrw disjoint_app_l; dands; complete (eauto with slow)].
  rw <- a0; auto.
Qed.

Definition fresh_nrut_sub {o}
           (atoms : list (get_patom_set o))
           (vs : list NVar) : Sub :=
  let atoms' := remove_repeats (get_patom_deq o) atoms in
  match fresh_vars (length atoms') vs with
    | existT _ l _ => combine l (map mk_utoken atoms')
  end.

Lemma nrut_sub_fresh_nrut_sub {o} :
  forall (atoms : list (@get_patom_set o)) vs l,
    disjoint l atoms
    -> nrut_sub l (fresh_nrut_sub atoms vs).
Proof.
  introv disj.
  unfold fresh_nrut_sub.
  pose proof (no_repeats_remove_repeats _ (get_patom_deq o) atoms) as nr.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  assert (disjoint l atoms') as d.
  { subst; introv i j; apply in_remove_repeats in j; apply disj in i; tcsp. }
  clear dependent atoms.
  destruct (fresh_vars (length atoms') vs) as [vars q]; repnd.
  revert dependent atoms'.
  induction vars; allsimpl; introv nr d len; eauto with slow.
  destruct atoms'; allsimpl; ginv; cpx.
  allrw disjoint_cons_r; repnd.
  allrw @nrut_sub_cons.
  allrw disjoint_cons_l; repnd.
  allrw no_repeats_cons; repnd.
  repeat (autodimp IHvars hyp).
  pose proof (IHvars atoms') as h; clear IHvars.
  repeat (autodimp h hyp).
  eexists; dands; eauto.

  intro i.
  apply in_get_utokens_sub in i; exrepnd.
  apply in_combine in i0; repnd.
  allrw in_map_iff; exrepnd; subst; allsimpl; repndors; tcsp; subst; tcsp.
Qed.
Hint Resolve nrut_sub_fresh_nrut_sub : slow.

Lemma get_utokens_sub_fresh_nrut_sub {o} :
  forall (atoms : list (@get_patom_set o)) vars,
    get_utokens_sub (fresh_nrut_sub atoms vars)
    = remove_repeats (get_patom_deq o) atoms.
Proof.
  introv; unfold fresh_nrut_sub.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  destruct (fresh_vars (length atoms') vars) as [vs q]; repnd.
  clear dependent atoms.
  revert dependent vs.
  induction atoms'; introv nr disj len; allsimpl; cpx.
  destruct vs; allsimpl; cpx.
  allrw no_repeats_cons; allrw disjoint_cons_l; repnd.
  unfold get_utokens_sub; simpl; f_equal.
  apply IHatoms'; auto.
Qed.

Lemma no_repeats_dom_sub_fresh_nrut_sub {o} :
  forall (atoms : list (@get_patom_set o)) vars,
    no_repeats (dom_sub (fresh_nrut_sub atoms vars)).
Proof.
  introv; unfold fresh_nrut_sub.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  destruct (fresh_vars (length atoms') vars) as [vs q]; repnd.
  rw @dom_sub_combine; auto; allrw map_length; auto.
Qed.
Hint Resolve no_repeats_dom_sub_fresh_nrut_sub : slow.

Lemma disjoint_all_vars_dom_sub_fresh_nrut_sub {o} :
  forall (atoms : list (@get_patom_set o)) vars,
    disjoint vars (dom_sub (fresh_nrut_sub atoms vars)).
Proof.
  introv; unfold fresh_nrut_sub.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  destruct (fresh_vars (length atoms') vars) as [vs q]; repnd.
  rw @dom_sub_combine; auto; allrw map_length; eauto with slow.
Qed.
Hint Resolve disjoint_all_vars_dom_sub_fresh_nrut_sub : slow.

Lemma in_remove_repeats2 :
  forall T deq (l : list T) x,
    LIn x (remove_repeats deq l) <=> LIn x l.
Proof.
  introv; apply in_remove_repeats.
Qed.

Lemma in_fresh_nrut_sub_implies {o} :
  forall (atoms : list (@get_patom_set o)) vars v u,
    LIn (v, u) (fresh_nrut_sub atoms vars)
    -> (!LIn v vars
        # sub_find (fresh_nrut_sub atoms vars) v = Some u
        # {a : get_patom_set o & u = mk_utoken a # LIn a atoms}).
Proof.
  introv k.
  allunfold @fresh_nrut_sub.
  pose proof (no_repeats_remove_repeats _ (get_patom_deq o) atoms) as nr.
  pose proof (in_remove_repeats2 _ (get_patom_deq o) atoms) as e.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  clear Heqatoms'.
  destruct (fresh_vars (length atoms') vars) as [vs q]; repnd.
  revert dependent atoms'.
  revert dependent atoms.
  induction vs; allsimpl; introv len i nr e; eauto with slow; tcsp.
  destruct atoms'; allsimpl; ginv; cpx.
  allrw disjoint_cons_l; repnd.
  allrw no_repeats_cons; repnd.
  repeat (autodimp IHvs hyp).
  repndors; tcsp; cpx.

  - boolvar; tcsp.
    dands; auto.
    eexists; dands; eauto.
    apply e; tcsp.

  - pose proof (IHvs (remove (get_patom_deq o) g atoms) atoms') as h; clear IHvs.
    applydup in_combine in i; repnd.
    boolvar; tcsp.
    repeat (autodimp h hyp).

    + introv; rw in_remove; split; intro j; repnd; dands; tcsp.
      * intro d; subst; tcsp.
      * apply e; tcsp.
      * apply e in j; repndors; tcsp.

    + exrepnd; subst; allsimpl; dands; tcsp.
      eexists; dands; eauto.
      allrw in_remove; tcsp.
Qed.

Lemma in_fresh_nrut_sub_if {o} :
  forall (atoms : list (@get_patom_set o)) vars a,
    LIn a atoms
    -> {v : NVar
        & !LIn v vars
        # sub_find (fresh_nrut_sub atoms vars) v = Some (mk_utoken a)}.
Proof.
  introv k.
  allunfold @fresh_nrut_sub.
  pose proof (no_repeats_remove_repeats _ (get_patom_deq o) atoms) as nr.
  pose proof (in_remove_repeats2 _ (get_patom_deq o) atoms) as e.
  remember (remove_repeats (get_patom_deq o) atoms) as atoms'.
  apply e in k.
  clear dependent atoms.
  destruct (fresh_vars (length atoms') vars) as [vs q]; repnd.
  revert dependent atoms'.
  induction vs; allsimpl; introv k nr len; eauto with slow; tcsp; cpx.
  destruct atoms'; allsimpl; ginv; cpx.
  allrw disjoint_cons_l; repnd.
  allrw no_repeats_cons; repnd.
  repeat (autodimp IHvs hyp).
  repndors; subst; tcsp.

  - exists a0; boolvar; tcsp.

  - pose proof (IHvs atoms') as h; clear IHvs.
    repeat (autodimp h hyp); exrepnd.
    exists v; boolvar; tcsp.

    provefalse.
    apply @sub_find_some in h0.
    apply in_combine in h0; sp.
Qed.

Lemma cl_sub_fresh_nrut_sub {o} :
  forall (atoms : list (@get_patom_set o)) vars,
    cl_sub (fresh_nrut_sub atoms vars).
Proof.
  introv d.
  apply in_fresh_nrut_sub_implies in d; exrepnd; subst; eauto with slow.
Qed.
Hint Resolve cl_sub_fresh_nrut_sub : slow.

Definition all_vars_bterm {o} (b : @BTerm o) :=
  match b with
    | bterm vs t => vs ++ all_vars t
  end.

Definition all_vars_bterms {o} (bs : list (@BTerm o)) :=
  flat_map all_vars_bterm bs.

Lemma pull_out_atoms_aux {o} :
  forall (t : @NTerm o) atoms vars sub,
    wf_term t
    -> get_utokens_sub sub = remove_repeats (get_patom_deq o) atoms
    -> disjoint (all_vars t ++ vars) (dom_sub sub)
    -> no_repeats (dom_sub sub)
    -> (forall l, disjoint l atoms -> nrut_sub l sub)
    -> (forall (v : NVar) (u : NTerm),
          LIn (v, u) sub
          -> !LIn v (all_vars t ++ vars)
           # sub_find sub v = Some u
           # {a : get_patom_set o $ u = mk_utoken a # LIn a atoms})
    -> (forall a : get_patom_set o,
          LIn a atoms
          -> {v : NVar $ !LIn v (all_vars t ++ vars) # sub_find sub v = Some (mk_utoken a)})
    -> {u : NTerm
        & nrut_sub (get_utokens u) sub
        # alpha_eq t (lsubst u sub)
        # disjoint (bound_vars u) (dom_sub sub)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf e disj norep nrut i j.

  - Case "vterm".
    exists (@mk_var o v); allsimpl.
    dands; simpl; eauto 3 with slow.
    pose proof (nrut []) as h; autodimp h hyp.
    rw @cl_lsubst_lsubst_aux; eauto 2 with slow; simpl.
    unfold all_vars in disj; allsimpl; allrw disjoint_cons_l; repnd.
    rw @sub_find_none_if; auto.

  - Case "sterm".
    exists (sterm f); allsimpl; dands; tcsp.

  - Case "oterm".
    allsimpl.
    pose proof (nrut []) as nrutn; autodimp nrutn hyp.

    destruct (dec_op_eq_ntok op) as [x|x].

    {
      exrepnd; subst.
      apply wf_term_utok in wf; subst; allsimpl; fold_terms.
      destruct (in_deq _ (get_patom_deq o) a atoms).

      - apply j in l; exrepnd; GC.
        exists (@mk_var o v); simpl; dands; eauto 3 with slow.
        rw @cl_lsubst_lsubst_aux; eauto 2 with slow; simpl.
        rw l0; auto.

      - exists (mk_utoken a); simpl; dands; eauto 3 with slow.
        apply nrut; apply disjoint_singleton_l; auto.
    }

    assert {bs' : list BTerm
            & nrut_sub (get_utokens_bs bs') (fresh_nrut_sub atoms (all_vars_bterms bs ++ vars))
            # alpha_eq_bterms bs (lsubst_bterms_aux bs' sub)
            # disjoint (bound_vars_bterms bs') (dom_sub sub)}
      as h.
    {
      rw @wf_oterm_iff in wf; repnd.
      clear wf0.
      induction bs; allsimpl; tcsp.

      - exists ([] : list (@BTerm o)); simpl; dands; eauto with slow.

      - allunfold @all_vars; allsimpl.
        allrw disjoint_app_l; repnd.
        repeat (autodimp IHbs hyp).
        { introv ibs s w d i' j'; eapply ind; eauto. }
        { introv is; apply i in is; allrw in_app_iff; allrw not_over_or; sp. }
        { introv ia; apply j in ia; exrepnd; exists v.
          allrw in_app_iff; allrw not_over_or; sp. }
        exrepnd.
        destruct a as [vs t].
        allsimpl.

        pose proof (fresh_vars (length vs) (vars ++ vs ++ dom_sub sub ++ all_vars t ++ all_vars_bterms bs))
          as fvs; exrepnd.
        allrw disjoint_app_r; allrw disjoint_app_l; repnd.

        pose proof (ind t (lsubst t (var_ren vs lvn)) vs) as hh; clear ind; repeat (autodimp hh hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }
        pose proof (hh atoms vars sub) as h; clear hh; repeat (autodimp h hyp).
        { pose proof (wf (bterm vs t)) as w; autodimp w hyp.
          apply wf_bterm_iff in w.
          apply lsubst_preserves_wf_term; auto. }
        { introv a b.
          rw @boundvars_lsubst_vars in a; auto.
          repeat (rw in_app_iff in a); repndors; tcsp.
          - pose proof (eqvars_free_vars_disjoint t (var_ren vs lvn)) as ev.
            rw eqvars_prop in ev; apply ev in a; clear ev.
            rw @dom_sub_var_ren in a; auto.
            rw in_app_iff in a; repndors.
            + apply disj3 in a; sp.
            + apply in_sub_free_vars in a; exrepnd.
              apply in_sub_keep_first in a0; repnd.
              apply sub_find_some in a2.
              apply in_var_ren in a2; exrepnd; subst; allsimpl; repndors; tcsp; subst.
              apply fvs5 in a4; sp.
          - apply disj2 in a; sp.
          - apply disj in a; sp. }
        { introv is.
          rw @boundvars_lsubst_vars; auto.
          apply i in is; repnd; dands; auto.
          allrw in_app_iff; allrw not_over_or; repnd; dands; auto.
          intro k.
          pose proof (eqvars_free_vars_disjoint t (var_ren vs lvn)) as ev.
          rw eqvars_prop in ev; apply ev in k; clear ev.
          rw @dom_sub_var_ren in k; auto.
          rw in_app_iff in k; repndors; tcsp.
          apply in_sub_free_vars in k; exrepnd.
          apply in_sub_keep_first in k0; repnd.
          apply sub_find_some in k2.
          apply in_var_ren in k2; exrepnd; subst; allsimpl; repndors; tcsp.
          subst.
          apply sub_find_some in is1; apply in_sub_eta in is1; repnd.
          apply fvs5 in k4; sp. }
        { introv ea.
          apply j in ea; exrepnd.
          exists v; dands; auto.
          rw @boundvars_lsubst_vars; auto.
          allrw in_app_iff; allrw not_over_or; repnd; dands; auto.
          intro k.
          pose proof (eqvars_free_vars_disjoint t (var_ren vs lvn)) as ev.
          rw eqvars_prop in ev; apply ev in k; clear ev.
          rw @dom_sub_var_ren in k; auto.
          rw in_app_iff in k; repndors; tcsp.
          apply in_sub_free_vars in k; exrepnd.
          apply in_sub_keep_first in k0; repnd.
          apply sub_find_some in k2.
          apply in_var_ren in k2; exrepnd; subst; allsimpl; repndors; tcsp.
          subst.
          apply sub_find_some in ea0; apply in_sub_eta in ea0; repnd.
          apply fvs5 in k4; sp. }

        exrepnd.

        exists (bterm lvn u :: bs').
        simpl; dands; eauto 3 with slow.

        + apply nrut_sub_fresh_nrut_sub.
          apply disjoint_app_l; dands; auto.

          * introv a b.
            unfold nrut_sub in h1; repnd.
            apply h1 in a.
            rw e in a.
            rw in_remove_repeats in a; sp.

          * introv a b.
            unfold nrut_sub in IHbs1; repnd.
            apply IHbs1 in a.
            rw @get_utokens_sub_fresh_nrut_sub in a.
            rw in_remove_repeats in a; sp.

        + apply alpha_eq_bterms_cons; dands; auto.
          pose proof (alpha_bterm_change (bterm vs t) vs t lvn) as h.
          repeat (autodimp h hyp).
          { allrw disjoint_app_l; dands; eauto with slow. }
          eapply alpha_eq_bterm_trans;[exact h|].
          apply alpha_eq_bterm_congr; auto.
          rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
          rw @sub_filter_disjoint1; eauto 2 with slow.

        + allrw disjoint_app_l; dands; eauto 2 with slow.
    }

    exrepnd.
    exists (oterm op bs').
    dands; auto.

    + apply nrut; simpl.
      apply disjoint_app_l; dands; auto.

      * rw @get_utok_none; auto.
        destruct op; tcsp.
        destruct c; tcsp.
        destruct x; eexists; eauto.

      * unfold nrut_sub in h1; repnd.
        rw @get_utokens_sub_fresh_nrut_sub in h1.
        introv a b; apply h1 in a.
        rw in_remove_repeats in a; sp.

    + rw @cl_lsubst_lsubst_aux; eauto 2 with slow.
      simpl.
      unfold alpha_eq_bterms, lsubst_bterms_aux in h2; repnd.
      apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
Qed.

Lemma pull_out_atoms {o} :
  forall (t : @NTerm o) atoms vars,
    wf_term t ->
    {sub : Sub
     & get_utokens_sub sub = remove_repeats (get_patom_deq o) atoms
     # disjoint (all_vars t ++ vars) (dom_sub sub)
     # no_repeats (dom_sub sub)
     # {u : NTerm
        & nrut_sub (get_utokens u) sub
        # alpha_eq t (lsubst u sub)
        # disjoint (bound_vars u) (dom_sub sub)}}.
Proof.
  introv wf.
  exists (fresh_nrut_sub atoms (all_vars t ++ vars)).
  pose proof (nrut_sub_fresh_nrut_sub atoms (all_vars t ++ vars)) as nrut.
  pose proof (get_utokens_sub_fresh_nrut_sub atoms (all_vars t ++ vars)) as e.
  pose proof (no_repeats_dom_sub_fresh_nrut_sub atoms (all_vars t ++ vars)) as norep.
  pose proof (disjoint_all_vars_dom_sub_fresh_nrut_sub atoms (all_vars t ++ vars)) as disj.
  pose proof (in_fresh_nrut_sub_implies atoms (all_vars t ++ vars)) as i.
  pose proof (in_fresh_nrut_sub_if atoms (all_vars t ++ vars)) as j.
  remember (fresh_nrut_sub atoms (all_vars t ++ vars)) as sub.
  clear Heqsub; dands; auto.
  eapply pull_out_atoms_aux; eauto.
Qed.

Lemma implies_nrut_sub_app {o} :
  forall (sub : @Sub o) l1 l2,
    nrut_sub l1 sub
    -> nrut_sub l2 sub
    -> nrut_sub (l1 ++ l2) sub.
Proof.
  introv nrut1 nrut2.
  allunfold @nrut_sub; repnd; dands; auto.
  apply disjoint_app_l; dands; auto.
Qed.

Lemma pull_out_atoms_sub {o} :
  forall (s : @Sub o) atoms vars,
    wf_sub s ->
    {sub : Sub
     & get_utokens_sub sub = remove_repeats (get_patom_deq o) atoms
     # disjoint (sub_allvars s ++ vars) (dom_sub sub)
     # no_repeats (dom_sub sub)
     # {s' : Sub
        & nrut_sub (get_utokens_sub s') sub
        # alphaeq_sub s (lsubst_sub s' sub)
        # disjoint (sub_bound_vars s') (dom_sub sub)}}.
Proof.
  introv wf.
  exists (fresh_nrut_sub atoms (sub_allvars s ++ vars)).
  pose proof (nrut_sub_fresh_nrut_sub atoms (sub_allvars s ++ vars)) as nrut.
  pose proof (get_utokens_sub_fresh_nrut_sub atoms (sub_allvars s ++ vars)) as e.
  pose proof (no_repeats_dom_sub_fresh_nrut_sub atoms (sub_allvars s ++ vars)) as norep.
  pose proof (disjoint_all_vars_dom_sub_fresh_nrut_sub atoms (sub_allvars s ++ vars)) as disj.
  pose proof (in_fresh_nrut_sub_implies atoms (sub_allvars s ++ vars)) as i.
  pose proof (in_fresh_nrut_sub_if atoms (sub_allvars s ++ vars)) as j.
  remember (fresh_nrut_sub atoms (sub_allvars s ++ vars)) as sub.
  clear Heqsub; dands; auto.

  induction s; allsimpl.

  - exists ([] : @Sub o); allsimpl; dands; auto.
    apply nrut; unfold get_utokens_sub; simpl; auto.

  - destruct a as [v t]; allsimpl.
    allrw @wf_sub_cons_iff; repnd.
    unfold sub_allvars in disj; allsimpl; fold (sub_allvars s) in disj.
    allrw disjoint_app_l; repnd.
    repeat (autodimp IHs hyp).
    { introv k; apply i in k; repnd; dands; auto.
      unfold sub_allvars in k0; allsimpl; fold (sub_allvars s) in k0.
      allrw in_app_iff; allrw not_over_or; repnd; dands; auto. }
    { introv k; apply j in k; exrepnd.
      unfold sub_allvars in k1; allsimpl; fold (sub_allvars s) in k1.
      exists v0; dands; auto.
      allrw in_app_iff; allrw not_over_or; repnd; dands; auto. }

    exrepnd.
    pose proof (pull_out_atoms_aux t atoms vars sub) as k.
    repeat (autodimp k hyp).
    { rw disjoint_app_l; dands; auto.
      apply disjoint_sym; apply disjoint_to_all_vars_r; eauto with slow. }
    { introv k; apply i in k; repnd; dands; auto.
      pose proof (allvars_eq_all_vars t) as ee; rw eqvars_prop in ee.
      unfold sub_allvars in k0; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; dands; auto;
      introv kk; destruct k3; apply ee; allrw in_app_iff; sp. }
    { introv k; apply j in k; exrepnd; exists v0; dands; auto.
      pose proof (allvars_eq_all_vars t) as ee; rw eqvars_prop in ee.
      unfold sub_allvars in k0; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; dands; auto;
      introv kk; destruct k3; apply ee; allrw in_app_iff; sp. }

    exrepnd.
    exists ((v,u) :: s'); allsimpl; dands; auto.

    + unfold get_utokens_sub; simpl.
      apply implies_nrut_sub_app; auto.

    + constructor; auto.
      apply alphaeq_eq; auto.

    + apply disjoint_app_l; dands; auto.
Qed.

Lemma remove_repeats_if_no_repeats :
  forall T (deq : Deq T) (l : list T),
    no_repeats l
    -> remove_repeats deq l = l.
Proof.
  induction l; introv nr; allsimpl; tcsp.
  allrw no_repeats_cons; repnd; autodimp IHl hyp.
  boolvar; tcsp.
  f_equal; auto.
Qed.

Lemma no_repeats_get_utokens_nrut_sub {o} :
  forall (sub : @Sub o) l,
    nrut_sub l sub
    -> no_repeats (get_utokens_sub sub).
Proof.
  unfold nrut_sub; sp.
Qed.
Hint Resolve no_repeats_get_utokens_nrut_sub : slow.

Lemma get_utokens_eq_nrut_subs_implies_eq_range {o} :
  forall (sub1 sub2 : @Sub o) l1 l2,
    nrut_sub l1 sub1
    -> nrut_sub l2 sub2
    -> get_utokens_sub sub1 = get_utokens_sub sub2
    -> range sub1 = range sub2.
Proof.
  induction sub1; destruct sub2; introv nrut1 nrut2 e; allsimpl; tcsp.
  - destruct p; allrw @nrut_sub_cons; exrepnd; subst.
    unfold get_utokens_sub in e; allsimpl; cpx.
  - destruct a; allrw @nrut_sub_cons; exrepnd; subst.
    unfold get_utokens_sub in e; allsimpl; cpx.
  - destruct a, p; allrw @nrut_sub_cons; exrepnd; subst.
    unfold get_utokens_sub in e; allsimpl; cpx.
    f_equal; eapply IHsub1; eauto.
Qed.

Lemma pull_out_nrut_sub_sub {o} :
  forall (s : @Sub o) sub l,
    nrut_sub l sub
    -> no_repeats (dom_sub sub)
    -> wf_sub s
    -> disjoint (sub_free_vars s) (dom_sub sub)
    -> {s' : Sub
        & alphaeq_sub s (lsubst_sub s' sub)
        # disjoint (get_utokens_sub sub) (get_utokens_sub s')
        # disjoint (sub_bound_vars s') (dom_sub sub)}.
Proof.
  induction s; introv nrut norep wf disj; allsimpl.
  - exists ([] : @Sub o); allsimpl; dands; auto.
    unfold get_utokens_sub; allsimpl; auto.
  - destruct a as [v t]; allrw @wf_sub_cons_iff; repnd.
    allrw disjoint_app_l; repnd.
    pose proof (IHs sub l) as h; clear IHs; repeat (autodimp h hyp); exrepnd.
    pose proof (pull_out_nrut_sub t sub l) as k; repeat (autodimp k hyp); exrepnd.
    exists ((v,u) :: s'); simpl.
    unfold get_utokens_sub; simpl; fold (get_utokens_sub s'); fold (get_utokens_sub sub).
    allrw disjoint_app_r; allrw disjoint_app_l; dands; auto.
    constructor; auto.
    apply alphaeq_eq; auto.
Qed.

Lemma alpha_eq_lsubst_closed {o} :
  forall (t : @NTerm o) sub,
    closed t
    -> alpha_eq (lsubst t sub) t.
Proof.
  introv cl.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0.
  rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow.
  apply alphaeq_preserves_closed in h1; apply h1; auto.
Qed.

Lemma sub_find_lsubst_aux_sub {o} :
  forall v (sub1 sub2 : @Sub o),
    sub_find (lsubst_aux_sub sub1 sub2) v
    = match sub_find sub1 v with
        | Some t => Some (lsubst_aux t sub2)
        | None => None
      end.
Proof.
  induction sub1; introv; allsimpl; auto.
  destruct a; allsimpl; boolvar; tcsp.
Qed.

Lemma cl_lsubst_aux_sub_trivial {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub1
    -> lsubst_aux_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv cl; allsimpl; tcsp.
  destruct a as [v t]; allsimpl.
  allrw @cl_sub_cons; repnd.
  rw IHsub1; auto.
  rw @lsubst_aux_trivial_cl_term2; auto.
Qed.

Lemma sub_bound_vars_app {o} :
  forall (sub1 sub2 : @Sub o),
    sub_bound_vars (sub1 ++ sub2)
    = sub_bound_vars sub1 ++ sub_bound_vars sub2.
Proof.
  induction sub1; introv; allsimpl; tcsp.
  destruct a as [v t].
  rw IHsub1.
  rw app_assoc; auto.
Qed.

Lemma lsubst_aux_sub_app {o} :
  forall (sub1 sub2 sub : @Sub o),
    lsubst_aux_sub (sub1 ++ sub2) sub
    = lsubst_aux_sub sub1 sub ++ lsubst_aux_sub sub2 sub.
Proof.
  induction sub1; introv; allsimpl; tcsp.
  destruct a as [v t].
  rw IHsub1; simpl; auto.
Qed.

Lemma lsubst_aux_sub_disj_dom2 {o} :
  forall (sub1 sub2 : @Sub o),
    disjoint (sub_free_vars sub1) (dom_sub sub2)
    -> lsubst_aux_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv disj; allsimpl; tcsp.
  destruct a as [v t]; allsimpl.
  allrw disjoint_app_l; repnd.
  rw IHsub1; auto.
  rw @lsubst_aux_trivial_cl_term; auto.
Qed.

Lemma cl_lsubst_aux_lsubst_aux_lsubst_aux_sub {o} :
  forall (t : @NTerm o) s sub1 sub2,
    cl_sub sub1
    -> cl_sub sub2
    -> cl_sub (lsubst_aux_sub s sub2)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> disjoint (dom_sub sub1) (dom_sub s)
    -> disjoint (dom_sub sub1) (sub_free_vars s)
    -> disjoint (dom_sub sub2) (free_vars t)
    -> disjoint (dom_sub sub1) (bound_vars t)
    -> disjoint (dom_sub sub2) (bound_vars t)
    -> alpha_eq
         (lsubst_aux (lsubst_aux t sub1) (lsubst_aux_sub s sub2))
         (lsubst_aux (lsubst_aux t s) (sub1 ++ sub2)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
  introv cl1 cl2 cl3 disj1 disj2 disj3 disj4 disj5 disj6.

  - Case "vterm".
    allsimpl; allrw disjoint_singleton_r.

    remember (sub_find sub1 v) as sf; symmetry in Heqsf; destruct sf.

    + rw @cl_sub_eq2 in cl1.
      applydup @sub_find_some in Heqsf.
      applydup cl1 in Heqsf0.
      rw @lsubst_aux_trivial_cl_term2; auto.
      apply in_sub_eta in Heqsf0; repnd.
      applydup disj2 in Heqsf2.
      rw @sub_find_none_if; auto.
      simpl.
      rw @sub_find_app.
      rw Heqsf; auto.

    + simpl.
      rw @sub_find_lsubst_aux_sub.
      allrw disjoint_singleton_r.
      remember (sub_find s v) as sf'; symmetry in Heqsf'; destruct sf'; allsimpl.

      * rw @cl_lsubst_aux_app; auto.
        rw (lsubst_aux_trivial_cl n sub1); auto.
        apply sub_find_some in Heqsf'.
        rw @sub_free_vars_is_flat_map_free_vars_range in disj3.
        apply in_sub_eta in Heqsf'; repnd; disj_flat_map; eauto with slow.

      * rw @sub_find_app; rw Heqsf.
        rw @sub_find_none_if; auto.

  - Case "sterm".
    allsimpl; auto.

  - Case "oterm".
    allsimpl; allrw map_map; unfold compose.
    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i; rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; allsimpl.
    rw @sub_filter_lsubst_aux_sub.
    rw @sub_filter_app.
    disj_flat_map; allsimpl.
    allrw disjoint_app_r; repnd.

    apply alpha_eq_bterm_congr.
    rw <- @sub_filter_lsubst_aux_sub.
    rw (sub_filter_disjoint1 sub1 l); auto.
    rw (sub_filter_disjoint1 sub2 l); auto.

    pose proof (ind t t l) as h; repeat (autodimp h hyp); clear ind; eauto 3 with slow.
    pose proof (h (sub_filter s l) (sub_filter sub1 l) (sub_filter sub2 l)) as k; clear h.
    rw (sub_filter_disjoint1 sub1 l) in k; auto.
    rw (sub_filter_disjoint1 sub2 l) in k; auto.
    rw <- @dom_sub_sub_filter in k.
    rw <- @sub_filter_lsubst_aux_sub in k.
    repeat (autodimp k hyp); eauto 3 with slow.
    { introv i j; applydup i3 in i; applydup i4 in i.
      allrw in_remove_nvars; sp. }
Qed.

Lemma cl_lsubst_lsubst_lsubst_sub {o} :
  forall (t : @NTerm o) s sub1 sub2,
    cl_sub sub1
    -> cl_sub sub2
    -> cl_sub (lsubst_sub s sub2)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> disjoint (dom_sub sub1) (dom_sub s)
    -> disjoint (dom_sub sub1) (sub_free_vars s)
    -> disjoint (dom_sub sub2) (free_vars t)
    -> disjoint (dom_sub sub1) (bound_vars t)
    -> disjoint (dom_sub sub2) (bound_vars t)
    -> disjoint (sub_free_vars s) (bound_vars t)
    -> alpha_eq
         (lsubst (lsubst t sub1) (lsubst_sub s sub2))
         (lsubst (lsubst t s) (sub1 ++ sub2)).
Proof.
  introv cl1 cl2 cl3 disj1 disj2 disj3 disj4 disj5 disj6 disj7.
  rw (cl_lsubst_lsubst_aux t sub1); auto.
  rw (cl_lsubst_lsubst_aux (lsubst_aux t sub1)); auto.
  rw (cl_lsubst_lsubst_aux (lsubst t s)); eauto 2 with slow.
  rw @lsubst_lsubst_aux;[|rw <- @sub_free_vars_is_flat_map_free_vars_range]; eauto 2 with slow.
  rw @cl_lsubst_sub_eq_lsubst_aux_sub; auto.
  apply cl_lsubst_aux_lsubst_aux_lsubst_aux_sub; auto.
  rw <- @cl_lsubst_sub_eq_lsubst_aux_sub; auto.
Qed.

Lemma cl_sub_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren,
    cl_sub sub
    -> cl_sub (ren_utokens_sub ren sub).
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a as [v t]; allrw @cl_sub_cons; repnd; dands; tcsp.
  unfold closed; rw @free_vars_ren_utokens; auto.
Qed.
Hint Resolve cl_sub_ren_utokens_sub : slow.

Lemma dom_sub_lsubst_sub {o} :
  forall (sub1 sub2 : @Sub o),
    dom_sub (lsubst_sub sub1 sub2) = dom_sub sub1.
Proof.
  induction sub1; introv; allsimpl; tcsp.
  destruct a as [v t]; allsimpl; rw IHsub1; auto.
Qed.

Lemma free_vars_subset_allvars {o} :
  forall (t : @NTerm o), subset (free_vars t) (allvars t).
Proof.
  introv i.
  pose proof (allvars_eq_all_vars t) as h; rw eqvars_prop in h; apply h.
  rw in_app_iff; sp.
Qed.
Hint Resolve free_vars_subset_allvars : slow.

Lemma bound_vars_subset_allvars {o} :
  forall (t : @NTerm o), subset (bound_vars t) (allvars t).
Proof.
  introv i.
  pose proof (allvars_eq_all_vars t) as h; rw eqvars_prop in h; apply h.
  rw in_app_iff; sp.
Qed.
Hint Resolve bound_vars_subset_allvars : slow.

Lemma in_range_utok_ren_implies_ren_atom_some {o} :
  forall (ren : @utok_ren o) a,
    no_repeats (dom_utok_ren ren)
    -> LIn a (range_utok_ren ren)
    -> {b : get_patom_set o
        & LIn b (dom_utok_ren ren)
        # ren_atom ren b = a}.
Proof.
  induction ren; introv nr i; allsimpl; tcsp.
  destruct a; allsimpl; repndors; subst; tcsp.
  - exists g; simpl; dands; tcsp.
    unfold ren_atom; simpl; boolvar; tcsp.
  - allrw no_repeats_cons; repnd.
    apply IHren in i; exrepnd; auto.
    destruct (get_patom_deq o g b); subst; tcsp.
    exists b; dands; tcsp.
    unfold ren_atom; simpl; boolvar; tcsp.
Qed.

Definition utok_ren_cond {o} (atoms : list (get_patom_set o)) ren :=
  forall a, LIn a atoms -> LIn a (range_utok_ren ren) -> LIn a (dom_utok_ren ren).

Lemma utok_ren_cond_nil {o} :
  forall ren : @utok_ren o, utok_ren_cond [] ren.
Proof.
  introv i j; allsimpl; sp.
Qed.
Hint Resolve utok_ren_cond_nil : slow.

Lemma utok_ren_cond_app {o} :
  forall atoms1 atoms2 (ren : @utok_ren o),
    utok_ren_cond atoms1 ren
    -> utok_ren_cond atoms2 ren
    -> utok_ren_cond (atoms1 ++ atoms2) ren.
Proof.
  introv c1 c2 i j; allrw in_app_iff; repndors.
  - apply c1; auto.
  - apply c2; auto.
Qed.

Lemma ex_ren_atom {o} :
  forall (a : get_patom_set o) ren atoms,
    no_repeats (dom_utok_ren ren) ->
    {ren' : utok_ren
     & {b : get_patom_set o
     & ren_atom (ren ++ ren') b = a
     # disjoint (a :: atoms ++ dom_utok_ren ren ++ range_utok_ren ren) (dom_utok_ren ren')
     # disjoint (range_utok_ren ren') (range_utok_ren ren)
     # subset (range_utok_ren ren') (dom_utok_ren ren)
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond [b] ren }}.
Proof.
  introv norep.

  destruct (in_deq _ (get_patom_deq o) a (range_utok_ren ren)) as [r|r].

  - applydup @in_range_utok_ren_implies_ren_atom_some in r; auto; exrepnd.
    exists ([] : @utok_ren o) b; simpl; allrw app_nil_r; dands; tcsp.
    introv i j; allsimpl; repndors; subst; tcsp.

  - destruct (in_deq _ (get_patom_deq o) a (dom_utok_ren ren)) as [d|d].

    + pose proof (fresh_atom o (a :: atoms ++ dom_utok_ren ren ++ range_utok_ren ren)) as h.
      exrepnd.
      exists [(x,a)] x; simpl.
      rw disjoint_singleton_l.
      rw disjoint_singleton_r.
      rw singleton_subset.
      allrw in_app_iff; simpl.
      dands; auto.

      {
        unfold ren_atom.
        allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
        rw @utok_ren_find_app.
        rw @utok_ren_find_none_if_not_in; simpl; auto.
        boolvar; tcsp.
      }

      {
        introv i j; allsimpl; repndors; subst; tcsp.
        allrw in_app_iff; allrw not_over_or; tcsp.
      }

    + exists ([] : @utok_ren o) a; allrw app_nil_r; allsimpl; dands; tcsp.
      { apply ren_atom_not_in; tcsp. }
      { introv i j; allsimpl; repndors; subst; tcsp. }
Qed.

Lemma ex_ren_utok_op {o} :
  forall (op : @Opid o) ren atoms,
    no_repeats (dom_utok_ren ren) ->
    {ren' : utok_ren
     & {op' : Opid
     & ren_utok_op (ren ++ ren') op' = op
     # disjoint (get_utokens_o op ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren) (dom_utok_ren ren')
     # disjoint (range_utok_ren ren') (range_utok_ren ren)
     # subset (range_utok_ren ren') (dom_utok_ren ren)
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond (get_utokens_o op') ren }}.
Proof.
  introv norep.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
  - apply get_utok_some in Heqguo; subst; allsimpl.
    pose proof (ex_ren_atom g ren atoms norep) as h; exrepnd.
    exists ren' (Can (NUTok b)); dands; auto.
    simpl; rw h0; auto.
  - exists ([] : @utok_ren o) op; allsimpl; dands; auto.
    { rw app_nil_r; apply implies_ren_utok_op_id; apply get_utok_none; auto. }
    { apply get_utok_none in Heqguo; rw Heqguo; introv i j; allsimpl; sp. }
Qed.

Lemma dom_utok_ren_app {o} :
  forall (ren1 ren2 : @utok_ren o),
    dom_utok_ren (ren1 ++ ren2) = dom_utok_ren ren1 ++ dom_utok_ren ren2.
Proof.
  induction ren1; introv; allsimpl; tcsp.
  destruct a; allsimpl; rw IHren1; auto.
Qed.

Lemma ren_utokens_bs_app_weak_l {o} :
  forall (bs : list (@BTerm o)) ren1 ren2,
    disjoint (dom_utok_ren ren2) (get_utokens_bs bs)
    -> ren_utokens_bs (ren1 ++ ren2) bs = ren_utokens_bs ren1 bs.
Proof.
  induction bs; introv disj; allsimpl; auto.
  destruct a as [v t]; allsimpl.
  allrw disjoint_app_r; repnd.
  rw IHbs; auto.
  rw @ren_utokens_app_weak_l; auto.
Qed.

Lemma ex_ren_utokens {o} :
  forall (t : @NTerm o) ren atoms,
    no_repeats (dom_utok_ren ren) ->
    {ren' : utok_ren
     & {u : NTerm
     & ren_utokens (ren ++ ren') u = t
     # disjoint (get_utokens t ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren) (dom_utok_ren ren')
     # disjoint (range_utok_ren ren') (range_utok_ren ren)
     # subset (range_utok_ren ren') (dom_utok_ren (ren ++ ren'))
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond (get_utokens u) ren }}.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv norep.

  - Case "vterm".
    exists ([] : @utok_ren o) (@mk_var o v); simpl; dands; eauto with slow.

  - Case "sterm".
    exists ([] : @utok_ren o) (sterm f); autorewrite with slow in *.
    simpl; dands; tcsp; eauto 3 with slow.

  - Case "oterm".

    assert
      (forall atoms ren,
         no_repeats (dom_utok_ren ren)
         -> {ren' : utok_ren
            & {bs' : list BTerm
            & ren_utokens_bs (ren ++ ren') bs' = bs
            # disjoint (get_utokens_bs bs ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren) (dom_utok_ren ren')
            # disjoint (range_utok_ren ren') (range_utok_ren ren)
            # subset (range_utok_ren ren') (dom_utok_ren (ren ++ ren'))
            # no_repeats (dom_utok_ren ren')
            # no_repeats (range_utok_ren ren')
            # utok_ren_cond (get_utokens_bs bs') ren }}) as ebs.
    { clear ren atoms norep.
      induction bs; introv norep.
      - exists ([] : @utok_ren o) ([] : list (@BTerm o)); simpl; dands; eauto with slow.
      - destruct a as [l t].
        autodimp IHbs hyp.
        { introv i; apply (ind nt lv); eauto; simpl; sp. }
        pose proof (IHbs (atoms ++ get_utokens t) ren norep) as ibs; clear IHbs; exrepnd; allsimpl.
        pose proof (ind t l) as h; clear ind; autodimp h hyp.
        pose proof (h (ren ++ ren') (get_utokens_bs bs ++ get_utokens_bs bs' ++ atoms)) as k; clear h.
        autodimp k hyp.
        { rw @dom_utok_ren_app; rw no_repeats_app; dands; auto.
          allrw disjoint_app_l; repnd; auto. }
        exrepnd.
        exists (ren' ++ ren'0) (bterm l u :: bs'); simpl.
        allrw @range_utok_ren_app.
        allrw @dom_utok_ren_app.
        allrw no_repeats_app.
        allrw disjoint_app_l.
        allrw subset_app.
        allrw disjoint_app_r.
        repeat (rw app_assoc).
        repnd; dands; eauto 2 with slow.
        + rw k0; f_equal; rw @ren_utokens_bs_app_weak_l; eauto with slow.
        + apply utok_ren_cond_app; auto.
          introv i j.
          apply k1 in i.
          rw @range_utok_ren_app in i; rw @dom_utok_ren_app in i; allrw in_app_iff.
          autodimp i hyp; repndors; tcsp.
          apply ibs2 in i; tcsp.
    }

    pose proof (ebs (atoms ++ get_utokens_o op) ren norep) as ebs'; clear ebs; exrepnd.

    pose proof (ex_ren_utok_op op (ren ++ ren') (get_utokens_bs bs ++ get_utokens_bs bs' ++ atoms)) as eop.
    allrw disjoint_app_l; repnd.
    autodimp eop hyp.
    { rw @dom_utok_ren_app; rw no_repeats_app; dands; auto. }
    exrepnd.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw disjoint_app_l; repnd.
    allrw disjoint_app_r; repnd.

    exists (ren' ++ ren'0) (oterm op' bs'); simpl.
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw disjoint_app_l; allrw disjoint_app_r.
    repeat (rw app_assoc).
    dands; eauto 3 with slow.

    {
      rw eop0; f_equal.
      fold (ren_utokens_bs ((ren ++ ren') ++ ren'0) bs').
      rw @ren_utokens_bs_app_weak_l; eauto with slow.
    }

    {
      apply utok_ren_cond_app; tcsp.
      introv i j.
      apply eop1 in i.
      rw @range_utok_ren_app in i; rw @dom_utok_ren_app in i; allrw in_app_iff.
      autodimp i hyp; repndors; tcsp.
      apply ebs'2 in i; tcsp.
    }
Qed.

Lemma ren_utokens_sub_app_weak_l {o} :
  forall (sub : @Sub o) ren1 ren2,
    disjoint (dom_utok_ren ren2) (get_utokens_sub sub)
    -> ren_utokens_sub (ren1 ++ ren2) sub = ren_utokens_sub ren1 sub.
Proof.
  induction sub; introv disj; allsimpl; auto.
  destruct a as [v t]; allsimpl.
  allrw @get_utokens_sub_cons; allrw disjoint_app_r; repnd.
  rw IHsub; auto.
  rw @ren_utokens_app_weak_l; auto.
Qed.

Lemma ex_ren_utokens_sub {o} :
  forall (sub : @Sub o) ren atoms,
    no_repeats (dom_utok_ren ren) ->
    {ren' : utok_ren
     & {sub' : Sub
     & ren_utokens_sub (ren ++ ren') sub' = sub
     # disjoint (get_utokens_sub sub ++ atoms ++ dom_utok_ren ren ++ range_utok_ren ren) (dom_utok_ren ren')
     # disjoint (range_utok_ren ren') (range_utok_ren ren)
     # subset (range_utok_ren ren') (dom_utok_ren (ren ++ ren'))
     # no_repeats (dom_utok_ren ren')
     # no_repeats (range_utok_ren ren')
     # utok_ren_cond (get_utokens_sub sub') ren }}.
Proof.
  induction sub; introv nr.
  - exists ([] : @utok_ren o) ([] : @Sub o); simpl; rw @get_utokens_sub_nil.
    dands; eauto with slow.
  - destruct a as [v t]; allsimpl.
    pose proof (IHsub ren (atoms ++ get_utokens t) nr) as ih; clear IHsub; exrepnd.
    allrw disjoint_app_l; repnd.

    pose proof (ex_ren_utokens t (ren ++ ren') (get_utokens_sub sub ++ get_utokens_sub sub' ++ atoms)) as h.
    autodimp h hyp .
    { rw @dom_utok_ren_app; rw no_repeats_app; dands; auto. }
    exrepnd.

    exists (ren' ++ ren'0) ((v,u) :: sub'); simpl.
    repeat (rw app_assoc).
    allrw @range_utok_ren_app.
    allrw @dom_utok_ren_app.
    allrw no_repeats_app.
    allrw @get_utokens_sub_cons.
    allrw disjoint_app_l; allrw disjoint_app_r.

    repnd; dands; eauto 3 with slow.

    {
      rw h0; f_equal.
      rw @ren_utokens_sub_app_weak_l; eauto with slow.
    }

    {
      apply utok_ren_cond_app; auto.
      introv i j.
      apply h1 in i.
      rw @range_utok_ren_app in i; rw @dom_utok_ren_app in i; allrw in_app_iff.
      autodimp i hyp; repndors; tcsp.
      apply ih2 in i; tcsp.
    }
Qed.

Lemma wf_sub_ren_utokens_sub_iff {o} :
  forall (sub : @Sub o) (ren : utok_ren),
    wf_sub (ren_utokens_sub ren sub) <=> wf_sub sub.
Proof.
  induction sub; introv; split; intro k; allsimpl; tcsp; destruct a as [v t];
  allrw @wf_sub_cons_iff; repnd; dands; tcsp.
  - apply wf_term_ren_utokens in k0; auto.
  - apply IHsub in k; auto.
  - apply wf_term_ren_utokens; auto.
  - apply IHsub; auto.
Qed.

Lemma diff_nil_if_subset :
  forall T (eq : Deq T) l1 l2,
    subset l2 l1
    -> diff eq l1 l2 = [].
Proof.
  introv ss.
  pose proof (null_diff_subset T eq l1 l2) as h.
  rw null_iff_nil in h; apply h; auto.
Qed.

Lemma alpha_eq_bterm_preserves_utokens {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> get_utokens_b b1 = get_utokens_b b2.
Proof.
  introv aeq.
  pose proof (alphaeq_preserves_utokens (oterm Exc [b1]) (oterm Exc [b2])) as h.
  allsimpl; allrw app_nil_r; apply h.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; cpx.
Qed.

Lemma subset_map_map :
  forall {A B} (f : A -> B) (l1 l2 : list A),
    subset l1 l2
    -> subset (map f l1) (map f l2).
Proof.
  introv ss i.
  allrw in_map_iff; exrepnd; subst.
  apply ss in i1.
  exists a; dands; auto.
Qed.

Lemma get_utokens_b_ren_utokens_b {o} :
  forall (b : @BTerm o) ren,
    get_utokens_b (ren_utokens_b ren b)
    = map (ren_atom ren) (get_utokens_b b).
Proof.
  introv.
  pose proof (get_utokens_ren_utokens (oterm Exc [b]) ren) as h.
  allsimpl; allrw app_nil_r; auto.
Qed.

Lemma inv_ren_utokens_b {o} :
  forall (b : @BTerm o) ren,
    no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens_b b))
    -> ren_utokens_b (inv_utok_ren ren) (ren_utokens_b ren b) = b.
Proof.
  introv norep disj.
  destruct b as [l t]; allsimpl.
  f_equal; apply inv_ren_utokens; auto.
Qed.

Lemma computes_to_exception_ren_utokens {o} :
  forall lib (t a e : NTerm) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_to_exception lib a t e
    -> computes_to_exception lib (ren_utokens ren a) (ren_utokens ren t) (ren_utokens ren e).
Proof.
  introv wf norep disj r.
  allunfold @computes_to_exception; repnd; dands; eauto 2 with slow.
  apply (reduces_to_ren_utokens _ _ _ ren) in r; auto.
Qed.

Lemma computes_to_exception_preserves_utokens {o} :
  forall lib (t a e : @NTerm o),
    nt_wf t
    -> computes_to_exception lib a t e
    -> (subset (get_utokens a) (get_utokens t)
        # subset (get_utokens e) (get_utokens t)).
Proof.
  introv wf r.
  allunfold @computes_to_exception; repnd; dands; eauto 2 with slow.
  - apply reduces_to_preserves_utokens in r; allsimpl; allrw app_nil_r; allrw subset_app; sp.
  - apply reduces_to_preserves_utokens in r; allsimpl; allrw app_nil_r; allrw subset_app; sp.
Qed.

Lemma computes_to_marker_ren_utokens {o} :
  forall lib (t : @NTerm o) m ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> computes_to_marker lib t m
    -> computes_to_marker lib (ren_utokens ren t) m.
Proof.
  introv wf norep disj r.
  allunfold @computes_to_marker; repnd; dands; eauto 2 with slow.
  apply (reduces_to_ren_utokens _ _ _ ren) in r0; auto.
Qed.
