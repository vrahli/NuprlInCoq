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


Require Export substitution4.
Require Export computation4.
Require Export alphaeq_sub.


(* same as [isvalue_like] but includes markers too *)
Definition is_value_like {o} lib (t : @NTerm o) :=
  isvalue_like t [+] ismrk lib t.

Definition hasvalue_like {p} lib (t : @NTerm p) :=
  {v : NTerm & reduces_to lib t v # isvalue_like v}.

Definition has_value_like {p} lib (t : @NTerm p) :=
  {v : NTerm & reduces_to lib t v # is_value_like lib v}.

Definition converges_to_value_like {p} lib (t : @NTerm p) :=
  {u : NTerm & reduces_to lib t u # isvalue_like u}.

Definition converges_to_is_value_like {p} lib (t : @NTerm p) :=
  {u : NTerm & reduces_to lib t u # is_value_like lib u}.


(*
Lemma bottom_doesnt_mark {p} :
  forall (lib : @library p) m,
    computes_to_marker lib mk_bottom m
    -> False.
Proof.
  introv Hcv.
  repnud Hcv.
  repnud Hcv.
  repnud Hcv0.
  exrepnd.
  unfold reduces_in_atmost_k_steps in Hcv1.
  unfold_all_mk.
  induction k as [k  Hind] using comp_ind.
  destruct k.

  - inverts Hcv1.

  - rw @compute_at_most_k_steps_eq_f in Hcv1.
    rw @compute_at_most_k_stepsf_S in Hcv1; allsimpl.
    destruct k.

    + inversion Hcv1.

    + rw @compute_at_most_k_stepsf_S in Hcv1; allsimpl.
      unfold apply_bterm in Hcv1.
      simpl in Hcv1.
      revert Hcv1.
      change_to_lsubst_aux4; simpl; try (complete sp).
      intro Hcv1.
      rw <- @compute_at_most_k_steps_eq_f in Hcv1.
      apply Hind in Hcv1; sp.
Qed.

Lemma can_doesnt_mark {p} :
  forall (lib : @library p) c bterms m,
    computes_to_marker lib (oterm (@Can p c) bterms) m -> False.
Proof.
  introv ce.
  destruct ce as [r i].
  destruct r as [k r].
  unfold reduces_to, reduces_in_atmost_k_steps in r; exrepnd.
  rw @compute_at_most_k_steps_eq_f in r.
  induction k; simpl in r; sp.
  inversion r; subst.
Qed.

Lemma axiom_doesnt_mark {p} :
  forall lib m, @computes_to_marker p lib mk_axiom m -> False.
Proof.
  introv c.
  apply can_doesnt_mark in c; sp.
Qed.

Lemma vbot_doesnt_mark {p} :
  forall lib v m, !computes_to_marker lib (@mk_vbot p v) m.
Proof.
  introv Hcv.
  unfold computes_to_marker, reduces_to, reduces_in_atmost_k_steps in Hcv.
  exrepnd.
  induction k as [k Hind] using comp_ind.
  destruct k.

  - inverts Hcv1.

  - rw @compute_at_most_k_steps_eq_f in Hcv1.
    rw @compute_at_most_k_stepsf_S in Hcv1.
    simpl in Hcv1.
    destruct k.

    + inversion Hcv1.

    + rw @compute_at_most_k_stepsf_S in Hcv1.
      simpl in Hcv1.
      unfold apply_bterm in Hcv1.
      simpl in Hcv1.
      revert Hcv1.
      change_to_lsubst_aux4; simpl; try (complete sp); boolvar.
      intro Hc.
      rw <- @compute_at_most_k_steps_eq_f in Hc.
      apply Hind in Hc; sp.
Qed.

Lemma alpha_eq_marker {o} :
  forall m (t : @NTerm o),
    alpha_eq (mk_marker m) t <=> t = mk_marker m.
Proof.
  introv; split; intro k; subst; auto.
  inversion k as [|? ? ? len imp]; subst; allsimpl; cpx.
Qed.

(*Require Export atoms.*)

Definition not_marked {o} (m : marker) (t : @NTerm o) :=
  !LIn m (get_markers t).

Definition not_marked_b {o} (m : marker) (b : @BTerm o) :=
  match b with
    | bterm _ t => not_marked m t
  end.
 *)

Definition bot_sub {o} (vs : list NVar) : @Sub o :=
  map (fun v : NVar => (v, mk_bottom)) vs.

Definition bot_sub_fv {o} (t : @NTerm o) : @Sub o :=
  bot_sub (free_vars t).

Lemma bot_sub_remove_nvars_filter {o} :
  forall vs l,
    @bot_sub o (remove_nvars l vs)
    = sub_filter (bot_sub vs) l.
Proof.
  induction vs; introv; simpl.
  - rw remove_nvars_nil_r; auto.
  - boolvar.
    + rw remove_nvars_cons_r; boolvar; tcsp.
    + rw remove_nvars_cons_r; boolvar; tcsp.
      simpl; rw IHvs; auto.
Qed.

Lemma sub_filter_twice {o} :
  forall (sub : @Sub o) vs,
    sub_filter (sub_filter sub vs) vs = sub_filter sub vs.
Proof.
  induction sub; introv; simpl; auto.
  destruct a; boolvar; simpl; tcsp; boolvar; simpl; tcsp.
  rw IHsub; auto.
Qed.

Lemma implies_in_bot_sub {o} :
  forall v (t : @NTerm o) vars,
    LIn (v,t) (bot_sub vars)
    -> (LIn v vars # t = mk_bottom).
Proof.
  induction vars; introv i; allsimpl; tcsp.
  dorn i; cpx.
Qed.

Lemma prog_sub_bot_sub {o} :
  forall vs, @prog_sub o (bot_sub vs).
Proof.
  induction vs; simpl; auto.
  - repeat constructor; allsimpl; sp.
  - apply prog_sub_cons; auto.
Qed.
Hint Resolve prog_sub_bot_sub : slow.

Lemma wf_sub_bot_sub {o} :
  forall vs, @wf_sub o (bot_sub vs).
Proof.
  induction vs; simpl; eauto with slow.
Qed.
Hint Resolve wf_sub_bot_sub : slow.

(*
Lemma not_marked_oterm {o} :
  forall m op (bs : list (@BTerm o)),
    not_marked m (oterm op bs)
    <=> (!LIn m (get_markers_o op) # forall b, LIn b bs -> not_marked_b m b).
Proof.
  introv.
  unfold not_marked; simpl; split; intro k.
  - dands.
    + introv i.
      destruct k.
      rw in_app_iff; sp.
    + introv i.
      rw in_app_iff in k; rw not_over_or in k; repnd.
      destruct b; simpl.
      introv j.
      destruct k; rw lin_flat_map.
      eexists; dands; eauto.
  - introv i; rw in_app_iff in i; dorn i; repnd; tcsp.
    rw lin_flat_map in i; exrepnd.
    apply k in i1.
    destruct x; allsimpl; tcsp.
Qed.
 *)

Lemma isvalue_like_ncan {o} :
  forall (bs : list (@BTerm o)) ncan,
    isvalue_like (oterm (NCan ncan) bs) -> False.
Proof.
  introv isv.
  unfold isvalue_like in isv.
  dorn isv; eauto with slow.
Qed.
Hint Resolve isvalue_like_ncan : slow.

Lemma is_value_like_ncan {o} :
  forall lib (bs : list (@BTerm o)) ncan,
    is_value_like lib (oterm (NCan ncan) bs) -> False.
Proof.
  introv isv.
  unfold is_value_like, isvalue_like in isv; repndors; tcsp.
Qed.
Hint Resolve is_value_like_ncan : slow.

(*
Lemma isvalue_like_marker {o} :
  forall (bs : list (@BTerm o)) m,
    isvalue_like (oterm (Mrk m) bs).
Proof.
  introv.
  eauto with slow.
Qed.
Hint Resolve isvalue_like_marker.
*)

Lemma reduces_in_atmost_k_steps_ncan_primarg_apply_id {o} :
  forall lib ncan (t : @NTerm o) bs u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan ncan) (nobnd (mk_apply mk_id t) :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan ncan) (nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ncan_primarg_apply_id_if_is_value_like {o} :
  forall lib ncan (t : @NTerm o) bs u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan ncan) (nobnd (mk_apply mk_id t) :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan ncan) (nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ncan_primarg_bot {o} :
  forall lib ncan (bs : list (@BTerm o)) u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan ncan) (nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; allsimpl; ginv; auto; fold_terms.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply isvalue_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_ncan_primarg_apply_id in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ncan_primarg_bot_if_is_value_like {o} :
  forall lib ncan (bs : list (@BTerm o)) u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan ncan) (nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; allsimpl; ginv; auto; fold_terms.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply is_value_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_ncan_primarg_apply_id_if_is_value_like in r0;
      exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma lsubst_aux_oterm {o} :
  forall op (bs : list (@BTerm o)) sub,
    lsubst_aux (oterm op bs) sub = oterm op (map (fun b => lsubst_bterm_aux b sub) bs).
Proof. sp. Qed.

Lemma map_cons :
  forall {A B} (f : A -> B) x l,
    map f (x :: l) = (f x) :: map f l.
Proof. sp. Qed.

Lemma lsubst_aux_bterm_nil {o} :
  forall (t : @NTerm o) sub,
    lsubst_bterm_aux (bterm [] t) sub = bterm [] (lsubst_aux t sub).
Proof.
  introv; simpl.
  rw @sub_filter_nil_r; auto.
Qed.

Lemma reduces_to_apply_id {o} :
  forall (lib : @library o) t,
    reduces_to lib (mk_apply mk_id t) t.
Proof.
  introv.
  exists 1.
  rw @reduces_in_atmost_k_steps_S.
  exists t; dands; auto.
  rw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma alpha_eq_oterm_map {o} :
  forall op (f g : @BTerm o -> @BTerm o) bs,
    default_bt = f default_bt
    -> default_bt = g default_bt
    -> (forall b, LIn b bs -> alpha_eq_bterm (f b) (g b))
    -> alpha_eq (oterm op (map f bs)) (oterm op (map g bs)).
Proof.
  introv e1 e2 imp.
  apply al_oterm; allrw map_length; auto.
  introv i.
  unfold selectbt.
  rw e1; rw map_nth; rw <- e1.
  rw e2; rw map_nth; rw <- e2.
  apply imp.
  apply nth_in; auto.
Qed.

Lemma covered_remove_nvars {o} :
  forall (t : @NTerm o) vs l,
    covered t vs
    -> disjoint l (free_vars t)
    -> covered t (remove_nvars l vs).
Proof.
  introv cov disj.
  allunfold @covered.
  allrw subvars_prop.
  introv i.
  rw in_remove_nvars; dands; auto; introv j.
  apply disj in j; sp.
Qed.

Lemma simple_subst_lsubst_aux {o} :
  forall (t : @NTerm o) u v sub,
    cl_sub sub
    -> covered u (dom_sub sub)
    -> disjoint (bound_vars t) (free_vars u)
    -> lsubst_aux (lsubst_aux t (sub_filter sub [v]))
                  [(v, lsubst_aux u sub)]
       = lsubst_aux (lsubst_aux t [(v, u)]) sub.
Proof.
  nterm_ind t as [x|f|op bs ind] Case; introv clsub cov disj2; auto.

  - Case "vterm".
    simpl; boolvar.

    + rw @sub_find_sub_filter; tcsp; simpl; boolvar; auto.

    + rw @sub_find_sub_filter_eta; simpl; tcsp.
      remember (sub_find sub x) as f; symmetry in Heqf; destruct f;
      simpl; boolvar; tcsp.

      apply sub_find_some in Heqf.
      dup clsub as cl.
      rw @cl_sub_eq in clsub.
      apply in_sub_eta in Heqf; repnd.
      apply clsub in Heqf.
      rw @lsubst_aux_trivial_cl2; auto.
      apply cl_sub_cons; dands; auto;[|apply cl_sub_nil].

      pose proof (free_vars_lsubst_aux_cl u sub) as fv.
      autodimp fv hyp.
      unfold closed; rw fv; simpl.
      apply (covered_implies_remove_nvars _ (dom_sub sub)); auto.

  - Case "oterm".
    simpl.
    allrw map_map; unfold compose.
    f_equal; apply eq_maps; introv i.

    destruct x; simpl; boolvar;
    auto; allrw @lsubst_aux_nil.

    + rw <- @sub_filter_app_r; simpl.
      rw (sub_filter_eqvars (v :: l) l sub); auto.
      rw eqvars_prop; simpl; introv; split; sp; subst; sp.

    + rw @sub_filter_swap.
      f_equal.
      dup i as ibs.
      allsimpl; rw disjoint_flat_map_l in disj2.
      apply disj2 in i; simpl in i; rw disjoint_app_l in i; repnd.
      pose proof (ind n l ibs u v (sub_filter sub l)) as h.
      repeat (autodimp h hyp).

      * apply implies_cl_sub_filter; auto.

      * rw <- @dom_sub_sub_filter.
        apply covered_remove_nvars; auto.

      * assert (lsubst_aux u (sub_filter sub l)
                = lsubst_aux u sub) as e;
        [|rw e in h; auto]; clear h.
        apply lsubst_aux_sub_filter; eauto with slow.
Qed.

Lemma implies_covered_sub_sub_filter_r {o} :
  forall (sub1 sub2 : @Sub o) l,
    covered_sub sub1 sub2
    -> disjoint l (sub_free_vars sub1)
    -> covered_sub sub1 (sub_filter sub2 l).
Proof.
  induction sub1; introv cov disj; allsimpl; auto.
  - apply covered_sub_nil.
  - destruct a.
    allrw disjoint_app_r; repnd.
    allrw @covered_sub_cons; repnd; dands; auto.
    rw <- @dom_sub_sub_filter.
    apply covered_remove_nvars; auto.
Qed.

Lemma implies_covered_sub_sub_filter_l {o} :
  forall (sub1 sub2 : @Sub o) l,
    covered_sub sub1 sub2
    -> covered_sub (sub_filter sub1 l) sub2.
Proof.
  induction sub1; introv cov; allsimpl; auto.
  destruct a; boolvar; allsimpl;
  allrw @covered_sub_cons; repnd; dands; auto.
Qed.

(* is bottom or marker *)
Definition is_bm {o} (t : @NTerm o) :=
  t = mk_bottom [+] {m : marker & t = mk_marker m}.

Definition bm_sub {o} (sub : @Sub o) := sub_range_sat sub is_bm.

Definition bm_sub_implies_cl_sub {o} :
  forall (sub : @Sub o), bm_sub sub -> cl_sub sub.
Proof.
  introv bm.
  unfold bm_sub in bm; unfold cl_sub.
  allunfold @sub_range_sat; introv i.
  apply bm in i.
  dorn i; exrepnd; subst; tcsp.
Qed.

Lemma map_nth2 :
  forall {A B} (d : A) (z : B) (f : A -> B) (l : list A) (n : nat),
    z = f d
    -> nth n (map f l) z = f (nth n l d).
Proof.
  introv e; subst; apply map_nth.
Qed.

Lemma cswap_sub_sub_filter_same {o} :
  forall (sub : @Sub o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> disjoint vs2 (dom_sub sub)
    -> length vs1 = length vs2
    -> cswap_sub (mk_swapping vs1 vs2) (sub_filter sub vs1)
       = sub_filter (cswap_sub (mk_swapping vs1 vs2) sub) vs2.
Proof.
  induction sub; introv norep disj1 disj2 len; simpl; auto.
  allsimpl; allrw disjoint_cons_r; repnd.

  destruct a; allsimpl; boolvar; simpl; tcsp;
  try (complete (pose proof (swapvar_implies3 vs1 vs2 a0) as h; repeat (autodimp h hyp); tcsp));
  try (complete (rw swapvar_not_in in Heqb0; tcsp));
  try (complete (f_equal; apply IHsub; tcsp)).
Qed.

(*
Lemma swap_sub_sub_filter_same_cl_sub {o} :
  forall (sub : @Sub o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> disjoint vs2 (dom_sub sub)
    -> length vs1 = length vs2
    -> cl_sub sub
    -> swap_sub (mk_swapping vs1 vs2) (sub_filter sub vs1)
       = sub_filter sub vs1.
Proof.
  induction sub; introv norep disj1 disj2 len cl; simpl; auto.
  allsimpl; allrw disjoint_cons_r; repnd.
  allsimpl; allrw @cl_sub_cons; repnd.

  boolvar; simpl; tcsp.

  rw IHsub; auto; clear IHsub.
  pose proof (swapvar_not_in a0 vs1 vs2) as e.
  repeat (autodimp e hyp); rw e; clear e.

Qed.
*)

Lemma implies_disjoint_remove_nvars :
  forall vs vs1 vs2,
    disjoint vs vs1
    -> disjoint vs (remove_nvars vs2 vs1).
Proof.
  introv disj i j.
  apply disj in i.
  rw in_remove_nvars in j; sp.
Qed.

Lemma flat_map_free_vars_range_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub -> flat_map free_vars (range sub) = [].
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a; allsimpl.
  rw @cl_sub_cons in cl; repnd.
  rw IHsub; auto.
  rw cl0; auto.
Qed.

Lemma remove_nvars_nil_if_subvars :
  forall vs1 vs2,
    subvars vs1 vs2 -> remove_nvars vs2 vs1 = [].
Proof.
  induction vs1; introv sv; allsimpl; auto.
  - rw remove_nvars_nil_r; auto.
  - rw subvars_cons_l in sv; repnd.
    rw remove_nvars_cons_r; boolvar; sp.
Qed.

Lemma lsubst_aux_alpha_congr_same_cl_sub {o} :
  forall (t1 t2 : @NTerm o) sub,
    alpha_eq t1 t2
    -> cl_sub sub
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub).
Proof.
  introv aeq cl.
  pose proof (sub_eta sub) as e.
  rw e; clear e.
  apply lsubst_aux_alpha_congr; auto.
  - rw @sub_eta_length; auto.
  - rw @sub_eta_length; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
Qed.

Lemma eqvars_free_vars_disjoint_aux2 {o} :
  forall (t : @NTerm o) sub,
    disjoint_bv_sub t sub
    -> eqvars (free_vars (lsubst_aux t sub))
              (remove_nvars (dom_sub sub) (free_vars t)
               ++ sub_free_vars (sub_keep_first sub (free_vars t))).
Proof.
  introv disj.
  apply eqvars_free_vars_disjoint_aux.
  introv i.
  unfold disjoint_bv_sub, sub_range_sat in disj.
  eapply disj; eauto.
Qed.

Lemma disjoint_bv_sub_nil {o} :
  forall (t : @NTerm o), disjoint_bv_sub t [].
Proof.
  introv.
  unfold disjoint_bv_sub, sub_range_sat; simpl; sp.
Qed.

Lemma disjoint_bv_sub_cons {o} :
  forall (t : @NTerm o) v u sub,
    disjoint_bv_sub t ((v,u) :: sub)
    <=> (disjoint (bound_vars t) (free_vars u) # disjoint_bv_sub t sub).
Proof.
  introv.
  unfold disjoint_bv_sub, sub_range_sat; simpl; split; intro k; repnd; dands; introv.
  - intros i j.
    pose proof (k v u) as h; autodimp h hyp.
    apply h in j; sp.
  - intro i.
    eapply k; eauto.
  - intro i; dorn i; cpx.
    + apply disjoint_sym; auto.
    + eapply k; eauto.
Qed.

Lemma disjoint_bv_sub_var_ren {o} :
  forall (t : @NTerm o) vs1 vs2,
    length vs1 = length vs2
    -> (disjoint_bv_sub t (var_ren vs1 vs2) <=> disjoint (bound_vars t) vs2).
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; auto; split; intro k; auto;
  allrw @var_ren_nil_l; auto; cpx.
  - apply disjoint_bv_sub_nil.
  - rw @var_ren_cons in k.
    rw disjoint_cons_r.
    rw @disjoint_bv_sub_cons in k; allsimpl; repnd; dands; auto.
    + apply IHvs1; auto.
    + allrw disjoint_singleton_r; auto.
  - rw @var_ren_cons.
    rw @disjoint_bv_sub_cons; simpl.
    rw disjoint_cons_r in k; repnd.
    rw disjoint_singleton_r; dands; auto.
    apply IHvs1; auto.
Qed.

Lemma sub_free_vars_sub_keep_first_subvars {o} :
  forall (sub : @Sub o) vs,
    subvars (sub_free_vars (sub_keep_first sub vs))
            (sub_free_vars sub).
Proof.
  introv.
  rw subvars_prop; introv i.
  apply @in_sub_free_vars in i; exrepnd.
  apply in_sub_keep_first in i0; repnd.
  apply sub_find_some in i2.
  apply in_sub_free_vars_iff.
  exists x0 t; sp.
Qed.

Lemma sub_free_vars_var_ren {o} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> @sub_free_vars o (var_ren vs1 vs2) = vs2.
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  fold (@var_ren o vs1 vs2).
  rw IHvs1; auto.
Qed.

Lemma lsubst_aux_nest_swap_filter_cl_sub {o} :
  forall (t : @NTerm o) sub1 sub2 vs,
    eqvars vs (dom_sub sub2)
    -> cl_sub sub1
    -> disjoint (dom_sub sub1) (flat_map free_vars (range sub2))
    -> disjoint (flat_map bound_vars (range sub1)) (flat_map free_vars (range sub2))
    -> disjoint (bound_vars t) (flat_map free_vars (range sub2))
    -> disjoint vs (flat_map free_vars (range sub2))
    -> lsubst_aux (lsubst_aux t (sub_filter sub1 vs)) sub2
       = lsubst_aux (lsubst_aux t sub2) sub1.
Proof.
  introv sv cl disj1 disj2 disj3 disj4.

  pose proof (lsubst_aux_nest_swap2
                t
                (sub_filter sub1 vs)
                sub2) as h; simpl in h.
  repeat (autodimp h hyp).

  { rw <- @dom_sub_sub_filter.
    rw disjoint_remove_nvars_l.
    eapply subvars_disjoint_r;[|exact disj1].
    apply subvars_remove_nvars; auto.
    apply subvars_app_weak_l; auto. }

  { rw @flat_map_free_vars_range_cl_sub; auto.
    apply implies_cl_sub_filter; auto. }

  { rw <- @dom_sub_sub_filter.
    rw disjoint_remove_nvars_l.
    introv i j.
    rw in_remove_nvars in j; repnd.
    rw eqvars_prop in sv.
    apply sv in j0; sp. }

  { eapply subvars_disjoint_l;[|exact disj2].
    apply subvars_flat_map; introv i.
    apply in_range in i; exrepnd.
    apply in_sub_filter in i0; repnd.
    eapply implies_subvars_flat_map_r; eauto.
    apply in_range_iff; eexists; eauto. }

  { rw @flat_map_free_vars_range_cl_sub; auto.
    apply implies_cl_sub_filter; auto. }

  { rw @flat_map_free_vars_range_cl_sub; auto.
    apply implies_cl_sub_filter; auto. }

  rw h; clear h.

  rw @lsubst_aux_sub_filter; auto.

  { pose proof (eqvars_free_vars_disjoint_aux2 t sub2) as eqv.
    autodimp eqv hyp.
    { unfold disjoint_bv_sub, sub_range_sat; introv i.
      rw disjoint_flat_map_r in disj3.
      apply disjoint_sym; apply disj3.
      apply in_range_iff; eexists; eauto. }
    apply eqvars_sym in eqv.
    eapply eqvars_disjoint;[exact eqv|]; clear eqv.
    rw disjoint_app_l; dands.
    { apply disjoint_remove_nvars_l.
      apply eqvars_sym in sv.
      erewrite remove_nvars_if_eqvars;[|exact sv].
      rw remove_nvars_eq; auto. }
    pose proof (sub_free_vars_sub_keep_first_subvars sub2 (free_vars t)) as svf.
    eapply subvars_disjoint_l;[exact svf|]; auto.
    pose proof (sub_eta sub2) as e; rw e.
    rw @sub_free_vars_combine; auto;[|rw @sub_eta_length; auto].
    apply disjoint_sym; auto. }
Qed.

Lemma simple_lsubst_aux_lsubst_aux_aeq {o} :
  forall (t t' : @NTerm o) u v sub,
    cl_sub sub
    -> covered u (dom_sub sub)
    -> disjoint (bound_vars t') (free_vars u)
    -> alphaeq t t'
    -> alphaeq
         (lsubst_aux (lsubst_aux t (sub_filter sub [v]))
                     [(v, lsubst_aux u sub)])
         (lsubst_aux (lsubst_aux t' [(v, u)]) sub).
Proof.
  introv cl cov disj aeq.
  pose proof (simple_subst_lsubst_aux t' u v sub cl cov disj) as h.
  rw <- h; clear h.
  apply alphaeq_eq in aeq.
  apply alphaeq_eq.
  repeat (apply lsubst_aux_alpha_congr_same_cl_sub); auto.
  - apply implies_cl_sub_filter; auto.
  - apply cl_sub_cons; dands;[|apply cl_sub_nil].
    unfold closed; rw @free_vars_lsubst_aux_cl; auto.
    eapply covered_implies_remove_nvars;[|eauto]; auto.
Qed.

Lemma implies_covered_cons_weak {o} :
  forall (t : @NTerm o) v vs,
    covered t vs
    -> covered t (v :: vs).
Proof.
  introv cov.
  allunfold @covered.
  allrw subvars_prop; simpl; introv i.
  apply cov in i; sp.
Qed.

Lemma simple_subst_lsubst_aux_aeq {o} :
  forall (t : @NTerm o) v u sub z,
    closed z
    -> cl_sub sub
    -> covered u (dom_sub sub)
    -> alpha_eq
         (subst
            (lsubst_aux t (sub_filter sub [v]))
            v
            (lsubst_aux u ((v, z) :: sub)))
         (lsubst_aux (subst t v u) ((v, z) :: sub)).
Proof.
  introv clz clsub cov.
  unfold subst, lsubst; boolvar; allsimpl; allrw app_nil_r;
  try (complete (provefalse; destruct n;
                 pose proof (free_vars_lsubst_aux_cl u ((v,z) :: sub)) as fv;
                 autodimp fv hyp;[apply cl_sub_cons; dands; auto|];
                 pose proof (covered_implies_remove_nvars
                               u (dom_sub sub) (dom_sub ((v, z) :: sub))) as h;
                 repeat (autodimp h hyp);[apply subvars_cons_r; auto|];
                 rw h in fv; clear h; rw fv; auto)).

  - pose proof (simple_subst_lsubst_aux t u v ((v,z) :: sub)) as h.
    repeat (autodimp h hyp).
    + apply cl_sub_cons; sp.
    + simpl; apply implies_covered_cons_weak; auto.
    + simpl in h; boolvar; tcsp; auto;[rw h; auto|allrw not_over_or; sp].

  - pose proof (change_bvars_alpha_spec t (free_vars u)) as h; simpl in h; repnd.
    remember (change_bvars_alpha (free_vars u) t) as t'; clear Heqt'.
    pose proof (simple_lsubst_aux_lsubst_aux_aeq t t' u v ((v,z) :: sub)) as k.
    repeat (autodimp k hyp).
    + apply cl_sub_cons; dands; auto.
    + simpl; apply implies_covered_cons_weak; auto.
    + eauto with slow.
    + apply alphaeq_eq; auto.
    + simpl in k; boolvar; tcsp; auto;[apply alphaeq_eq; auto|allrw not_over_or; sp].
Qed.

Lemma simple_subst_lsubst_aux_aeq2 {o} :
  forall (t : @NTerm o) v u sub,
    cl_sub sub
    -> covered u (dom_sub sub)
    -> alpha_eq
         (subst
            (lsubst_aux t (sub_filter sub [v]))
            v
            (lsubst_aux u sub))
         (lsubst_aux (subst t v u) sub).
Proof.
  introv cl cov.
  unfold subst, lsubst; allsimpl; boolvar; allsimpl; allrw app_nil_r;
  try (complete (provefalse; destruct n;
                 pose proof (free_vars_lsubst_aux_cl u sub) as fv;
                 autodimp fv hyp;
                 pose proof (covered_implies_remove_nvars
                               u (dom_sub sub) (dom_sub sub)) as h;
                 repeat (autodimp h hyp);
                 rw h in fv; clear h; rw fv; auto)).

  - rw @simple_subst_lsubst_aux; auto.

  - pose proof (change_bvars_alpha_spec t (free_vars u)) as h; simpl in h; repnd.
    remember (change_bvars_alpha (free_vars u) t) as t'; clear Heqt'.
    apply alphaeq_eq.
    apply simple_lsubst_aux_lsubst_aux_aeq; eauto with slow.
    apply alphaeq_eq; auto.
Qed.

(*
(*

   we're going to use: simple_lsubst_aux_lsubst_aux_sub_aeq
   below.  Can we use something else that does not require the cl_sub
   and uses disjointness?

   BEGINNING OF MESSING AROUND

*)

Lemma simple_lsubst_aux_lsubst_aux_sub_aeq2 {o} :
  forall (t t' : @NTerm o) sub1 sub2,
    cl_sub sub2
    -> disjoint (bound_vars t') (sub_free_vars sub1)
    -> disjoint (bound_vars (lsubst_aux t (sub_filter sub2 (dom_sub sub1))))
                (flat_map free_vars (range (lsubst_aux_sub sub1 sub2)))
    -> alpha_eq t t'
    -> alpha_eq
         (lsubst_aux (lsubst_aux t (sub_filter sub2 (dom_sub sub1)))
                     (lsubst_aux_sub sub1 sub2))
         (lsubst_aux (lsubst_aux t' sub1) sub2).
Proof.
  introv cl disj1 disj2 aeq.
  pose proof (simple_lsubst_aux_lsubst_aux_sub t' sub1 sub2 cl disj1) as h.
  rw <- h; clear h.


(* In this version we don't collect the bound variables from bterms that are closed
   because on closed terms lsubst_aux doesn't capture *)
Fixpoint bound_vars_ncl {p} (t : @NTerm p) : list NVar :=
  match t with
  | vterm v => []
  | oterm op bts => flat_map bound_vars_bterm_ncl bts
  end
 with bound_vars_bterm_ncl {p} (bt : BTerm) :=
  match bt with
  | bterm lv nt =>
    if sub_vars (free_vars nt) lv
    then []
    else lv ++ bound_vars_ncl nt
  end.

Definition lsubst_alpha3_congr_aux_ncl {p} t1 t2 lvi lnt1 lnt2 :=
  @alpha_eq3 p [] t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars_ncl t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars_ncl t2)
  -> bin_rel_nterm (alpha_eq3 []) lnt1 lnt2
  -> alpha_eq3 [] (lsubst_aux t1 (combine lvi lnt1)) (lsubst_aux t2 (combine lvi lnt2)).

Definition lsubst_alphabt3_congr_aux_ncl {p} bt1 bt2 lvi lnt1 lnt2 :=
  @alpha_eq_bterm3 p [] bt1 bt2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars_bterm_ncl bt1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars_bterm_ncl bt2)
  -> bin_rel_nterm (alpha_eq3 []) lnt1 lnt2
  -> alpha_eq_bterm3 [] (lsubst_bterm_aux bt1 (combine lvi lnt1))
                    (lsubst_bterm_aux bt2 (combine lvi lnt2)).

Hint Unfold lsubst_alphabt3_congr_aux_ncl.
Hint Unfold lsubst_alpha3_congr_aux_ncl.

Theorem lsubst_alphabt3_congr_ncl {p} :
  forall bnt1 blv1,
    (forall t1' t2 lvi lnt1 lnt2,
       (@size p t1' <= @size p bnt1)
       -> lsubst_alpha3_congr_aux_ncl t1' t2 lvi lnt1 lnt2)
    -> forall bt2 lvi lnt1 lnt2,
         lsubst_alphabt3_congr_aux_ncl
           (bterm blv1 bnt1)
           bt2 lvi lnt1 lnt2.
Proof.
  introv Hind Hlt1 H1len H2len H1dis H2dis Hall.
  destruct bt2 as [blv2 bnt2].
  applydup @alpha_eq3_bterm_lenbvars in Hlt1 as Hblen.
  pose proof (fresh_vars
                (length blv1)
                (all_vars bnt1
                          ++ all_vars bnt2
                          ++ flat_map free_vars lnt1
                          ++ flat_map free_vars lnt2
                          ++ flat_map bound_vars lnt1
                          ++ flat_map bound_vars lnt2
                          ++ all_vars (lsubst_aux bnt1 (combine (dom_sub (sub_filter (combine lvi lnt1) blv1)) (range (sub_filter (combine lvi lnt1) blv1))))
                          ++ all_vars (lsubst_aux bnt2 (combine (dom_sub (sub_filter (combine lvi lnt2) blv2)) (range (sub_filter (combine lvi lnt2) blv2))))
                          ++ lvi
                          ++ blv1
                          ++ blv2))
    as Hfresh. exrepnd.
  apply alpha3bt_change_var with (lv:=lvn) in Hlt1;sp;[| disjoint_reasoningv;fail].
  allsimpl.

  repeat( rewrite (bvar_renamings_subst_disjoint_bound_vars);
          [|
           apply disjoint_sub_as_flat_map; rewrite dom_range_combine;sp;
           disjoint_reasoningv]).
  allsimpl.
  rename Hlt1 into XX.
  pose proof (sub_eta (sub_filter (combine lvi lnt1) blv1)) as Xsf1eta;
    pose proof (sub_eta (sub_filter (combine lvi lnt2) blv2)) as Xsf2eta;
    pose proof (sub_eta_length (sub_filter (combine lvi lnt1) blv1)) as X1len;
    pose proof (sub_eta_length (sub_filter (combine lvi lnt2) blv2)) as X2len;
    remember (dom_sub (sub_filter (combine lvi lnt1) blv1)) as lsvi1;
    remember (dom_sub (sub_filter (combine lvi lnt2) blv2)) as lsvi2;
    remember (range (sub_filter (combine lvi lnt1) blv1)) as lsnt1;
    remember (range (sub_filter (combine lvi lnt2) blv2)) as lsnt2.

  rewrite Xsf1eta.
  rewrite Xsf2eta.
  unfold lsubst_alpha3_congr_aux in Hind.
  simpl in Hind.
  apply al_bterm3 with (lv:=lvn); auto.
    + disjoint_reasoningv.

    + eapply Hind with (lvi:=lvi)  (lnt1:=lnt1) (lnt2:=lnt2) in XX; eauto;
      [|rewrite lsubst_aux_allvars_preserves_size;[omega|];apply allvars_combine; fail].

      unfold var_ren.
      (** swapping below requires the domains to be disjoint *)
      rewrite lsubst_aux_nest_swap2; spcls; simpl;
      disjoint_reasoningv;try(disjoint_sub_filter; fail).

      Focus 2. rw Heqlsvi1.
        rw <- @dom_sub_sub_filter.
        spcls. apply disjoint_remove_nvars.

      apply alpha_eq3_sym.
      rewrite lsubst_aux_nest_swap2; spcls; simpl;
      disjoint_reasoningv;try(disjoint_sub_filter; fail).

      Focus 2. rw Heqlsvi2.
        rw <- @dom_sub_sub_filter.
        spcls. apply disjoint_remove_nvars.


      rw <- Xsf2eta. rw @lsubst_aux_sub_filter2.
      rw <- Xsf1eta. rw @lsubst_aux_sub_filter2.
      apply alpha_eq3_sym. unfold var_ren in XX;sp.
      * unfold disjoint_bv_sub.
         rw @disjoint_sub_as_flat_map.
         spcls.
         apply disjoint_sym. apply disjoint_bound_vars_lsubst_aux;spcls;disjoint_reasoningv.
      * introv Hin. apply free_vars_lsubst_aux2 in Hin. 
      
          simpl_sub.
          dorn Hin;exrepnd; auto;[].
          apply in_var_ren in Hin0. exrepnd.
          subst. allsimpl. dorn Hin1;subst;try(sp;fail);[].
          apply Hfresh10;sp.

         unfold disjoint_bv_sub.
         rw @disjoint_sub_as_flat_map.
         spcls. disjoint_reasoningv.

      * unfold disjoint_bv_sub.
         rw @disjoint_sub_as_flat_map.
         spcls.
         apply disjoint_sym. apply disjoint_bound_vars_lsubst_aux;spcls;disjoint_reasoningv.

      * introv Hin. apply free_vars_lsubst_aux2 in Hin. 
      
          simpl_sub.
          dorn Hin;exrepnd; auto;[].
          apply in_var_ren in Hin0. exrepnd.
          subst. allsimpl. dorn Hin1;subst;try(sp;fail);[].
          apply Hfresh2;sp.

         unfold disjoint_bv_sub.
         rw @disjoint_sub_as_flat_map.
         spcls. disjoint_reasoningv.
Qed.

Theorem lsubst_alpha3_congr_aux_ncl {p} : forall t1 t2 lvi lnt1 lnt2,
  @alpha_eq3 p [] t1 t2
  -> length lvi = length lnt1
  -> length lvi = length lnt2
  -> disjoint (flat_map free_vars lnt1) (bound_vars_ncl t1)
  -> disjoint (flat_map free_vars lnt2) (bound_vars_ncl t2)
  -> bin_rel_nterm (alpha_eq3 [] ) lnt1 lnt2
  -> alpha_eq3 [] (lsubst_aux t1 (combine lvi lnt1)) (lsubst_aux t2 (combine lvi lnt2)).
Proof.
  nterm_ind1s t1 as [v1 | o1 lbt1 Hind] Case; introv Hal H1len H2len H1dis H2dis Hall; inverts Hal as Hlen Hal.
  - Case "vterm". simpl.
    destructrn (sub_find (combine lvi lnt1) v1) as [s1s|n1n] H1sn;
    destructrn (sub_find (combine lvi lnt2) v1) as [s2s|n2n] H2sn; allsimpl;sp.
    + symmetry in HeqH2sn. symmetry in HeqH1sn.
      eapply sub_find_some2_first in HeqH1sn; eauto. exrepnd.
      repnud Hall.
      repnud Hall.
      assert(n < length lnt1) as Hlt by congruence.
      pose proof (Hall _ Hlt).
      rewrite nth_indep with (d' := default_nterm) in HeqH1sn0; try(congruence).
      rewrite nth_indep with (d' := default_nterm) in HeqH1sn4; try(congruence).
    + provefalse. symmetry in  HeqH1sn. eapply sub_find_some_none_contra in HeqH1sn ; eauto.
    + provefalse. symmetry in  HeqH2sn. eapply @sub_find_some_none_contra with(lnt2:=lnt1) in HeqH2sn; eauto.

  - Case "oterm". simpl. constructor;
    repeat(rewrite map_length); auto.
    introv Hlt. rewrite selectbt_map; auto.
    duplicate Hlt. rewrite Hlen in Hlt0.
    rewrite selectbt_map; auto.
    fold @lsubst_bterm_aux.
    applydup Hal in Hlt.
    clear Hal.
    pose proof (selectbt_in2 n lbt1 Hlt) as [bt99 pp].
    exrepnd. destruct bt99 as [blv1 bnt1].
    rewrite pp. rewrite pp in Hlt1.
    pose proof (selectbt_in2 n lbt2 Hlt0) as [bt99 p2p].
    exrepnd. destruct bt99 as [blv2 bnt2].
    rewrite p2p. rewrite p2p in Hlt1.
    simpl in H1dis, H2dis.
    eapply (@disjoint_lbt_bt2 p) in H1dis; eauto. repnd.
    eapply (@disjoint_lbt_bt2 p) in H2dis; eauto. repnd.
    apply lsubst_alphabt3_congr_auxp; allsimpl; spc; disjoint_reasoningv;[].
    introv. intros. eapply Hind with (nt:=bnt1); eauto.
Qed.

Lemma lsubst_aux_alpha_congr_disj {o} :
  forall (t1 t2 : @NTerm o) sub,
    alpha_eq t1 t2
    -> disjoint (bound_vars t1) (sub_free_vars sub)
    -> disjoint (bound_vars t2) (sub_free_vars sub)
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub).
Proof.
  introv aeq cl.
  pose proof (sub_eta sub) as e.
  rw e; clear e.
  apply lsubst_aux_alpha_congr; auto.
  - rw @sub_eta_length; auto.
  - rw @sub_eta_length; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - rw @flat_map_free_vars_range_cl_sub; auto.
  - unfold bin_rel_nterm, binrel_list; allrw map_length; dands; auto.
Qed.


  repeat (apply lsubst_aux_alpha_congr_same_cl_sub); auto.
  - apply implies_cl_sub_filter; auto.
  - apply implies_cl_sub_lsubst_aux_sub; auto.
Qed.

(*

   END OF MESSING AROUND

*)
*)

Lemma cl_sub_bot_sub {o} :
  forall vs, @cl_sub o (bot_sub vs).
Proof.
  introv.
  unfold bot_sub, cl_sub, sub_range_sat.
  introv i; rw in_map_iff in i; exrepnd; cpx.
Qed.
Hint Immediate cl_sub_bot_sub.

Lemma cl_sub_bot_sub_fv {o} :
  forall (t : @NTerm o), cl_sub (bot_sub_fv t).
Proof.
  unfold bot_sub_fv; auto.
Qed.
Hint Immediate cl_sub_bot_sub_fv.

Lemma dom_sub_bot_sub {o} :
  forall vs, @dom_sub o (bot_sub vs) = vs.
Proof.
  induction vs; simpl; auto.
  rw IHvs; auto.
Qed.

Lemma dom_sub_bot_sub_fv {o} :
  forall (t : @NTerm o), dom_sub (bot_sub_fv t) = free_vars t.
Proof.
  introv; unfold bot_sub_fv.
  apply dom_sub_bot_sub.
Qed.

Lemma compute_step_ncompop_can1 {o} :
  forall (lib : @library o) comp can ncbts rest x,
    compute_step lib
      (oterm (NCan (NCompOp comp))
             (bterm [] (oterm (Can can) ncbts) :: rest)) = csuccess x
    -> co_wf_def comp can ncbts
       # {op : Opid
       & {bs : list BTerm
       & {l : list BTerm
       & rest = (bterm [] (oterm op bs)) :: l }}}.
Proof.
  introv c; allsimpl.
  apply compute_step_ncompop_can1_success in c; repnd; dands; auto.
  repndors; exrepnd; subst.
  - exists (Can can') ([] : list (@BTerm o)) [nobnd t1, nobnd t2]; auto.
  - unfold isnoncan_like in c3; repndors.
    + apply isnoncan_implies in c3; exrepnd; subst.
      exists (@NCan o c) bterms bs'; auto.
    + apply isabs_implies in c3; exrepnd; subst.
      exists (@Abs o abs) bterms bs'; auto.
  - apply isexc_implies2 in c1; exrepnd; subst.
    exists (@Exc o) l bs'; auto.
Qed.

Lemma compute_step_narithop_can1 {o} :
  forall (lib : @library o) a can ncbts rest x,
    compute_step lib
      (oterm (NCan (NArithOp a))
             (bterm [] (oterm (Can can) ncbts) :: rest)) = csuccess x
    -> ca_wf_def can ncbts
       # {op : Opid
       & {bs : list BTerm
       & {l : list BTerm
       & rest = (bterm [] (oterm op bs)) :: l }}}.
Proof.
  introv c; allsimpl.
  apply compute_step_narithop_can1_success in c; repnd; dands; auto.
  repndors; exrepnd; subst.
  - exists (Can can') ([] : list (@BTerm o)) ([] : list (@BTerm o)); auto.
  - unfold isnoncan_like in c3; repndors.
    + apply isnoncan_implies in c3; exrepnd; subst.
      exists (@NCan o c) bterms bs'; auto.
    + apply isabs_implies in c3; exrepnd; subst.
      exists (@Abs o abs) bterms bs'; auto.
  - apply isexc_implies2 in c1; exrepnd; subst.
    exists (@Exc o) l bs'; auto.
Qed.

Lemma sub_find_bot_sub_some_if_in {o} :
  forall v vs,
    LIn v vs
    -> @sub_find o (bot_sub vs) v = Some mk_bot.
Proof.
  induction vs; introv i; allsimpl; cpx.
  boolvar; auto.
  dorn i; subst; sp.
Qed.

Lemma sub_find_bot_sub_fv_some_if_in_free_vars {o} :
  forall (t : @NTerm o) v,
    LIn v (free_vars t)
    -> sub_find (bot_sub_fv t) v = Some mk_bot.
Proof.
  introv i.
  unfold bot_sub_fv.
  apply sub_find_bot_sub_some_if_in; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ncompop_primarg2_apply_id {o} :
  forall lib ncop can l (t : @NTerm o) bs u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NCompOp ncop))
                (nobnd (oterm (Can can) l)
                       :: nobnd (mk_apply mk_id t)
                       :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan (NCompOp ncop)) (nobnd (oterm (Can can) l) :: nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
    dcwf h; allsimpl; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_ncompop_primarg2_bot {o} :
  forall lib ncop can l (bs : list (@BTerm o)) u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NCompOp ncop)) (nobnd (oterm (Can can) l) :: nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv; auto; fold_terms.
    dcwf h; allsimpl; ginv.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply isvalue_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_ncompop_primarg2_apply_id in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma reduces_in_atmost_k_steps_narithop_primarg2_apply_id {o} :
  forall lib naop can l (t : @NTerm o) bs u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NArithOp naop))
                (nobnd (oterm (Can can) l)
                       :: nobnd (mk_apply mk_id t)
                       :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan (NArithOp naop)) (nobnd (oterm (Can can) l) :: nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
    dcwf h; allsimpl; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_narithop_primarg2_bot {o} :
  forall lib naop can l (bs : list (@BTerm o)) u k,
    isvalue_like u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NArithOp naop)) (nobnd (oterm (Can can) l) :: nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply isvalue_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv; auto; fold_terms.
    dcwf h; allsimpl; ginv.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply isvalue_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_narithop_primarg2_apply_id in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma reduces_in_atmost_k_steps_ncompop_primarg2_apply_id_if_is_value_like {o} :
  forall lib ncop can l (t : @NTerm o) bs u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NCompOp ncop))
                (nobnd (oterm (Can can) l)
                       :: nobnd (mk_apply mk_id t)
                       :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan (NCompOp ncop)) (nobnd (oterm (Can can) l) :: nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
    dcwf h; allsimpl; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_ncompop_primarg2_bot_if_is_value_like {o} :
  forall lib ncop can l (bs : list (@BTerm o)) u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NCompOp ncop)) (nobnd (oterm (Can can) l) :: nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv; auto; fold_terms.
    dcwf h; allsimpl; ginv.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply is_value_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_ncompop_primarg2_apply_id_if_is_value_like in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma reduces_in_atmost_k_steps_narithop_primarg2_apply_id_if_is_value_like {o} :
  forall lib naop can l (t : @NTerm o) bs u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NArithOp naop))
                (nobnd (oterm (Can can) l)
                       :: nobnd (mk_apply mk_id t)
                       :: bs)) u k
    -> {n : nat
        & k = S n
        # reduces_in_atmost_k_steps
            lib
            (oterm (NCan (NArithOp naop)) (nobnd (oterm (Can can) l) :: nobnd t :: bs)) u n }.
Proof.
  introv isv r.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    exists k; dands; auto.
    csunf r1; simpl in r1; ginv; auto.
    dcwf h; allsimpl; ginv; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_narithop_primarg2_bot_if_is_value_like {o} :
  forall lib naop can l (bs : list (@BTerm o)) u k,
    is_value_like lib u
    -> reduces_in_atmost_k_steps
         lib
         (oterm (NCan (NArithOp naop)) (nobnd (oterm (Can can) l) :: nobnd mk_bot :: bs)) u k
    -> False.
Proof.
  introv isv r.
  induction k as [k ind] using comp_ind_type.
  destruct k.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    apply is_value_like_ncan in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv; auto; fold_terms.
    dcwf h; allsimpl; ginv.
    destruct k.

    + rw @reduces_in_atmost_k_steps_0 in r0; subst.
      apply is_value_like_ncan in isv; sp.

    + apply reduces_in_atmost_k_steps_narithop_primarg2_apply_id_if_is_value_like in r0; exrepnd; ginv; auto.
      apply ind in r1; auto.
Qed.

Lemma isvalue_like_implies_is_value_like {o} :
  forall lib (t : @NTerm o),
    isvalue_like t -> is_value_like lib t.
Proof. sp.
Qed.
Hint Resolve isvalue_like_implies_is_value_like : slow.

Lemma hasvalue_like_implies_has_value_like {o} :
  forall lib (t : @NTerm o),
    hasvalue_like lib t -> has_value_like lib t.
Proof.
  introv hv.
  unfold has_value_like.
  unfold hasvalue_like in hv.
  exrepnd.
  eexists; dands; eauto with slow.
Qed.
Hint Resolve hasvalue_like_implies_has_value_like : slow.

Lemma is_value_like_mk_marker {o} :
  forall (lib : @library o) m,
    is_mrk lib m -> is_value_like lib (mk_marker m).
Proof.
  unfold is_value_like; simpl; introv ism.
  unfold is_mrk, ismrk in ism; allsimpl; sp.
Qed.
Hint Resolve is_value_like_mk_marker : slow.

Lemma is_value_like_bot {o} :
  forall (lib : @library o), is_value_like lib mk_bot -> False.
Proof.
  introv isv.
  unfold is_value_like in isv; repndors; tcsp.
  apply isvalue_like_bot in isv; sp.
Qed.

Lemma is_value_like_apply {o} :
  forall lib (a b : @NTerm o), is_value_like lib (mk_apply a b) -> False.
Proof.
  introv isv.
  unfold is_value_like in isv; repndors; tcsp.
  apply isvalue_like_apply in isv; sp.
Qed.

Lemma not_bot_reduces_to_is_value_like {p} :
  forall lib (t : @NTerm p), is_value_like lib t -> !reduces_to lib mk_bot t.
Proof.
  introv isv r.
  unfold reduces_to in r; sp.
  revert t isv r.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct k.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    apply is_value_like_bot in isv; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; simpl in r1; ginv.
    destruct k.

    + allrw @reduces_in_atmost_k_steps_0; subst.
      apply is_value_like_apply in isv; sp.

    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      csunf r0; simpl in r0; ginv.
      unfold apply_bterm, lsubst in r1; allsimpl.
      apply ind in r1; tcsp.
Qed.

Lemma not_fresh_id_reduces_to_is_value_like {p} :
  forall lib (t : @NTerm p) v,
    is_value_like lib t
    -> !reduces_to lib (mk_fresh v (mk_var v)) t.
Proof.
  introv isv r.
  unfold reduces_to in r; sp.
  revert t isv r.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct k.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold is_value_like, isvalue_like in isv; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; simpl in r1; ginv.
    boolvar; ginv.
    apply ind in r0; tcsp.
Qed.

Lemma has_value_like_if_marks {o} :
  forall lib (t : @NTerm o),
    marks lib t
    -> has_value_like lib t.
Proof.
  introv hv.
  unfold marks in hv; exrepnd.
  unfold computes_to_marker in hv0; repnd.
  unfold has_value_like.
  exists (@mk_marker o m); dands; eauto with slow.
Qed.
Hint Resolve has_value_like_if_marks : slow.

Lemma bottom_doesnt_converge_to_value_like {p} :
  forall (lib : @library p),
    converges_to_value_like lib mk_bottom
    -> False.
Proof.
  introv Hcv.
  unfold converges_to_value_like, reduces_to, reduces_in_atmost_k_steps in Hcv; exrepnd.
  unfold_all_mk.
  induction k as [k  Hind] using comp_ind.
  destruct k.

  - rw @compute_at_most_k_steps_0 in Hcv2; ginv; fold_terms.
    apply isvalue_like_bot in Hcv0; sp.

  - rw @compute_at_most_k_steps_eq_f in Hcv2.
    rw @compute_at_most_k_stepsf_S in Hcv2; allsimpl.
    destruct k.

    + rw @compute_at_most_k_stepsf_0 in Hcv2; ginv; fold_terms.
      apply isvalue_like_apply in Hcv0; sp.

    + rw @compute_at_most_k_stepsf_S in Hcv2; allsimpl.
      unfold apply_bterm in Hcv2.
      simpl in Hcv2.
      revert Hcv2.
      change_to_lsubst_aux4; simpl; try (complete sp).
      intro c.
      rw <- @compute_at_most_k_steps_eq_f in c.
      apply Hind in c; sp.
Qed.

Lemma bottom_doesnt_converge_to_is_value_like {p} :
  forall (lib : @library p),
    converges_to_is_value_like lib mk_bottom
    -> False.
Proof.
  introv Hcv.
  unfold converges_to_is_value_like, reduces_to, reduces_in_atmost_k_steps in Hcv; exrepnd.
  unfold_all_mk.
  induction k as [k  Hind] using comp_ind.
  destruct k.

  - rw @compute_at_most_k_steps_0 in Hcv2; ginv; fold_terms.
    apply is_value_like_bot in Hcv0; sp.

  - rw @compute_at_most_k_steps_eq_f in Hcv2.
    rw @compute_at_most_k_stepsf_S in Hcv2; allsimpl.
    destruct k.

    + rw @compute_at_most_k_stepsf_0 in Hcv2; ginv; fold_terms.
      apply is_value_like_apply in Hcv0; sp.

    + rw @compute_at_most_k_stepsf_S in Hcv2; allsimpl.
      unfold apply_bterm in Hcv2.
      simpl in Hcv2.
      revert Hcv2.
      change_to_lsubst_aux4; simpl; try (complete sp).
      intro c.
      rw <- @compute_at_most_k_steps_eq_f in c.
      apply Hind in c; sp.
Qed.

Lemma reduces_to_if_isvalue_like {p} :
  forall lib (a t : @NTerm p), isvalue_like a -> reduces_to lib a t -> t = a.
Proof.
  introv isv r.
  destruct a; auto.
  - provefalse; unfold isvalue_like in isv; sp.
  - unfold reduces_to in r; exrepnd.
    induction k.
    * rw @reduces_in_atmost_k_steps_0 in r0; auto.
    * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
      csunf r0; allsimpl; ginv; sp.
  - dopid o as [can|ncan|exc|abs] Case.
    + Case "Can".
      unfold reduces_to in r; exrepnd.
      induction k.
      * rw @reduces_in_atmost_k_steps_0 in r0; auto.
      * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
        csunf r0; allsimpl; ginv; sp.
    + Case "NCan".
      provefalse; unfold isvalue_like in isv; sp.
    + Case "Exc".
      unfold reduces_to in r; exrepnd.
      induction k.
      * rw @reduces_in_atmost_k_steps_0 in r0; auto.
      * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
        csunf r0; allsimpl; ginv; sp.
    + Case "Abs".
      provefalse; unfold isvalue_like in isv; sp.
Qed.

(* !!MOVE to library *)
Lemma find_entry_eq_unfold_abs {o} :
  forall lib abs (bs : list (@BTerm o)),
    match find_entry lib abs bs with
    | Some (lib_cs _ _) => unfold_abs lib abs bs = None
    | Some (lib_abs oa vars rhs correct) =>
      unfold_abs lib abs bs = Some (mk_instance vars bs rhs)
    | None => unfold_abs lib abs bs = None
    end.
Proof.
  induction lib; introv; allsimpl; auto.
  destruct a; boolvar; allsimpl; boolvar; allsimpl; tcsp;
    allrw @not_matching_entry_iff; tcsp;
      try (complete (apply IHlib)).
Qed.

Lemma reduces_to_abs_if_doesnt_find_entry {o} :
  forall lib abs (l : list (@BTerm o)) t,
    find_entry lib abs l = None
    -> reduces_to lib (oterm (Abs abs) l) t
    -> t = oterm (Abs abs) l.
Proof.
  introv fe r.
  unfold reduces_to in r; exrepnd.
  destruct k.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r0; allsimpl.
    pose proof (find_entry_eq_unfold_abs lib abs l) as h.
    rw fe in h.
    unfold compute_step_lib in r0; rw h in r0; ginv.
Qed.

Lemma reduces_to_if_is_value_like {p} :
  forall lib (a t : @NTerm p), is_value_like lib a -> reduces_to lib a t -> t = a.
Proof.
  introv isv r.
  destruct a.
  - provefalse; unfold is_value_like, isvalue_like in isv; sp.
  - unfold reduces_to in r; exrepnd.
    induction k.
    * rw @reduces_in_atmost_k_steps_0 in r0; auto.
    * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
      csunf r0; allsimpl; ginv; sp.
  - dopid o as [can|ncan|exc|abs] Case.
    + Case "Can".
      unfold reduces_to in r; exrepnd.
      induction k.
      * rw @reduces_in_atmost_k_steps_0 in r0; auto.
      * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
        csunf r0; allsimpl; ginv; sp.
    + Case "NCan".
      provefalse; unfold is_value_like, isvalue_like in isv; sp.
    + Case "Exc".
      unfold reduces_to in r; exrepnd.
      induction k.
      * rw @reduces_in_atmost_k_steps_0 in r0; auto.
      * rw @reduces_in_atmost_k_steps_S in r0; exrepnd.
        csunf r0; allsimpl; ginv; sp.
    + Case "Abs".
      unfold is_value_like, isvalue_like in isv; repndors; allsimpl; tcsp.
      apply reduces_to_abs_if_doesnt_find_entry in r; auto.
Qed.

Lemma converge_to_value_like_reduces_to {p} :
  forall (lib : @library p) a b,
    converges_to_value_like lib a
    -> reduces_to lib a b
    -> converges_to_value_like lib b.
Proof.
  introv c r.
  allunfold @converges_to_value_like; exrepnd.
  exists u; dands; auto.
  apply @reduces_to_or with (u := u) in r; auto.
  dorn r; auto.
  pose proof (reduces_to_if_isvalue_like lib u b) as e.
  repeat (autodimp e hyp); subst; auto.
Qed.

Lemma converge_to_is_value_like_reduces_to {p} :
  forall (lib : @library p) a b,
    converges_to_is_value_like lib a
    -> reduces_to lib a b
    -> converges_to_is_value_like lib b.
Proof.
  introv c r.
  allunfold @converges_to_is_value_like; exrepnd.
  exists u; dands; auto.
  apply @reduces_to_or with (u := u) in r; auto.
  dorn r; auto.
  pose proof (reduces_to_if_is_value_like lib u b) as e.
  repeat (autodimp e hyp); subst; auto.
Qed.

Lemma reduces_to_if_step_lib {p} :
  forall lib abs bs (u : @NTerm p),
    compute_step_lib lib abs bs = csuccess u
    -> reduces_to lib (oterm (Abs abs) bs) u.
Proof.
 unfold reduces_to; sp; exists 1; simpl; sp.
Qed.

Lemma converges_to_value_like_ncan {o} :
  forall (lib : @library o) ncan t bs,
    converges_to_value_like lib (oterm (NCan ncan) (nobnd t :: bs))
    -> {u : NTerm & reduces_to lib t u # (isexc u [+] iscan u)}.
Proof.
  introv conv.
  unfold converges_to_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold isvalue_like in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [|f|op bs1]; ginv.

    + exists (sterm f); simpl; dands; eauto 3 with slow.

    + dopid op as [can2|ncan2|exc2|abs2] Case; ginv.

      * Case "Can".
        allsimpl.
        eexists;dands;[apply reduces_to_symm|]; simpl; auto.

      * Case "NCan".
        remember (compute_step lib (oterm (NCan ncan2) bs1)) as cs;
          destruct cs; ginv; fold_terms.
        apply IHk in comp0; auto; exrepnd.
        exists u0; dands; auto.
        symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
        eapply reduces_to_trans; eauto.

      * Case "Exc".
        exists (oterm Exc bs1); dands; eauto 3 with slow.

      * Case "Abs".
        csunf comp1; allsimpl.
        remember (compute_step_lib lib abs2 bs1) as csl;
          symmetry in Heqcsl; destruct csl; ginv.
        apply IHk in comp0; auto; exrepnd.
        exists u0; dands; auto.
        apply reduces_to_if_step_lib in Heqcsl.
        eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_is_value_like_ncan {o} :
  forall (lib : @library o) ncan t bs,
    converges_to_is_value_like lib (oterm (NCan ncan) (nobnd t :: bs))
    -> {u : NTerm & reduces_to lib t u # (isexc u [+] iscan u)}.
Proof.
  introv conv.
  unfold converges_to_is_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold is_value_like, isvalue_like in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t as [|f|op bs1]; ginv.

    { exists (sterm f); simpl; dands; eauto 3 with slow. }

    dopid op as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      exists (oterm (Can can2) bs1); dands; eauto 3 with slow.

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as cs;
        destruct cs; ginv; fold_terms.
      apply IHk in comp0; auto; exrepnd.
      exists u0; dands; auto.
      symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
      eapply reduces_to_trans; eauto.

    + Case "Exc".
      allsimpl; ginv.
      exists (oterm Exc bs1); dands; eauto 3 with slow.

    + Case "Abs".
      unfold nobnd in comp1; rw @compute_step_ncan_abs in comp1.
      remember (compute_step_lib lib abs2 bs1) as csl;
        symmetry in Heqcsl; destruct csl; ginv.
      apply IHk in comp0; auto; exrepnd.
      exists u0; dands; auto.
      apply reduces_to_if_step_lib in Heqcsl.
      eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_value_like_ncompop {o} :
  forall (lib : @library o) ncop can l t bs,
    converges_to_value_like
      lib
      (oterm (NCan (NCompOp ncop))
             (nobnd (oterm (Can can) l)
                    :: nobnd t
                    :: bs))
    -> (
        {pk : param_kind & computes_to_pk lib t pk}
        [+]
        {e : NTerm & reduces_to lib t e # isexc e}
       ).
Proof.
  introv conv.
  unfold converges_to_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold isvalue_like in isv; sp.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t; ginv; try (complete (csunf comp1; allsimpl; dcwf h)).
    dopid o0 as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      csunf comp1; unfold compute_step_comp in comp1; allsimpl.
      dcwf h; allsimpl.
      apply compute_step_compop_success_can_can in comp1; exrepnd; subst.
      repndors; exrepnd; subst;
      allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.
      * left; exists (@PKi o n2).
        unfold computes_to_pk, computes_to_value; dands; tcsp; eauto 2 with slow.
      * left; exists pk2; allrw <- @pk2term_eq; eauto 3 with slow.

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_ncan2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step lib (oterm (NCan ncan2) l0)) as cs;
        destruct cs; ginv.
      fold_terms.
      apply IHk in comp0; auto.
      repndors; exrepnd.
      * left; exists pk.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
        eapply reduces_to_trans; eauto.

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      right.
      exists (oterm Exc l0); dands; tcsp; eauto with slow.

    + Case "Abs".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_abs2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step_lib lib abs2 l0) as csl;
        symmetry in Heqcsl; destruct csl; ginv.
      apply IHk in comp0; auto.
      repndors; exrepnd.
      * left; exists pk.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        apply reduces_to_if_step_lib in Heqcsl.
        eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_value_like_narithop {o} :
  forall (lib : @library o) a can l t bs,
    converges_to_value_like
      lib
      (oterm (NCan (NArithOp a))
             (nobnd (oterm (Can can) l)
                    :: nobnd t
                    :: bs))
    -> (
        {i : Z & computes_to_value lib t (mk_integer i)}
        [+]
        {e : NTerm & reduces_to lib t e # isexc e}
       ).
Proof.
  introv conv.
  unfold converges_to_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold isvalue_like in isv; sp.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t; ginv; try (complete (csunf comp1; allsimpl; dcwf h)).
    dopid o0 as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      csunf comp1; allsimpl; dcwf h; allsimpl.
      unfold compute_step_arith in comp1; allsimpl.
      destruct l; allsimpl; ginv.
      destruct l0; allsimpl; ginv.
      destruct bs; allsimpl; ginv.
      destruct can; allsimpl; ginv.
      destruct can2; allsimpl; ginv.
      left; exists z0.
      unfold computes_to_value; dands; tcsp.
      { exists 0; rw @reduces_in_atmost_k_steps_0; auto. }
      { repeat constructor; simpl; sp. }

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_narithop_ncan2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step lib (oterm (NCan ncan2) l0)) as cs;
        destruct cs; ginv.
      fold_terms.
      apply IHk in comp0; auto.
      dorn comp0; exrepnd.
      * left; exists i.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
        eapply reduces_to_trans; eauto.

    + Case "Exc".
      allsimpl; ginv.
      right.
      exists (oterm Exc l0); dands; tcsp; eauto with slow.

    + Case "Abs".
      unfold nobnd in comp1; rw @compute_step_narithop_abs2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step_lib lib abs2 l0) as csl;
        symmetry in Heqcsl; destruct csl; ginv.
      apply IHk in comp0; auto.
      dorn comp0; exrepnd.
      * left; exists i.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        apply reduces_to_if_step_lib in Heqcsl.
        eapply reduces_to_trans; eauto.
Qed.

Hint Resolve computes_to_value_step : slow.

Lemma computes_to_pk_step {p} :
  forall lib (t1 t2 : @NTerm p) pk,
  computes_to_pk lib t2 pk
  -> compute_step lib t1 = csuccess t2
  -> computes_to_pk lib t1 pk.
Proof.
  introv comp1 comp2; eauto 3 with slow.
Qed.
Hint Resolve computes_to_pk_step : slow.

Lemma converges_to_is_value_like_ncompop {o} :
  forall (lib : @library o) ncop can l t bs,
    converges_to_is_value_like
      lib
      (oterm (NCan (NCompOp ncop))
             (nobnd (oterm (Can can) l)
                    :: nobnd t
                    :: bs))
    -> (
        {pk : param_kind & computes_to_pk lib t pk}
        [+]
        {e : NTerm & reduces_to lib t e # isexc e}
       ).
Proof.
  introv conv.
  unfold converges_to_is_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold is_value_like, isvalue_like in isv; sp.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t; ginv; try (complete (csunf comp1; allsimpl; dcwf h)).
    dopid o0 as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      csunf comp1; unfold compute_step_comp in comp1; allsimpl.
      dcwf h; allsimpl.
      apply compute_step_compop_success_can_can in comp1; exrepnd; subst.
      repndors; exrepnd; subst;
      allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.
      * left; exists (@PKi o n2).
        unfold computes_to_value; dands; tcsp; eauto 3 with slow.
      * left; exists pk2.
        allrw <- @pk2term_eq.
        unfold computes_to_value; dands; tcsp; eauto 3 with slow.

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_ncan2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step lib (oterm (NCan ncan2) l0)) as cs;
        destruct cs; ginv.
      fold_terms.
      apply IHk in comp0; auto.
      repndors; exrepnd.
      * left; exists pk; eauto 3 with slow.
      * right; exists e; dands; auto.
        symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
        eapply reduces_to_trans; eauto.

    + Case "Exc".
      csunf comp1; allsimpl; ginv.
      right.
      exists (oterm Exc l0); dands; tcsp; eauto with slow.

    + Case "Abs".
      unfold nobnd in comp1.
      rw @compute_step_ncompop_abs2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step_lib lib abs2 l0) as csl;
        symmetry in Heqcsl; destruct csl; ginv.
      apply IHk in comp0; auto.
      repndors; exrepnd.
      * left; exists pk; eauto 3 with slow.
      * right; exists e; dands; auto.
        apply reduces_to_if_step_lib in Heqcsl.
        eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_is_value_like_narithop {o} :
  forall (lib : @library o) a can l t bs,
    converges_to_is_value_like
      lib
      (oterm (NCan (NArithOp a))
             (nobnd (oterm (Can can) l)
                    :: nobnd t
                    :: bs))
    -> (
        {i : Z & computes_to_value lib t (mk_integer i)}
        [+]
        {e : NTerm & reduces_to lib t e # isexc e}
       ).
Proof.
  introv conv.
  unfold converges_to_is_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp isv.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold is_value_like, isvalue_like in isv; sp.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t; ginv; try (complete (csunf comp1; allsimpl; dcwf h)).
    dopid o0 as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      csunf comp1; allsimpl; dcwf h; allsimpl.
      unfold compute_step_arith in comp1; allsimpl.
      destruct l; allsimpl; ginv.
      destruct l0; allsimpl; ginv.
      destruct bs; allsimpl; ginv.
      destruct can; allsimpl; ginv.
      destruct can2; allsimpl; ginv.
      left; exists z0.
      unfold computes_to_value; dands; tcsp.
      { exists 0; rw @reduces_in_atmost_k_steps_0; auto. }
      { repeat constructor; simpl; sp. }

    + Case "NCan".
      unfold nobnd in comp1.
      rw @compute_step_narithop_ncan2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step lib (oterm (NCan ncan2) l0)) as cs;
        destruct cs; ginv.
      fold_terms.
      apply IHk in comp0; auto.
      dorn comp0; exrepnd.
      * left; exists i.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        symmetry in Heqcs; apply reduces_to_if_step in Heqcs.
        eapply reduces_to_trans; eauto.

    + Case "Exc".
      allsimpl; ginv.
      right.
      exists (oterm Exc l0); dands; tcsp; eauto with slow.

    + Case "Abs".
      unfold nobnd in comp1; rw @compute_step_narithop_abs2 in comp1.
      dcwf h; allsimpl.
      remember (compute_step_lib lib abs2 l0) as csl;
        symmetry in Heqcsl; destruct csl; ginv.
      apply IHk in comp0; auto.
      dorn comp0; exrepnd.
      * left; exists i.
        eapply computes_to_value_step; eauto.
      * right; exists e; dands; auto.
        apply reduces_to_if_step_lib in Heqcsl.
        eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_value_like_step {o} :
  forall lib (t u : @NTerm o),
    compute_step lib t = csuccess u
    -> converges_to_value_like lib u
    -> converges_to_value_like lib t.
Proof.
  introv cs cv.
  allunfold @converges_to_value_like; exrepnd.
  exists u0; sp.
  apply reduces_to_if_step in cs.
  eapply reduces_to_trans; eauto.
Qed.

Lemma converges_to_is_value_like_step {o} :
  forall lib (t u : @NTerm o),
    compute_step lib t = csuccess u
    -> converges_to_is_value_like lib u
    -> converges_to_is_value_like lib t.
Proof.
  introv cs cv.
  allunfold @converges_to_is_value_like; exrepnd.
  exists u0; sp.
  apply reduces_to_if_step in cs.
  eapply reduces_to_trans; eauto.
Qed.

Lemma computes_steps_prinargs_arith_can {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt k1 k2 ntpc1 ntpc2,
    compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
    -> isinteger ntpc1
    -> compute_at_most_k_steps lib k2 ntp2 = csuccess ntpc2
    -> {j : nat
        $ compute_at_most_k_steps
             lib j (oterm (NCan (NArithOp a))
                          ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
            = csuccess (oterm (NCan (NArithOp a))
                              ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt)))
        # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind]; introv H1c H1v H2c.

  - inverts H2c.
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end.
    exrepnd. exists j. dands; spc. omega.

  - duplicate H1v.
    rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [| | ntp2o  ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail| |].

    { rw @compute_at_most_k_steps_isvalue_like in Hck; eauto 3 with slow; ginv; GC.
      eapply Hind in H1c; auto;
      [|rw @compute_at_most_k_steps_isvalue_like;try reflexivity;eauto 3 with slow].
      exrepnd.
      exists j; dands; auto; try omega. }

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v0 eq_refl) as XX. clear H1v0. exrepnd.
    destruct csk as [sckv| | csko csklbt]; [inverts Hck; fail| |];[|].

    { csunf Hck; allsimpl; ginv.
      eapply Hind in H1c; eauto.
      exrepnd.
      exists j; dands; auto; try omega. }

    dopid csko as [cskoc| cskon | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j).
      unfold isinteger in H1v; exrepnd; subst.
      dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
      csunf; simpl.
      dcwf h; allsimpl; tcsp; try (rw Hck); clear Hck; simpl; auto.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      unfold isinteger in H1v; exrepnd; subst.
      exists (S j). dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
      csunf; simpl; dcwf h.
      rw Hck; clear Hck; simpl; auto.
Qed.

Lemma reduce_to_prinargs_arith_can {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt ntpv1 ntpc2,
    reduces_to lib ntp1 ntpv1
    -> isinteger ntpv1
    -> reduces_to lib ntp2 ntpc2
    -> reduces_to
         lib
         (oterm (NCan (NArithOp a))
                ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
         (oterm (NCan (NArithOp a))
                ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv red1 can1 red2.
  allunfold @reduces_to; exrepnd.
  allunfold @reduces_in_atmost_k_steps.
  eapply (computes_steps_prinargs_arith_can _ a ntp1 ntp2 lbt) in red2; eauto.
  exrepnd.
  exists j; sp.
Qed.

Lemma computes_steps_prinargs_comp_can {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt k1 k2 ntpc1 ntpc2,
    compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
    -> iswfpk a ntpc1
    -> compute_at_most_k_steps lib k2 ntp2 = csuccess ntpc2
    -> {j : nat
        $ compute_at_most_k_steps
             lib j (oterm (NCan (NCompOp a))
                          ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
            = csuccess (oterm (NCan (NCompOp a))
                              ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt)))
        # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind]; introv H1c H1v H2c.

  - inverts H2c.
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end.
    exrepnd. exists j. dands; spc. omega.

  - duplicate H1v.
    rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [| | ntp2o  ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail| |].

    { rw @compute_at_most_k_steps_isvalue_like in Hck; eauto 3 with slow; ginv.
      eapply Hind in H1c; auto;
      [|rw @compute_at_most_k_steps_isvalue_like;try reflexivity;eauto 3 with slow].
      exrepnd.
      exists j; dands; auto; try omega. }

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v0 eq_refl) as XX. clear H1v0. exrepnd.
    destruct csk as [sckv| | csko csklbt]; [inverts Hck; fail| |].

    { csunf Hck; allsimpl; ginv.
      eapply Hind in H1c; eauto.
      exrepnd.
      exists j; dands; auto; try omega. }

    dopid csko as [cskoc| cskon | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j).
      unfold iswfpk in H1v; destruct a; allsimpl.
      * unfold isinteger in H1v; exrepnd; subst.
        dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
        csunf; simpl; dcwf h.
        rw Hck; clear Hck; auto.
      * unfold ispk in H1v; exrepnd; subst.
        dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
        csunf; simpl; allrw @pk2term_eq; dcwf h; allrw @co_wf_pk2can; ginv.
        rw Hck; clear Hck; auto.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      exists (S j).
      unfold iswfpk in H1v; destruct a; allsimpl.
      * unfold isinteger in H1v; exrepnd; subst.
        dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
        csunf; simpl; dcwf h.
        rw Hck; clear Hck; auto.
      * unfold ispk in H1v; exrepnd; subst.
        dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
        csunf; simpl; allrw @pk2term_eq; dcwf h; allrw @co_wf_pk2can; ginv.
        rw Hck; clear Hck; auto.
Qed.

Lemma reduce_to_prinargs_comp_can {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt ntpv1 ntpc2,
    reduces_to lib ntp1 ntpv1
    -> iswfpk a ntpv1
    -> reduces_to lib ntp2 ntpc2
    -> reduces_to
         lib
         (oterm (NCan (NCompOp a))
                ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
         (oterm (NCan (NCompOp a))
                ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv red1 can1 red2.
  allunfold @reduces_to; exrepnd.
  allunfold @reduces_in_atmost_k_steps.
  eapply (computes_steps_prinargs_comp_can _ a ntp1 ntp2 lbt) in red2; eauto.
  exrepnd.
  exists j; sp.
Qed.

Lemma memvar_nil :
  forall v, memvar v [] = false.
Proof. sp. Qed.

Lemma in_lsubst_aux_sub {o} :
  forall v t (sub1 sub2 : @Sub o),
    LIn (v,t) (lsubst_aux_sub sub1 sub2)
    <=> {u : NTerm & t = lsubst_aux u sub2 # LIn (v,u) sub1}.
Proof.
  induction sub1; introv; simpl; split; introv k; exrepnd; tcsp; allsimpl.
  - dorn k; cpx.
    + exists a; auto; sp.
    + apply IHsub1 in k; exrepnd; subst.
      exists u; sp.
  - dorn k0; cpx; subst.
    rw IHsub1; right; exists u; sp.
Qed.

Definition cl_sk {o} (sk : @sosub_kind o) :=
  match sk with
    | sosk vs t => subvars (free_vars t) vs
  end.

Definition cl_sosub {o} (sub : @SOSub o) :=
  forall (v : NVar) (sk : sosub_kind),
    LIn (v,sk) sub -> cl_sk sk.

Lemma free_vars_sosub_sub2sosub {o} :
  forall (sub : @Sub o),
    free_vars_sosub (sub2sosub sub) = sub_free_vars sub.
Proof.
  induction sub; simpl; auto.
  destruct a; simpl.
  rw remove_nvars_nil_l.
  rw IHsub; auto.
Qed.

Lemma lsubst_aux_sub_disj_dom {o} :
  forall (sub1 sub2 : @Sub o),
    cl_sub sub2
    -> disjoint (sub_free_vars sub1) (dom_sub sub2)
    -> lsubst_aux_sub sub1 sub2 = sub1.
Proof.
  induction sub1; introv cl disj; allsimpl; auto.
  destruct a.
  allrw disjoint_app_l; repnd.
  rw IHsub1; auto.
  f_equal; f_equal.
  apply lsubst_aux_trivial_cl; eauto with slow.
Qed.

Lemma sub_free_vars_sub_change_bvars_alpha {o} :
  forall (sub : @Sub o) vars,
    sub_free_vars (sub_change_bvars_alpha vars sub)
    = sub_free_vars sub.
Proof.
  induction sub; introv; allsimpl; auto.
  destruct a; rw IHsub.
  rw @free_vars_change_bvars_alpha; auto.
Qed.

Lemma sub_filter_sub_change_bvars_alpha {o} :
  forall (sub : @Sub o) vs l,
    sub_filter (sub_change_bvars_alpha vs sub) l
    = sub_change_bvars_alpha vs (sub_filter sub l).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; simpl; boolvar; simpl; auto.
  rw IHsub; auto.
Qed.

Lemma subsovars_flat_map_l :
  forall {A} (l : list A) (f : A -> list sovar_sig) vs,
    subsovars (flat_map f l) vs
    <=> (forall a, LIn a l -> subsovars (f a) vs).
Proof.
  introv.
  rw subsovars_prop; split; intro k; introv i.
  - rw subsovars_prop; introv j.
    apply k; rw lin_flat_map.
    eexists; eauto.
  - rw lin_flat_map in i; exrepnd.
    apply k in i1.
    rw subsovars_prop in i1; apply i1 in i0; auto.
Qed.

(*
Lemma compute_step_lib_if_is_mrk {o} :
  forall (lib : @library o) m,
    is_mrk lib m
    -> compute_step_lib lib (abs_marker m) []
       = cfailure compute_step_error_abs (mk_marker m).
Proof.
  introv ism.
  apply ismrk_implies in ism; exrepnd.
  unfold mk_marker in ism0; ginv.
  unfold compute_step_lib; simpl.
  pose proof (find_entry_eq_unfold_abs lib (abs_marker m) []) as h; rw ism1 in h; rw h; auto.
Qed.

Lemma compute_step_if_is_mrk {o} :
  forall (lib : @library o) m,
    is_mrk lib m
    -> compute_step lib (mk_marker m)
       = cfailure compute_step_error_abs (mk_marker m).
Proof.
  introv ism.
  csunf; simpl.
  apply compute_step_lib_if_is_mrk; auto.
Qed.

Lemma closed_marker {o} :
  forall m, @closed o (mk_marker m).
Proof. sp. Qed.
Hint Resolve closed_marker : slow.
 *)

Lemma cl_lsubst_aux_pushdown_fresh {o} :
  forall (t : @NTerm o) (v : NVar) (sub : Substitution),
    cl_sub sub
    -> isvalue_like t
    -> alpha_eq (lsubst_aux (pushdown_fresh v t) sub)
                (pushdown_fresh v (lsubst_aux t (sub_filter sub [v]))).
Proof.
  introv cl isv.
  rw <- @cl_lsubst_lsubst_aux; eauto with slow.
  rw <- @cl_lsubst_lsubst_aux; eauto with slow.
  apply cl_lsubst_pushdown_fresh; auto.
Qed.

Lemma simple_lsubst_lsubst_sub_aeq4 {o} :
  forall (t : @NTerm o) (sub1 sub2 : Substitution),
    cl_sub sub1
    -> cl_sub sub2
    -> lsubst (lsubst t sub1) sub2
       = lsubst (lsubst t (sub_filter sub2 (dom_sub sub1))) sub1.
Proof.
  introv cl1 cl2.
  repeat unflsubst.
  revert sub1 sub2 cl1 cl2.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl1 cl2; allsimpl; auto.

  - Case "vterm".
    rw @sub_find_sub_filter_eq; boolvar; allsimpl; auto.

    + remember (sub_find sub1 v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.

      * rw @lsubst_aux_trivial_cl2; auto.
        apply sub_find_some in Heqsf.
        apply in_cl_sub in Heqsf; auto.

      * apply sub_find_none_iff in Heqsf; sp.

    + rw @sub_find_none_if; auto; simpl.
      remember (sub_find sub2 v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.

      * rw @lsubst_aux_trivial_cl2; auto.
        apply sub_find_some in Heqsf.
        apply in_cl_sub in Heqsf; auto.

      * rw @sub_find_none_if; auto.

  - Case "oterm".
    allrw map_map; unfold compose; f_equal.
    apply eq_maps; introv i; destruct x as [l t]; simpl.
    f_equal.
    rw (ind t l); eauto with slow.
    f_equal.
    rw <- @dom_sub_sub_filter.
    allrw <- @sub_filter_app_r.
    rw <- @sub_filter_app_as_remove_nvars.
    allrw @sub_filter_app_r.
    rw @sub_filter_swap; auto.
Qed.

Lemma converges_to_value_like_alpha_eq {o} :
  forall lib (t1 t2 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> converges_to_value_like lib t1
    -> converges_to_value_like lib t2.
Proof.
  introv wf aeq conv.
  allunfold @converges_to_value_like; exrepnd.
  eapply reduces_to_alpha in conv1;[|auto|eauto].
  exrepnd.
  eexists; dands; eauto.
  eapply alpha_eq_preserves_isvalue_like; eauto.
Qed.
Hint Resolve converges_to_value_like_alpha_eq : slow.

Hint Resolve nt_wf_subst : slow.

Lemma no_repeats_get_utokens_sub_singleton_tok {o} :
  forall v (a : get_patom_set o),
    no_repeats (get_utokens_sub [(v, mk_utoken a)]).
Proof.
  introv.
  unfold get_utokens_sub; simpl; eauto 3 with slow.
Qed.

(*
Lemma converges_to_is_value_like_fresh_implies {o} :
  forall lib (t : @NTerm o) v,
    wf_term t
    -> converges_to_is_value_like lib (mk_fresh v t)
    -> forall a,
         !LIn a (get_utokens t)
         -> converges_to_value_like lib (subst t v (mk_utoken a)).
Proof.
  introv wf conv.
  unfold converges_to_is_value_like, reduces_to in conv; exrepnd.
  revert t v u wf conv2 conv0.
  induction k; introv wf comp isvl nia; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold is_value_like, isvalue_like in isvl; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_ncan_bterm_cons_success in comp1; repnd; GC.
    repndors; exrepnd; subst; allsimpl; repnd; subst.

    + apply (not_fresh_id_reduces_to_is_value_like _ _ v) in isvl.
      destruct isvl; exists k; auto.

    + unfold converges_to_value_like.
      exists (subst t v (mk_utoken a)); dands; eauto with slow.

    + assert (wf_term x) as wfx.
      { apply compute_step_preserves_wf in comp3; auto.
        apply wf_term_subst; eauto with slow. }

      pose proof (IHk (subst_utokens x [(get_fresh_atom t, mk_var v)]) v u) as h; clear IHk.
      repeat (autodimp h hyp).
      { apply wf_subst_utokens; eauto 3 with slow. }

      pose proof (h (get_fresh_atom t)) as conv; clear h.
      autodimp conv hyp.
      { pose proof (get_fresh_atom_prop t) as gfa.
        allrw in_app_iff; allrw not_over_or; repnd.
        introv ni.
        apply get_utokens_subst_utokens_subset in ni; allsimpl.
        unfold get_utokens_utok_ren in ni; allsimpl; allrw app_nil_r.
        apply in_remove in ni; repnd.
        pose proof (compute_step_preserves lib (subst t v (mk_utoken (get_fresh_atom t))) x) as q.
        repeat (autodimp q hyp); repnd; eauto 3 with slow.
      }

      assert (!LIn v (free_vars x)) as nivx.
      { pose proof (compute_step_preserves lib (subst t v (mk_utoken (get_fresh_atom t))) x) as q.
        repeat (autodimp q hyp); repnd; eauto 3 with slow.
        introv i.
        rw subvars_eq in q0; apply q0 in i.
        unfsubst in i.
        rw @free_vars_lsubst_aux_cl in i; allsimpl; eauto 3 with slow.
        rw in_remove_nvars in i; allsimpl; sp.
      }

      pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom t) v) as aeq.
      repeat (autodimp aeq hyp).
      eapply converges_to_value_like_alpha_eq in aeq;
        eauto 4 with slow.
      apply converges_to_value_like_step in comp3; auto.

      unfold converges_to_value_like in comp3; exrepnd.
      unfold converges_to_value_like.
      unfold reduces_to in comp3; exrepnd.

      remember (get_fresh_atom t) as a'.

      assert (!LIn a' (get_utokens t)) as nia't.
      { subst; pose proof (get_fresh_atom_prop t) as h; tcsp.
        introv i.
        apply subset_get_utokens_get_utokens_step_seq in i; sp. }

      assert (!LIn a (get_utokens t)) as niat by tcsp.
      apply wf_term_eq in wf.

      assert (nr_ut_sub t [(v, mk_utoken a)]) as nrut by eauto 3 with slow.
      assert (nr_ut_sub t [(v, mk_utoken a')]) as nrut' by eauto 3 with slow.

      pose proof (reduces_in_atmost_k_steps_change_utok_sub_norep
                    lib k0 t u0 wf
                    [(v,mk_utoken a')]
                    [(v,mk_utoken a)]
                    eq_refl
                    (no_repeats_get_utokens_sub_singleton_tok v a')
                    (no_repeats_get_utokens_sub_singleton_tok v a)
                    nrut'
                    nrut)
        as ch; allsimpl.

      repeat (autodimp ch hyp); eauto 3 with slow.
      { unfold get_utokens_sub; simpl.
        apply disjoint_singleton_l.
        subst.
        apply get_fresh_atom_prop. }
      { unfold get_utokens_sub; simpl.
        apply disjoint_singleton_l; auto. }
      exrepnd.

      allrw @fold_subst.
      exists s; dands.
      { exists k0; auto. }
      eapply alpha_eq_preserves_isvalue_like;[apply alpha_eq_sym; exact ch1|].
      apply alpha_eq_preserves_isvalue_like in ch0; auto.
      unfold subst; rw @cl_lsubst_lsubst_aux; eauto 2 with slow.
      unfold subst in ch0; rw @cl_lsubst_lsubst_aux in ch0; eauto 2 with slow.
      apply isvalue_like_lsubst_aux_implies in ch0; repndors; eauto 3 with slow.
      exrepnd; subst.
      allsimpl; boolvar; eauto 3 with slow; ginv.
Qed.
*)

Lemma lsubst_aux_preserves_wf_term2 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> wf_sub sub
    -> wf_term (lsubst_aux t sub).
Proof.
  introv wt ws.
  apply lsubst_aux_preserves_wf_term; auto.
  introv i.
  unfold wf_sub, sub_range_sat in ws.
  apply ws in i.
  apply wf_term_eq; auto.
Qed.

(* !! MOVE *)
Hint Resolve wf_sub_filter : slow.

Lemma converges_to_is_value_like_if {o} :
  forall lib (t : @NTerm o),
    converges_to_value_like lib t
    -> converges_to_is_value_like lib t.
Proof.
  introv conv.
  unfold converges_to_value_like in conv.
  unfold converges_to_is_value_like.
  exrepnd.
  eexists; dands; eauto.
  apply isvalue_like_implies_is_value_like; auto.
Qed.

Lemma reduces_to_free_vars {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> reduces_to lib t u
    -> subset (free_vars u) (free_vars t).
Proof.
  introv wf r.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf r.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_preserves in r1; repnd; auto.
    apply IHk in r0; auto.
    rw subvars_eq in r2.
    eapply subset_trans; eauto.
Qed.

Lemma get_utokens_sub_alphaeq_sub {o} :
  forall (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> get_utokens_sub sub1 = get_utokens_sub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; auto; inversion aeq; subst.
  unfold get_utokens_sub; simpl; apply app_if; auto.
  - allrw @alphaeq_eq.
    apply alphaeq_preserves_utokens; auto.
  - apply IHsub1; auto.
Qed.

Lemma lsubst_aux_subst_utokens_disj_cl2 {o} :
  forall (t : @NTerm o) sub usub,
    disjoint (get_utokens_sub sub) (utok_sub_dom usub)
    -> disjoint (free_vars_utok_sub usub) (dom_sub sub)
    -> cl_sub sub
    -> alpha_eq (lsubst_aux (subst_utokens t usub) sub)
                (subst_utokens (lsubst_aux t sub) usub).
Proof.
  introv d1 d2 cl.

  pose proof (sub_change_bvars_alpha_spec (free_vars_utok_sub usub) sub) as a.
  simpl in a; repnd.
  remember (sub_change_bvars_alpha (free_vars_utok_sub usub) sub) as sub'; clear Heqsub'.

  pose proof (lsubst_aux_alpha_congr_cl_sub
                (subst_utokens t usub)
                (subst_utokens t usub)
                sub sub') as aeq.
  repeat (autodimp aeq hyp).
  eapply alpha_eq_trans;[exact aeq|].

  pose proof (unfold_subst_utokens usub t) as h; exrepnd.
  rw h0.
  rw @lsubst_aux_subst_utokens_aux_disj; auto;
  [|apply get_utokens_sub_alphaeq_sub in a; rw <- a; auto
   |apply alphaeq_sub_implies_eq_doms in a; rw <- a; auto].

  pose proof (unfold_subst_utokens usub (lsubst_aux t sub)) as k; exrepnd.
  rw k0.

  apply alpha_eq_subst_utokens_aux; eauto 3 with slow.

  - apply disjoint_sym.
    apply substitution.disjoint_bound_vars_lsubst_aux;
    allrw <- @sub_free_vars_is_flat_map_free_vars_range;
    allrw <- @sub_bound_vars_is_flat_map_bound_vars_range;
    eauto 3 with slow.

    + rw @sub_free_vars_if_cl_sub; eauto with slow.

    + rw disjoint_app_l; dands; eauto with slow.

  - eapply alpha_eq_trans;[|exact k1].
    apply lsubst_aux_alpha_congr2; eauto 3 with slow.

    + rw @sub_free_vars_if_cl_sub; eauto with slow.

    + rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma sub_filter_bot_sub {o} :
  forall vs l,
    sub_filter (@bot_sub o vs) l = bot_sub (remove_nvars l vs).
Proof.
  induction vs; simpl; introv.
  - rw remove_nvars_nil_r; simpl; auto.
  - rw remove_nvars_cons_r; boolvar; simpl; tcsp.
    f_equal; sp.
Qed.

Lemma get_utokens_sub_bot_sub {o} :
  forall vs, @get_utokens_sub o (bot_sub vs) = [].
Proof.
  induction vs; simpl; unfold get_utokens_sub; simpl; auto.
Qed.

Lemma isnoncan_like_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    isnoncan_like (lsubst_aux t sub)
    -> {v : NVar
        & {u : NTerm
        & t = mk_var v
        # sub_find sub v = Some u
        # isnoncan_like u}}
       [+] isnoncan_like t.
Proof.
  introv isn.
  destruct t as [v|f|op bs]; allsimpl; auto.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf.
  - left.
    exists v n; dands; auto.
  - unfold isnoncan_like in isn; allsimpl; sp.
Qed.

Lemma sub_find_bot_sub_eq {o} :
  forall v vs,
    @sub_find o (bot_sub vs) v
    = if memvar v vs
      then Some mk_bot
      else None.
Proof.
  induction vs; simpl; auto.
  rw memvar_cons; boolvar; tcsp.
Qed.

Lemma converges_to_value_like_bot {o} :
  forall (lib : @library o), !(converges_to_value_like lib mk_bot).
Proof.
  introv conv.
  unfold converges_to_value_like in conv; exrepnd.
  apply not_bot_reduces_to_value_like in conv1; sp.
Qed.

Lemma not_in_get_utokens_step_seq_implies_not_int_get_utokens {o} :
  forall a (t : @NTerm o),
    !LIn a (get_utokens_step_seq t)
    -> !LIn a (get_utokens t).
Proof.
  introv i j.
  apply subset_get_utokens_get_utokens_step_seq in j; sp.
Qed.
Hint Resolve not_in_get_utokens_step_seq_implies_not_int_get_utokens : slow.

Lemma wf_marker {o} :
  forall m, @wf_term o (mk_marker m).
Proof.
  introv.
  apply wf_term_eq.
  repeat constructor; simpl; sp.
Qed.
Hint Resolve wf_marker : slow.

Lemma computes_to_value_implies_reduces_to {o} :
  forall lib (t v : @NTerm o),
    computes_to_value lib t v
    -> reduces_to lib t v.
Proof.
  introv comp.
  unfold computes_to_value in comp; sp.
Qed.
Hint Resolve computes_to_value_implies_reduces_to : slow.

Lemma computes_to_pk_implies_reduces_to {o} :
  forall lib (t : @NTerm o) pk,
    computes_to_pk lib t pk
    -> reduces_to lib t (pk2term pk).
Proof.
  introv comp; eauto 3 with slow.
Qed.
Hint Resolve computes_to_pk_implies_reduces_to : slow.

Lemma is_value_like_pk2term {o} :
  forall lib (pk : @param_kind o),
    is_value_like lib (pk2term pk).
Proof.
  introv.
  unfold is_value_like; left.
  eauto 3 with slow.
Qed.
Hint Resolve is_value_like_pk2term : slow.

Lemma computes_to_pk_implies_converges_to_is_value_like {o} :
  forall lib (t : @NTerm o) pk,
    computes_to_pk lib t pk
    -> converges_to_is_value_like lib t.
Proof.
  introv comp.
  exists (pk2term pk); dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_pk_implies_converges_to_is_value_like : slow.

Lemma co_wf_def_implies_iswfpk {o} :
  forall c can (l : list (@BTerm o)),
    co_wf_def c can l -> iswfpk c (oterm (Can can) l).
Proof.
  introv w.
  unfold co_wf_def in w; exrepnd; subst.
  allrw @get_param_from_cop_some; subst.
  repndors; exrepnd; subst; unfold iswfpk.
  - exists pk; allrw @pk2term_eq; auto.
  - exists i; simpl; auto.
Qed.
Hint Resolve co_wf_def_implies_iswfpk : slow.

Lemma ca_wf_def_implies_isinteger {o} :
  forall can (l : list (@BTerm o)),
    ca_wf_def can l -> isinteger (oterm (Can can) l).
Proof.
  introv w.
  unfold ca_wf_def in w; exrepnd; subst.
  exists i; auto.
Qed.
Hint Resolve ca_wf_def_implies_isinteger : slow.

(*
Lemma compute_step_to_atom {o} :
  forall lib (t : @NTerm o) x m u vs,
    is_mrk lib m
    -> wf_term t
    -> subvars (free_vars t) vs
    -> compute_step lib (lsubst_aux t ((x, mk_marker m) :: bot_sub vs)) = csuccess u
    -> converges_to_is_value_like lib u
    -> {w : NTerm & alpha_eq u (lsubst_aux w ((x, mk_marker m) :: bot_sub vs))
                  # reduces_to lib t w}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv ism wft sv cs cm; auto.

  - allsimpl; boolvar; allsimpl.

    + csunf cs; allsimpl.
      rw @compute_step_lib_if_is_mrk in cs; auto; ginv.

    + provefalse.
      allrw subvars_singleton_l.
      rw @sub_find_bot_sub_some_if_in in cs; auto.
      apply converges_to_is_value_like_step in cs; auto.
      apply bottom_doesnt_converge_to_is_value_like in cs; sp.

  - dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf cs; simpl in cs; ginv.
      exists (oterm (Can can) bs); simpl; dands; eauto 2 with slow.

    + SCase "NCan".
      rw @lsubst_aux_oterm in cs.
      destruct bs; ginv.
      rw @map_cons in cs.
      destruct b; ginv.
      destruct l; ginv.

      {
        rw @lsubst_aux_bterm_nil in cs.
        simpl in sv; rw remove_nvars_nil_l in sv.
        rw subvars_app_l in sv; repnd.
        destruct n.

        * simpl in sv0; rw subvars_singleton_l in sv0.
          allsimpl; boolvar; allsimpl; ginv; fold_terms.

          {
            csunf cs; allsimpl; ginv.
            rw @compute_step_if_is_mrk in cs; auto; allsimpl; ginv.
          }

          {
            (* term diverges in r *)
            rw @sub_find_bot_sub_some_if_in in cs; auto.
            csunf cs; allsimpl; ginv; fold_terms.
            unfold converges_to_is_value_like, reduces_to in cm; exrepnd.
            apply reduces_in_atmost_k_steps_ncan_primarg_apply_id_if_is_value_like in cm2;
              exrepnd; subst; tcsp.
            apply reduces_in_atmost_k_steps_ncan_primarg_bot_if_is_value_like in cm1; sp.
          }

        * rw @lsubst_aux_oterm in cs.
          dopid o0 as [can2|ncan2|exc2|abs2] SSCase.
          { SSCase "Can".

            (* Because the principal argument is canonical we can destruct ncan *)
            dopid_noncan ncan SSSCase.

            - SSSCase "NApply".
              csunf cs; simpl in cs.
              apply compute_step_apply_success in cs; repndors; exrepnd; subst; allsimpl.

              { repeat (destruct l; allsimpl; cpx).
                destruct bs; allsimpl; ginv.
                destruct bs; allsimpl; ginv.
                cpx; GC.
                destruct b0; allsimpl; ginv.
                destruct b1; allsimpl; ginv.
                allrw remove_nvars_nil_l; allrw app_nil_r.
                allrw subvars_remove_nvars; allrw memvar_nil;
                allrw @sub_filter_nil_r.

                pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              n
                              [(v,n0)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.
                  { apply implies_covered_cons_weak; sp. }
                  { apply covered_sub_nil. }
                }

                simpl in h.

                exists (lsubst n [(v,n0)]); allrw @fold_subst; dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst n [(v,n0)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.
              }

              { destruct l; allsimpl; ginv.
                repeat (destruct bs; allsimpl; ginv).
                destruct b as [l t].
                destruct l; allsimpl; ginv.
                allrw remove_nvars_nil_l; allrw app_nil_r.

                exists (mk_apseq f t).
                simpl; fold_terms.
                dands; auto.
                apply reduces_to_if_step; csunf; simpl; auto.
              }

            - SSSCase "NApseq".

              clear ind.
              csunf cs; allsimpl.
              apply compute_step_apseq_success in cs; exrepnd; subst.
              destruct l; allsimpl; ginv.
              destruct bs; allsimpl; ginv.
              exists (@mk_nat o (n n0)).
              simpl; fold_terms; dands; auto.
              apply reduces_to_if_step; csunf; simpl.
              boolvar; try omega.
              rw @Znat.Nat2Z.id; auto.

            - SSSCase "NFix".
              csunf cs; simpl in cs.
              apply compute_step_fix_success in cs; repnd.
              destruct bs; allsimpl; cpx; GC; subst.

              exists (mk_apply (oterm (Can can2) l) (mk_fix (oterm (Can can2) l))).
              simpl; allrw @sub_filter_nil_r.
              dands; auto.

              exists 1.
              rw @reduces_in_atmost_k_steps_S.
              exists (mk_apply (oterm (Can can2) l) (mk_fix (oterm (Can can2) l))); dands; auto.
              rw @reduces_in_atmost_k_steps_0; auto.

            - SSSCase "NSpread".
              csunf cs; simpl in cs.
              apply compute_step_spread_success in cs; exrepnd.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct b0 as [l t].
              destruct b1 as [l1 t1].
              destruct b2 as [l2 t2].
              simpl in sv0; allrw app_nil_r; rw subvars_app_l in sv0; repnd.
              allsimpl; cpx; boolvar; allsimpl; tcsp; allrw not_over_or; repnd; GC;
              allrw @sub_filter_nil_r; allrw remove_nvars_nil_l.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t
                              [(va,t1),(vb,t2)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.

                exists (lsubst t [(va,t1),(vb,t2)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t [(va, t1), (vb, t2)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t
                              [(va,t1),(vb,t2)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.

                exists (lsubst t [(va,t1),(vb,t2)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t [(va, t1), (vb, t2)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

            - SSSCase "NDsup".
              csunf cs; simpl in cs.
              apply compute_step_dsup_success in cs; exrepnd.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct b0 as [l t].
              destruct b1 as [l1 t1].
              destruct b2 as [l2 t2].
              allsimpl; cpx; boolvar; allsimpl; tcsp; allrw not_over_or; repnd; GC;
              allrw @sub_filter_nil_r; allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw subvars_app_l; repnd.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t
                              [(va,t1),(vb,t2)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.

                exists (lsubst t [(va,t1),(vb,t2)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t [(va, t1), (vb, t2)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t
                              [(va,t1),(vb,t2)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.

                exists (lsubst t [(va,t1),(vb,t2)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t [(va, t1), (vb, t2)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

            - SSSCase "NDecide".
              csunf cs; simpl in cs.
              apply compute_step_decide_success in cs; exrepnd.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct l; allsimpl; cpx.
              destruct b1 as [l td].
              destruct b  as [l1 tl].
              destruct b0 as [l2 tr].
              allsimpl; cpx; boolvar; allsimpl; tcsp; allrw not_over_or; repnd; GC;
              allrw @sub_filter_nil_r; dorn cs0; repnd; subst;
              allrw app_nil_r; allrw remove_nvars_nil_l.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tl
                              [(v1,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tl [(v1,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tl [(v1,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tr
                              [(v2,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tr [(v2,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tr [(v2,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tl
                              [(v1,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tl [(v1,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tl [(v1,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tr
                              [(v2,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tr [(v2,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tr [(v2,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tl
                              [(v1,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tl [(v1,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tl [(v1,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tr
                              [(v2,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tr [(v2,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tr [(v2,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tl
                              [(v1,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tl [(v1,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tl [(v1,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              tr
                              [(v2,td)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst tr [(v2,td)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst tr [(v2,td)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

            - SSSCase "NCbv".
              csunf cs; simpl in cs.
              apply compute_step_cbv_success in cs; exrepnd.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct b  as [l1 t1].
              allsimpl; cpx; boolvar; allsimpl; tcsp; allrw not_over_or; repnd; GC;
              allrw @sub_filter_nil_r; allrw app_nil_r.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t1
                              [(v,oterm (Can can2) l)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst t1 [(v,oterm (Can can2) l)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t1 [(v,oterm (Can can2) l)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

              + pose proof (simple_lsubst_lsubst_aux_sub_aeq
                              t1
                              [(v,oterm (Can can2) l)]
                              ((x, mk_marker m) :: bot_sub vs))
                  as h.
                repeat (autodimp h hyp); tcsp.

                { rw @cl_sub_cons; dands; sp. }

                { allrw @covered_sub_cons; simpl.
                  allrw @dom_sub_bot_sub; simpl.
                  dands; auto.

                  { apply implies_covered_cons_weak; sp. }

                  { apply covered_sub_nil. }
                }

                simpl in h; boolvar; tcsp.
                allrw @fold_subst.

                exists (lsubst t1 [(v,oterm (Can can2) l)]); dands; auto.
                exists 1.
                rw @reduces_in_atmost_k_steps_S.
                exists (lsubst t1 [(v,oterm (Can can2) l)]); dands; auto.
                rw @reduces_in_atmost_k_steps_0; auto.

            - SSSCase "NSleep".
              csunf cs; simpl in cs.
              apply compute_step_sleep_success in cs; exrepnd.
              subst.
              destruct bs; allsimpl; cpx; GC.
              destruct l; allsimpl; cpx; GC.

              exists (@mk_axiom o); dands; auto.
              apply reduces_to_if_step; sp.

            - SSSCase "NTUni".
              csunf cs; simpl in cs.
              apply compute_step_tuni_success in cs; exrepnd.
              subst.
              destruct bs; allsimpl; cpx; GC.
              destruct l; allsimpl; cpx; GC.

              exists (@mk_uni o n); dands; auto.
              exists 1.
              rw @reduces_in_atmost_k_steps_S.
              exists (@mk_uni o n); dands; auto;
              [|rw @reduces_in_atmost_k_steps_0; auto].

              csunf; simpl.
              unfold compute_step_tuni; simpl; boolvar; try omega.
              rw Znat.Nat2Z.id; auto.

            - SSSCase "NMinus".
              csunf cs; simpl in cs.
              apply compute_step_minus_success in cs; exrepnd.
              subst.
              destruct bs; allsimpl; cpx; GC.
              destruct l; allsimpl; cpx; GC.

              exists (@mk_integer o (- z)); dands; auto.
              apply reduces_to_if_step; simpl.
              unfold compute_step_minus; simpl; auto.

            - SSSCase "NFresh".
              csunf cs; allsimpl; ginv.

            - SSSCase "NTryCatch".
              csunf cs; allsimpl.
              apply compute_step_try_success in cs; exrepnd.
              subst; allsimpl.
              repeat (destruct bs; allsimpl; cpx).
              destruct b as [l1 t1]; allsimpl; cpx.
              destruct b0 as [l2 t2]; allsimpl; cpx.
              allsimpl; allrw @sub_filter_nil_r; allrw app_nil_r; allrw remove_nvars_nil_l.

              exists (mk_atom_eq t1 t1 (oterm (Can can2) l) (mk_bot)).
              simpl; allrw @sub_filter_nil_r; allrw @memvar_singleton; fold_terms.
              dands; eauto 3 with slow;[].

              apply implies_alpha_eq_mk_atom_eq; auto.
              repeat (boolvar; allsimpl; tcsp);
                allrw @sub_find_sub_filter_eq; allrw memvar_singleton;
                boolvar; auto.

            - SSSCase "NParallel".
              csunf cs; allsimpl.
              apply compute_step_parallel_success in cs; subst; allsimpl.
              exists (@mk_axiom o); simpl; dands; auto.
              apply reduces_to_if_step; simpl.
              csunf; simpl.
              unfold compute_step_parallel; auto.

            - SSSCase "NCompOp".
              applydup @compute_step_ncompop_can1 in cs; exrepnd; subst.
              destruct bs; ginv.
              simpl in cs1.
              destruct b as [l1 t1].
              destruct l1; ginv; simpl in cs1.
              allsimpl; allrw remove_nvars_nil_l.
              destruct t1 as [v1|op1 bs1]; allsimpl.

              + provefalse.
                allrw @sub_filter_nil_r; boolvar; allsimpl; allrw subvars_cons_l; repnd.

                * csunf cs; allsimpl; dcwf h;[].
                  rw @compute_step_if_is_mrk in cs; auto; allsimpl; ginv.

                * repeat (onerw @sub_find_bot_sub_some_if_in; auto).
                  csunf cs; allsimpl; dcwf h; allsimpl; ginv; fold_terms;[].

                  unfold converges_to_is_value_like, reduces_to in cm; exrepnd.
                  apply reduces_in_atmost_k_steps_ncompop_primarg2_apply_id_if_is_value_like in cm2;
                    exrepnd; subst; tcsp.
                  apply reduces_in_atmost_k_steps_ncompop_primarg2_bot_if_is_value_like in cm1;
                    exrepnd; tcsp.

              + ginv.
                allrw @sub_filter_nil_r.
                dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

                * SSSSCase "Can".
                  csunf cs; simpl in cs; dcwf h; allsimpl;[].
                  apply compute_step_compop_success_can_can in cs; exrepnd; repndors; exrepnd; subst;
                  allrw @get_param_from_cop_some; subst; allsimpl;
                  destruct l, bs1; allsimpl; ginv;
                  repeat (destruct bs; allsimpl; ginv);
                  destruct b as [l1 u1]; destruct b0 as [l2 u2]; allsimpl;
                  allunfold @nobnd; ginv; allrw memvar_nil; allrw @sub_filter_nil_r;
                  allrw remove_nvars_nil_l; allrw app_nil_r.

                  { exists (if Z_lt_le_dec n1 n2 then u1 else u2); dands; auto;
                    [boolvar; auto|].
                    apply reduces_to_if_step.
                    csunf; simpl.
                    unfold compute_step_comp; simpl; auto.
                  }

                  { exists (if param_kind_deq pk1 pk2 then u1 else u2); dands; auto;
                    [boolvar; auto|].
                    apply reduces_to_if_step.
                    csunf; simpl; dcwf h;[].
                    unfold compute_step_comp; simpl; auto.
                    allrw @get_param_from_cop_pk2can; auto.
                  }

                * SSSSCase "NCan".
                  rw @compute_step_ncompop_ncan2 in cs; dcwf h; allsimpl;[].
                  allrw @sub_filter_nil_r.
                  remember (compute_step
                              lib
                              (oterm (NCan ncan3)
                                     (map
                                        (fun b : BTerm =>
                                           lsubst_bterm_aux
                                             b
                                             ((x, mk_marker m) :: bot_sub vs))
                                        bs1))) as cs3;
                    symmetry in Heqcs3; destruct cs3; ginv; fold_terms.

                  applydup @converges_to_is_value_like_ncompop in cm.

                  assert (converges_to_is_value_like lib n)
                    as cvl.
                  { repndors; exrepnd; eauto 3 with slow.
                    exists e; unfold isvalue_like; dands; auto; tcsp.
                  }

                  pose proof (ind (oterm (NCan ncan3) bs1) (oterm (NCan ncan3) bs1) []) as h;
                    clear ind; repeat (autodimp h hyp); tcsp.
                  pose proof (h x m n vs) as k;
                    clear h; repeat (autodimp k hyp); tcsp; exrepnd.

                  { apply wf_oterm_iff in wft; repnd; allsimpl.
                    pose proof (wft (nobnd (oterm (NCan ncan3) bs1))) as w.
                    autodimp w hyp. }

                  { simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; sp. }

                  exists (oterm
                            (NCan (NCompOp c))
                            (nobnd (oterm (Can can2) l)
                                   :: nobnd w
                                   :: bs));
                    simpl; fold_terms; dands; allrw @sub_filter_nil_r.

                  { apply alpha_eq_oterm_snd_subterm.
                    apply alphaeqbt_nilv2; auto. }

                  { apply reduce_to_prinargs_comp_can; tcsp.
                    apply reduces_to_symm.
                    apply co_wf_def_implies_iswfpk.
                    eapply co_wf_def_len_implies;[|eauto]; autorewrite with slow; auto. }

                * SSSSCase "Exc".
                  csunf cs; allsimpl; ginv; dcwf h; allsimpl; ginv;[].
                  exists (oterm Exc bs1); simpl; dands; auto.
                  apply reduces_to_if_step; sp.
                  csunf; simpl; dcwf h; tcsp.

                * SSSSCase "Abs".
                  rw @compute_step_ncompop_abs2 in cs.
                  dcwf h; allsimpl;[].
                  remember (compute_step_lib
                              lib abs3
                              (map
                                 (fun b : BTerm =>
                                    lsubst_bterm_aux
                                      b
                                      ((x, mk_marker m) :: bot_sub vs))
                                 bs1)) as cs3;
                    symmetry in Heqcs3; destruct cs3; ginv; fold_terms.

                  applydup @converges_to_is_value_like_ncompop in cm.

                  assert (converges_to_is_value_like lib n)
                    as cvl.
                  { repndors; exrepnd; eauto 3 with slow.
                    exists e; unfold isvalue_like; dands; auto; tcsp.
                  }

                  pose proof (ind (oterm (Abs abs3) bs1) (oterm (Abs abs3) bs1) []) as h;
                    clear ind; repeat (autodimp h hyp); tcsp.
                  pose proof (h x m n vs) as k;
                    clear h; repeat (autodimp k hyp); tcsp; exrepnd.

                  { apply wf_oterm_iff in wft; repnd; allsimpl.
                    pose proof (wft (nobnd (oterm (Abs abs3) bs1))) as w.
                    autodimp w hyp. }

                  { simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; sp. }

                  exists (oterm
                            (NCan (NCompOp c))
                            (nobnd (oterm (Can can2) l)
                                   :: nobnd w
                                   :: bs));
                    simpl; fold_terms; dands; allrw @sub_filter_nil_r.

                  { apply alpha_eq_oterm_snd_subterm.
                    apply alphaeqbt_nilv2; auto. }

                  { apply reduce_to_prinargs_comp_can; tcsp.
                    apply reduces_to_symm.
                    apply co_wf_def_implies_iswfpk.
                    eapply co_wf_def_len_implies;[|eauto]; autorewrite with slow; auto. }

            - SSSCase "NArithOp".
              applydup @compute_step_narithop_can1 in cs; exrepnd; subst.
              destruct bs; ginv.
              simpl in cs1.
              destruct b as [l1 t1].
              destruct l1; ginv; allsimpl.
              allrw @sub_filter_nil_r; allrw remove_nvars_nil_l.
              destruct t1 as [v1|op1 bs1]; ginv; allsimpl; ginv.

              + provefalse.
                allrw subvars_cons_l; repnd.
                boolvar; allsimpl.

                * csunf cs; allsimpl; dcwf h; [].
                  rw @compute_step_if_is_mrk in cs; auto; allsimpl; ginv.

                * repeat (onerw @sub_find_bot_sub_some_if_in; auto).
                  csunf cs; allsimpl; fold_terms; ginv; dcwf h; allsimpl; ginv; [].

                  unfold converges_to_is_value_like, reduces_to in cm; exrepnd.
                  apply reduces_in_atmost_k_steps_narithop_primarg2_apply_id_if_is_value_like in cm2;
                    exrepnd; subst; tcsp.
                  apply reduces_in_atmost_k_steps_narithop_primarg2_bot_if_is_value_like in cm1;
                    exrepnd; tcsp.

              + dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

                * SSSSCase "Can".
                  csunf cs; simpl in cs; dcwf h; allsimpl; [].
                  apply compute_step_arithop_success_can_can in cs; exrepnd; repndors; exrepnd; subst;
                  allapply @get_param_from_cop_pki; subst;
                  destruct l, bs1; allsimpl; ginv;
                  repeat (destruct bs; allsimpl; ginv).

                  exists (@oterm o (Can (Nint (get_arith_op a n1 n2))) []); dands; auto.
                  apply reduces_to_if_step.
                  csunf; simpl.
                  unfold compute_step_arith; simpl; auto.

                * SSSSCase "NCan".
                  rw @compute_step_narithop_ncan2 in cs; dcwf h; allsimpl;[].
                  remember (compute_step
                              lib
                              (oterm (NCan ncan3)
                                     (map
                                        (fun b : BTerm =>
                                           lsubst_bterm_aux
                                             b
                                             ((x, mk_marker m) :: bot_sub vs))
                                        bs1))) as cs3;
                    symmetry in Heqcs3; destruct cs3; ginv; fold_terms.

                  applydup @converges_to_is_value_like_narithop in cm.

                  assert (converges_to_is_value_like lib n)
                    as cvl.
                  { unfold converges_to_is_value_like; repndors; exrepnd.
                    - unfold computes_to_value in cm1; repnd.
                      exists (@mk_integer o i); unfold isvalue_like.
                      simpl; dands; sp.
                    - exists e; unfold isvalue_like; dands; auto; tcsp.
                  }

                  pose proof (ind (oterm (NCan ncan3) bs1) (oterm (NCan ncan3) bs1) []) as h;
                    clear ind; repeat (autodimp h hyp); tcsp.
                  pose proof (h x m n vs) as k;
                    clear h; repeat (autodimp k hyp); tcsp; exrepnd.

                  { apply wf_oterm_iff in wft; repnd; allsimpl.
                    pose proof (wft (nobnd (oterm (NCan ncan3) bs1))) as w.
                    autodimp w hyp. }

                  { simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; sp. }

                  exists (oterm
                            (NCan (NArithOp a))
                            (nobnd (oterm (Can can2) l)
                                   :: nobnd w
                                   :: bs));
                    simpl; fold_terms; dands; allrw @sub_filter_nil_r.

                  { apply alpha_eq_oterm_snd_subterm.
                    apply alphaeqbt_nilv2; auto. }

                  { apply reduce_to_prinargs_arith_can; tcsp.
                    apply reduces_to_symm.
                    apply ca_wf_def_implies_isinteger.
                    eapply ca_wf_def_len_implies;[|eauto]; autorewrite with slow; auto. }

                * SSSSCase "Exc".
                  csunf cs; allsimpl; ginv; dcwf h; ginv.
                  exists (oterm Exc bs1); simpl; dands; auto.
                  apply reduces_to_if_step; sp.
                  csunf; simpl; dcwf h; auto.

                * SSSSCase "Abs".
                  rw @compute_step_narithop_abs2 in cs.
                  dcwf h; allsimpl;[].
                  remember (compute_step_lib
                              lib abs3
                              (map
                                 (fun b : BTerm =>
                                    lsubst_bterm_aux
                                      b
                                      ((x, mk_marker m) :: bot_sub vs))
                                 bs1)) as cs3;
                    symmetry in Heqcs3; destruct cs3; ginv; fold_terms.

                  applydup @converges_to_is_value_like_narithop in cm.

                  assert (converges_to_is_value_like lib n)
                    as cvl.
                  { unfold converges_to_is_value_like; repndors; exrepnd.
                    - unfold computes_to_value in cm1; repnd.
                      exists (@mk_integer o i); unfold isvalue_like.
                      simpl; dands; sp.
                    - exists e; unfold isvalue_like; dands; auto; tcsp.
                  }

                  pose proof (ind (oterm (Abs abs3) bs1) (oterm (Abs abs3) bs1) []) as h;
                    clear ind; repeat (autodimp h hyp); tcsp.
                  pose proof (h x m n vs) as k;
                    clear h; repeat (autodimp k hyp); tcsp; exrepnd.

                  { apply wf_oterm_iff in wft; repnd; allsimpl.
                    pose proof (wft (nobnd (oterm (Abs abs3) bs1))) as w.
                    autodimp w hyp. }

                  { simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; sp. }

                  exists (oterm
                            (NCan (NArithOp a))
                            (nobnd (oterm (Can can2) l)
                                   :: nobnd w
                                   :: bs));
                    simpl; fold_terms; dands; allrw @sub_filter_nil_r.

                  { apply alpha_eq_oterm_snd_subterm.
                    apply alphaeqbt_nilv2; auto. }

                  { apply reduce_to_prinargs_arith_can; tcsp.
                    apply reduces_to_symm.
                    apply ca_wf_def_implies_isinteger.
                    eapply ca_wf_def_len_implies;[|eauto]; autorewrite with slow; auto. }

            - SSSCase "NCanTest".
              csunf cs; simpl in cs.
              apply compute_step_can_test_success in cs; exrepnd; subst.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct bs; allsimpl; cpx.
              destruct b as [l1 t1].
              destruct b0 as [l2 t2].
              allsimpl; cpx.
              allrw remove_nvars_nil_l; allrw app_nil_r; boolvar; cpx;
              allrw subvars_app_l; repnd; GC; allrw @sub_filter_nil_r.

              exists (if canonical_form_test_for c can2 then t1 else t2);
                simpl; dands; auto.

              { destruct (canonical_form_test_for c can2); auto. }

              { exists 1; rw @reduces_in_atmost_k_steps_S.
                exists (if canonical_form_test_for c can2 then t1 else t2);
                  simpl; dands; sp. }

          }

          { SSCase "NCan".

            rw @compute_step_ncan_ncan in cs.
            remember (compute_step
                        lib
                        (oterm (NCan ncan2)
                               (map
                                  (fun b : BTerm =>
                                     lsubst_bterm_aux b ((x, mk_marker m) :: bot_sub vs)) l)))
              as cs1; symmetry in Heqcs1; destruct cs1; ginv.

            applydup @converges_to_is_value_like_ncan in cm; exrepnd.

            assert (converges_to_is_value_like lib n) as cvl.
            { unfold converges_to_is_value_like; exists u; dands; sp. }

            pose proof (ind (oterm (NCan ncan2) l) (oterm (NCan ncan2) l) []) as h;
              clear ind; repeat (autodimp h hyp); tcsp.
            pose proof (h x m n vs) as k;
              clear h; repeat (autodimp k hyp); tcsp; exrepnd.

            { apply wf_oterm_iff in wft; repnd; allsimpl.
              pose proof (wft (nobnd (oterm (NCan ncan2) l))) as w.
              autodimp w hyp. }

            exists (oterm (NCan ncan) (nobnd w :: bs));
              simpl; fold_terms; dands; allrw @sub_filter_nil_r.

            { apply alpha_eq_oterm_fst_subterm.
              apply alphaeqbt_nilv2; auto. }

            { apply reduces_to_prinarg; tcsp. }

          }

          { SSCase "Exc".

            csunf cs; allsimpl.
            applydup @compute_step_catch_success in cs as i; dorn i; exrepnd; subst.

            - repeat (destruct l; allsimpl; ginv).
              repeat (destruct bs; allsimpl; ginv).
              destruct b0 as [l1 t1].
              destruct b1 as [l2 t2].
              destruct b2 as [l3 t3].
              destruct b3 as [l4 t4].
              allsimpl; ginv; allsimpl.
              allrw app_nil_r; allrw @sub_filter_nil_r; allrw remove_nvars_nil_l.
              allrw memvar_singleton.

              allrw subvars_app_l; repnd.

              pose proof (simple_lsubst_lsubst_aux_sub_aeq
                            t4
                            [(v,t2)]
                            ((x, mk_marker m) :: bot_sub vs))
                as h.
              repeat (autodimp h hyp); tcsp.

              { rw @cl_sub_cons; dands; sp. }

              { allrw @covered_sub_cons; simpl.
                allrw @dom_sub_bot_sub; simpl.
                dands; auto.
                { apply implies_covered_cons_weak; sp. }
                { apply covered_sub_nil. }
              }

              simpl in h.
              allrw @fold_subst.

              exists (mk_atom_eq t3 t1 (subst t4 v t2) (mk_exception t1 t2)); dands; auto.
              { simpl.
                allrw @sub_filter_nil_r.
                apply implies_alpha_eq_mk_atom_eq; auto.
                allrw memvar_singleton; auto. }

              apply reduces_to_if_step; sp.

            - exists (oterm Exc l); simpl; dands; auto.
              apply reduces_to_if_step; simpl.
              csunf; simpl.
              destruct ncan; tcsp.
          }

          { SSCase "Abs".

            rw @compute_step_ncan_abs in cs.
            remember (compute_step_lib
                        lib abs2
                        (map
                           (fun b : BTerm =>
                              lsubst_bterm_aux b ((x, mk_marker m) :: bot_sub vs)) l))
              as csl; symmetry in Heqcsl; destruct csl; ginv.

            applydup @converges_to_is_value_like_ncan in cm; exrepnd.

            assert (converges_to_is_value_like lib n)
              as cvl.
            { unfold converges_to_is_value_like; exists u; sp. }

            pose proof (ind (oterm (Abs abs2) l) (oterm (Abs abs2) l) []) as h;
              clear ind; repeat (autodimp h hyp); tcsp.
            pose proof (h x m n vs) as k;
              clear h; repeat (autodimp k hyp); tcsp; exrepnd.

            { apply wf_oterm_iff in wft; repnd; allsimpl.
              pose proof (wft (nobnd (oterm (Abs abs2) l))) as w.
              autodimp w hyp. }

            exists (oterm
                      (NCan ncan)
                      (nobnd w :: bs));
              simpl; fold_terms; dands; allrw @sub_filter_nil_r.

            { apply alpha_eq_oterm_fst_subterm.
              apply alphaeqbt_nilv2; auto. }

            { apply reduces_to_prinarg; tcsp. }
          }
      }

      { (* fresh case *)
        csunf cs; allsimpl.
        apply @compute_step_fresh_success in cs; repnd; subst.
        destruct bs; allsimpl; ginv.
        allrw app_nil_r; allrw memvar_singleton.
        boolvar; repndors; exrepnd; subst; allsimpl.

        - allrw @sub_filter_bot_sub.
          destruct n as [x|op bs]; allsimpl; ginv.
          allrw @sub_find_bot_sub_eq.
          boolvar; ginv; fold_terms.
          unfold converges_to_is_value_like in cm; exrepnd.
          apply not_fresh_id_reduces_to_is_value_like in cm1; sp.

        - assert (isvalue_like n) as isvn.
          { apply isvalue_like_lsubst_aux_implies in cs0; repndors; auto.
            exrepnd; subst.
            rw @sub_find_sub_filter_eq in cs1; rw memvar_singleton in cs1.
            boolvar; ginv.
            apply sub_find_some in cs1; apply implies_in_bot_sub in cs1; repnd; subst.
            apply isvalue_like_bot in cs0; sp.
          }

          exists (pushdown_fresh n0 n); simpl; dands.
          + pose proof (cl_lsubst_aux_pushdown_fresh
                          n n0 ((n0, mk_marker m) :: bot_sub vs)) as h.
            repeat (autodimp h hyp); eauto 3 with slow.
            simpl in h; rw memvar_singleton in h; boolvar; eauto with slow.
          + apply reduces_to_if_step.
            apply compute_step_fresh_if_isvalue_like; auto.

        - remember (get_fresh_atom (lsubst_aux n (sub_filter (bot_sub vs) [n0]))) as a.
          pose proof (ind n (subst n n0 (mk_utoken a)) [n0]) as h; clear ind.
          repeat (autodimp h hyp).
          { unfold subst; rw @simple_size_lsubst; eauto with slow. }

          assert (!LIn a (get_utokens (lsubst_aux n (sub_filter (bot_sub vs) [n0])))) as nia.
          { subst.
            pose proof (get_fresh_atom_prop (lsubst_aux n (sub_filter (bot_sub vs) [n0]))) as p; tcsp. }

          assert (wf_term x) as wfx.
          { eapply compute_step_preserves_wf; eauto.
            apply wf_term_subst; eauto 3 with slow.
            apply wf_fresh_iff in wft.
            apply lsubst_aux_preserves_wf_term2; eauto 2 with slow. }

          assert (!LIn n0 (free_vars x)) as nin0x.
          { apply compute_step_preserves in cs2; repnd.
            rw subvars_eq in cs0; intro i; apply cs0 in i.
            unfsubst in i.
            rw @free_vars_lsubst_aux_cl in i; eauto with slow; allsimpl.
            rw in_remove_nvars in i; allsimpl; sp. }

          pose proof (get_fresh_atom_prop (lsubst_aux n (sub_filter (bot_sub vs) [n0]))) as gfa.
          rw <- Heqa in gfa.

          assert (!LIn a (get_utokens (subst_utokens x [(a, mk_var n0)]))) as niasx.
          { intro i.
            apply get_utokens_subst_utokens_subset in i; allsimpl.
            unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
            apply in_remove in i; repnd; tcsp.
          }

          pose proof (h n0 m x vs) as k; clear h.
          repeat (autodimp k hyp).
          { apply wf_fresh_iff in wft.
            apply wf_term_subst; eauto 2 with slow. }
          { unfsubst; rw @free_vars_lsubst_aux_cl; eauto with slow. }
          { rw <- @cl_lsubst_lsubst_aux; eauto with slow.
            rw <- @cl_lsubst_lsubst_aux in cs2; eauto with slow.
            unfold subst; unfold subst in cs2.
            rw @simple_lsubst_lsubst_sub_aeq4; eauto with slow.
            simpl; rw memvar_singleton; boolvar; auto. }
          { pose proof (converges_to_is_value_like_fresh_implies
                          lib (subst_utokens x [(a, mk_var n0)]) n0) as conv.
            repeat (autodimp conv hyp).
            { apply wf_subst_utokens; eauto 3 with slow. }
            pose proof (conv a) as cv; clear conv.
            autodimp cv hyp.
            apply converges_to_is_value_like_if.
            eapply converges_to_value_like_alpha_eq;[|exact cv].
            apply simple_subst_subst_utokens_aeq; auto.
          }

          exrepnd; fold_terms.

          assert (a = get_fresh_atom n) as ea.
          { assert (get_utokens (lsubst_aux n (sub_filter (bot_sub vs) [n0]))
                    = get_utokens n) as e1.
            { apply get_utokens_lsubst_aux_trivial1.
              rw @sub_filter_bot_sub.
              rw @get_utokens_sub_bot_sub; auto. }
            rw Heqa; unfold get_fresh_atom; rw e1; auto. }

          apply isnoncan_like_lsubst_aux in cs1; repndors.

          {
            provefalse.
            exrepnd; subst n; allsimpl.
            allrw @sub_find_sub_filter_eq.
            allrw memvar_singleton; boolvar; ginv.
            allrw cs3.
            rw @sub_find_bot_sub_eq in cs3; boolvar; ginv.
            rw @cl_subst_trivial in cs2; allsimpl; tcsp; GC.
            pose proof (converges_to_is_value_like_fresh_implies
                          lib
                          (subst_utokens x [(get_fresh_atom (mk_var v), mk_var n0)])
                          n0) as h.
            repeat (autodimp h hyp).
            { apply wf_subst_utokens; eauto with slow. }
            pose proof (h (get_fresh_atom (mk_var v))) as q; clear h.
            autodimp q hyp.
            pose proof (simple_subst_subst_utokens_aeq
                          x (get_fresh_atom (mk_var v)) n0) as h.
            repeat (autodimp h hyp).
            eapply converges_to_value_like_alpha_eq in h; eauto.
            apply converges_to_value_like_step in cs2; auto.
            apply converges_to_value_like_bot in cs2; sp.
          }

          pose proof (reduces_to_fresh lib n w n0) as r2f.
          rw <- ea in r2f; simpl in r2f.
          repeat (autodimp r2f hyp).
          { apply wf_fresh_iff in wft; auto. }
          exrepnd.

          exists (mk_fresh n0 z); dands; auto.

          simpl; rw memvar_singleton; boolvar; fold_terms.
          apply implies_alpha_eq_mk_fresh.

          assert (!LIn n0 (free_vars w)) as ni0.
          { apply reduces_to_free_vars in k0.
            intro i; apply k0 in i.
            unfsubst in i; rw @free_vars_lsubst_aux_cl in i; eauto 2 with slow.
            allsimpl; rw in_remove_nvars in i; allsimpl; sp.
          }

          pose proof (lsubst_aux_sub_filter w ((n0, mk_marker m) :: bot_sub vs) [n0]) as e.
          autodimp e hyp.
          { apply disjoint_singleton_r; auto. }
          simpl in e; rw memvar_singleton in e; boolvar; tcsp.
          rw <- e in k1.

          apply (alpha_eq_subst_utokens _ _ [(a, mk_var n0)] [(a, mk_var n0)]) in k1; eauto 2 with slow.
          eapply alpha_eq_trans;[exact k1|].

          apply (lsubst_aux_alpha_congr_same_cl_sub _ _ (sub_filter (bot_sub vs) [n0])) in r2f0; eauto 2 with slow.
          eapply alpha_eq_trans;[|apply alpha_eq_sym;exact r2f0].

          apply alpha_eq_sym.
          apply lsubst_aux_subst_utokens_disj_cl2; simpl; eauto 3 with slow.
          { apply disjoint_singleton_r.
            rw @sub_filter_bot_sub.
            rw @get_utokens_sub_bot_sub; simpl; sp. }
          { apply disjoint_singleton_l.
            rw @sub_filter_bot_sub.
            rw @dom_sub_bot_sub.
            rw in_remove_nvars; simpl; sp. }

        - allrw @sub_filter_bot_sub.
          destruct n as [z|op bs]; allsimpl; ginv.
          allrw @sub_find_bot_sub_eq.
          boolvar; ginv; fold_terms.
          unfold converges_to_is_value_like in cm; exrepnd.
          apply not_fresh_id_reduces_to_is_value_like in cm1; sp.

        - apply isvalue_like_lsubst_aux_implies in cs0; repndors.

          {
            exists (pushdown_fresh n0 n); simpl; dands.
            + pose proof (cl_lsubst_aux_pushdown_fresh
                            n n0 ((x, mk_marker m) :: bot_sub vs)) as h.
              repeat (autodimp h hyp); eauto 3 with slow.
              simpl in h; rw memvar_singleton in h; boolvar; tcsp; eauto with slow.
            + apply reduces_to_if_step.
              apply compute_step_fresh_if_isvalue_like; auto.
          }

          {
            exrepnd; allsimpl; boolvar; allsimpl; boolvar; ginv.

            - unfold isvalue_like in cs0; allsimpl; sp.

            - subst; allsimpl; boolvar; tcsp; GC.
              allrw @sub_filter_bot_sub.
              allrw @sub_find_bot_sub_eq.
              boolvar; tcsp; ginv.
              unfold isvalue_like in cs0; allsimpl; sp.
          }

        - rename x into v.
          rename x0 into x.

          remember (get_fresh_atom (lsubst_aux n ((v,mk_marker m) :: sub_filter (bot_sub vs) [n0]))) as a.
          pose proof (ind n (subst n n0 (mk_utoken a)) [n0]) as h; clear ind.
          repeat (autodimp h hyp).
          { unfold subst; rw @simple_size_lsubst; eauto with slow. }

          pose proof (get_fresh_atom_prop (lsubst_aux n ((v,mk_marker m) :: sub_filter (bot_sub vs) [n0]))) as gfa.
          rw <- Heqa in gfa.

          assert (wf_term x) as wfx.
          { eapply compute_step_preserves_wf; eauto.
            apply wf_term_subst; eauto 3 with slow.
            apply wf_fresh_iff in wft.
            apply lsubst_aux_preserves_wf_term2; eauto with slow.
          }

          assert (!LIn n0 (free_vars x)) as nin0x.
          { apply compute_step_preserves in cs2; repnd.
            rw subvars_eq in cs0; intro i; apply cs0 in i.
            unfsubst in i.
            rw @free_vars_lsubst_aux_cl in i; eauto with slow; allsimpl.
            rw in_remove_nvars in i; allsimpl; sp. }

          assert (!LIn a (get_utokens (subst_utokens x [(a, mk_var n0)]))) as niasx.
          { intro i.
            apply get_utokens_subst_utokens_subset in i; allsimpl.
            unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
            apply in_remove in i; repnd; tcsp.
          }

          pose proof (h v m x vs) as k; clear h.
          repeat (autodimp k hyp).
          { apply wf_fresh_iff in wft.
            apply wf_term_subst; eauto 2 with slow. }
          { unfsubst; rw @free_vars_lsubst_aux_cl; eauto with slow. }
          { rw <- @cl_lsubst_lsubst_aux; eauto with slow.
            rw <- @cl_lsubst_lsubst_aux in cs2; eauto with slow.
            unfold subst; unfold subst in cs2.
            rw @simple_lsubst_lsubst_sub_aeq4; eauto with slow.
            simpl; rw memvar_singleton; boolvar; tcsp. }
          { pose proof (converges_to_is_value_like_fresh_implies
                          lib (subst_utokens x [(a, mk_var n0)]) n0) as conv.
            repeat (autodimp conv hyp).
            { apply wf_subst_utokens; eauto 3 with slow. }
            pose proof (conv a) as cv; clear conv.
            autodimp cv hyp.
            apply converges_to_is_value_like_if.
            eapply converges_to_value_like_alpha_eq;[|exact cv].
            apply simple_subst_subst_utokens_aeq; auto.
          }

          exrepnd; fold_terms.

          assert (a = get_fresh_atom n) as ea.
          { assert (get_utokens (lsubst_aux n ((v,mk_marker m) :: sub_filter (bot_sub vs) [n0]))
                    = get_utokens n) as e1.
            { apply get_utokens_lsubst_aux_trivial1.
              rw @sub_filter_bot_sub.
              unfold get_utokens_sub; simpl.
              fold (get_utokens_sub (@bot_sub o (remove_nvars [n0] vs))).
              rw @get_utokens_sub_bot_sub; auto. }
            rw Heqa; unfold get_fresh_atom; rw e1; auto. }

          apply isnoncan_like_lsubst_aux in cs1; repndors.

          {
            exrepnd; subst n; allsimpl.
            boolvar; ginv.
            { unfsubst in cs2; allsimpl; GC.
              fold (@mk_marker o m) in cs2.
              rw @compute_step_if_is_mrk in cs2; auto; ginv. }
            allrw @sub_find_sub_filter_eq.
            allrw memvar_singleton; boolvar; ginv.
            allrw cs3.
            rw @sub_find_bot_sub_eq in cs3; boolvar; ginv.
            rw @cl_subst_trivial in cs2; allsimpl; tcsp; GC.
            pose proof (converges_to_is_value_like_fresh_implies
                          lib
                          (subst_utokens x [(get_fresh_atom (mk_var v), mk_var n0)])
                          n0) as h.
            repeat (autodimp h hyp).
            { apply wf_subst_utokens; eauto with slow. }
            pose proof (h (get_fresh_atom (mk_var v))) as q; clear h.
            autodimp q hyp.
            pose proof (simple_subst_subst_utokens_aeq
                          x (get_fresh_atom (mk_var v)) n0) as h.
            repeat (autodimp h hyp).
            eapply converges_to_value_like_alpha_eq in h; eauto.
            apply converges_to_value_like_step in cs2; auto.
            apply converges_to_value_like_bot in cs2; sp.
          }

          pose proof (reduces_to_fresh lib n w n0) as r2f.
          rw <- ea in r2f; simpl in r2f.
          repeat (autodimp r2f hyp).
          { apply wf_fresh_iff in wft; auto. }
          exrepnd.

          exists (mk_fresh n0 z); dands; auto.

          simpl; rw memvar_singleton; boolvar; fold_terms; tcsp.
          apply implies_alpha_eq_mk_fresh.

          assert (!LIn n0 (free_vars w)) as ni0.
          { apply reduces_to_free_vars in k0.
            intro i; apply k0 in i.
            unfsubst in i; rw @free_vars_lsubst_aux_cl in i; eauto 2 with slow.
            allsimpl; rw in_remove_nvars in i; allsimpl; sp.
          }

          pose proof (lsubst_aux_sub_filter w ((v, mk_marker m) :: bot_sub vs) [n0]) as e.
          autodimp e hyp.
          { apply disjoint_singleton_r; auto. }
          simpl in e; rw memvar_singleton in e; boolvar; tcsp.
          rw <- e in k1.

          apply (alpha_eq_subst_utokens _ _ [(a, mk_var n0)] [(a, mk_var n0)]) in k1; eauto 2 with slow.
          eapply alpha_eq_trans;[exact k1|].

          apply (lsubst_aux_alpha_congr_same_cl_sub _ _ ((v, mk_marker m) :: sub_filter (bot_sub vs) [n0])) in r2f0; eauto 3 with slow.
          eapply alpha_eq_trans;[|apply alpha_eq_sym;exact r2f0].

          apply alpha_eq_sym.
          apply lsubst_aux_subst_utokens_disj_cl2; simpl; eauto 3 with slow.
          { apply disjoint_singleton_r.
            rw @sub_filter_bot_sub.
            unfold get_utokens_sub; simpl.
            fold (get_utokens_sub (@bot_sub o (remove_nvars [n0] vs))).
            rw @get_utokens_sub_bot_sub; auto; sp. }
          { apply disjoint_singleton_l.
            rw @sub_filter_bot_sub.
            rw @dom_sub_bot_sub.
            simpl; rw in_remove_nvars; simpl; sp. }
      }

    + SCase "Exc".

      csunf cs; allsimpl; ginv.
      exists (oterm Exc bs); simpl; dands; auto.
      apply reduces_to_symm.

    + SCase "Abs".

      csunf cs; simpl in cs.
      applydup @compute_step_lib_success in cs; exrepnd; subst.

      dup cs1 as cs2.
      apply found_entry_change_bs with (bs2 := bs) in cs2;
        [|rw map_map; unfold compose; apply eq_maps; intros b i;
          destruct b; unfold num_bvars; simpl; complete auto].

      exists (mk_instance vars bs rhs).

      dands; auto;
      [|apply reduces_to_if_step; simpl;
       eapply compute_step_lib_success_change_bs;[|eauto]; auto;
       rw map_map; unfold compose; apply eq_maps; intros b i;
       destruct b; unfold num_bvars; simpl; complete auto].

      unfold mk_instance.
      pose proof (lsubst_aux_sosub_aeq
                    rhs
                    (mk_abs_subst vars bs)
                    ((x, mk_marker m) :: bot_sub vs)) as h.
      repeat (autodimp h hyp).

      * apply cl_sub_cons; dands; sp.

      * apply found_entry_implies_matching_entry in cs2.
        unfold correct_abs in correct; repnd.
        apply socovered_implies_cover_so_vars; auto.
        unfold matching_entry in cs2; sp.

      * apply alpha_eq_sym in h.
        eapply alpha_eq_trans;[|exact h]; clear h.

        pose proof (sosub_trim
                      rhs
                      (lsubst_aux_sosub ((x, mk_marker m) :: bot_sub vs)
                                        (mk_abs_subst vars bs))
                      (sub2sosub ((x, mk_marker m) :: bot_sub vs)))
          as aeq.
        repeat (autodimp aeq hyp).

        { apply implies_cover_so_vars_lsubst_aux_sosub; auto.
          unfold correct_abs in correct; repnd.
          apply socovered_implies_cover_so_vars; auto.
          apply found_entry_implies_matching_entry in cs2; auto.
          unfold matching_entry in cs2; sp. }

        { rw @sodom_lsubst_aux_sosub.
          unfold correct_abs in correct; repnd.
          rw <- @mk_abs_subst_some_prop2; auto.
          apply found_entry_implies_matching_entry in cs2; auto.
          unfold matching_entry in cs2; sp. }

        { apply alphaeq_sym in aeq.
          apply alphaeq_eq in aeq.
          eapply alpha_eq_trans;[|exact aeq]; clear aeq.
          rw @lsubst_aux_sosub_mk_abs_subst; auto. }
Qed.

Lemma compute_step_to_atom2 {o} :
  forall lib (t : @NTerm o) x m u,
    is_mrk lib m
    -> wf_term t
    -> compute_step lib (lsubst_aux t ((x, mk_marker m) :: bot_sub_fv t)) = csuccess u
    -> converges_to_is_value_like lib u
    -> {w : NTerm & alpha_eq u (lsubst_aux w ((x, mk_marker m) :: bot_sub_fv t))
                  # reduces_to lib t w}.
Proof.
  introv ism cs conv.
  allunfold @bot_sub_fv.
  apply compute_step_to_atom; auto.
Qed.
*)

(*
Lemma reduces_to_preserves {o} :
  forall lib (t u : @NTerm o),
    reduces_to lib t u
    -> (subvars (free_vars u) (free_vars t)
        # subset (get_markers u) (get_markers t ++ get_markers_lib lib)
        # (wf_term t -> wf_term u)).
Proof.
  introv r.
  unfold reduces_to in r; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv comp.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst; dands; auto.
    introv i; allrw in_app_iff; sp.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    pose proof (compute_step_preserves lib t u0 comp1) as h; repnd.
    apply IHk in comp0; repnd.
    dands.
    + eapply subvars_trans; eauto.
    + introv i; apply comp3 in i; allrw in_app_iff; dorn i; tcsp.
      apply h1 in i; allrw in_app_iff; sp.
    + allrw @nt_wf_eq; sp.
Qed.

Definition not_marked_lib {o} (m : marker) (t : @NTerm o) (lib : @library o) :=
  !LIn m (get_markers t ++ get_markers_lib lib).

Lemma not_marked_if_subset {o} :
  forall lib m (t u : @NTerm o),
    not_marked_lib m t lib
    -> subset (get_markers u) (get_markers t ++ get_markers_lib lib)
    -> not_marked_lib m u lib.
Proof.
  introv nm sub i.
  rw in_app_iff in i; dorn i.
  - apply sub in i; allrw in_app_iff; dorn i.
    + unfold not_marked_lib in nm.
      destruct nm; rw in_app_iff; sp.
    + unfold not_marked_lib in nm.
      destruct nm; rw in_app_iff; sp.
  - unfold not_marked_lib in nm.
    destruct nm; rw in_app_iff; sp.
Qed.
*)

Lemma reduces_to_preserves {o} :
  forall lib (t u : @NTerm o),
    wf_term t
    -> reduces_to lib t u
    -> (subvars (free_vars u) (free_vars t)
        # subset (get_utokens_lib lib u) (get_utokens_lib lib t)
        # wf_term u).
Proof.
  introv wf r.
  unfold reduces_to in r; exrepnd.
  revert dependent u.
  revert dependent t.
  induction k; introv wf comp.
  - rw @reduces_in_atmost_k_steps_0 in comp; subst; dands; auto.
  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    allrw @wf_term_eq.
    pose proof (compute_step_preserves lib t u0 wf comp1) as h; repnd.
    apply IHk in comp0; repnd; eauto 3 with slow.
    dands; eauto 3 with slow.
    apply compute_step_preserves_utokens in comp1; auto.
Qed.

Lemma reduces_to_preserves_wf {o} :
  forall lib (t u : @NTerm o),
    reduces_to lib t u
    -> wf_term t
    -> wf_term u.
Proof.
  introv r w; apply reduces_to_preserves in r; sp.
Qed.

Lemma lsubst_aux_trim_cl_sub {o} :
  forall (t : @NTerm o) (sub : @Sub o),
    cl_sub sub
    -> lsubst_aux t sub = lsubst_aux t (sub_keep_first sub (free_vars t)).
Proof.
  introv cl.
  apply lsubst_aux_trim.
  introv i.
  rw @cl_sub_eq2 in cl.
  apply cl in i; rw i; auto.
Qed.

Lemma sub_find_bot_sub_some_if_not_in {o} :
  forall v vs,
    !LIn v vs
    -> @sub_find o (bot_sub vs) v = None.
Proof.
  induction vs; introv i; allsimpl; cpx.
  allrw not_over_or; repnd.
  boolvar; sp.
Qed.

Lemma implies_subvars_remove_nvars :
  forall l vs1 vs2,
    subvars vs1 vs2
    -> subvars (remove_nvars l vs1) (remove_nvars l vs2).
Proof.
  introv sv.
  allrw subvars_prop.
  introv i; allrw in_remove_nvars; repnd; dands; auto.
Qed.

Lemma remove_nvars_twice :
  forall l vs,
    remove_nvars l (remove_nvars l vs)
    = remove_nvars l vs.
Proof.
  induction vs; simpl.
  - allrw remove_nvars_nil_r; auto.
  - allrw remove_nvars_cons_r; boolvar; auto.
    allrw remove_nvars_cons_r; boolvar; tcsp.
    f_equal; sp.
Qed.

(*
Lemma eq_lsubst_aux_bot_sub {o} :
  forall (t : @NTerm o) x m vs1 vs2 vs,
    subvars vs1 vs2
    -> (forall v, LIn v (free_vars t) -> LIn v vs2 -> LIn v vs1)
    -> lsubst_aux t (sub_filter ((x, mk_marker m) :: bot_sub vs2) vs)
       = lsubst_aux t (sub_filter ((x, mk_marker m) :: bot_sub vs1) vs).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv sv cl; allsimpl.

  - Case "vterm".
    boolvar; auto; allrw @sub_filter_bot_sub; simpl; boolvar; auto;
    destruct (in_deq NVar deq_nvar v (remove_nvars vs vs1)) as [i|i].
    + rw (@sub_find_bot_sub_some_if_in o v (remove_nvars vs vs1)); auto.
      rw in_remove_nvars in i; repnd.
      rw subvars_prop in sv.
      applydup sv in i0.
      rw (@sub_find_bot_sub_some_if_in o v (remove_nvars vs vs2)); auto.
      rw in_remove_nvars; sp.
    + rw (@sub_find_bot_sub_some_if_not_in o v (remove_nvars vs vs1)); auto.
      destruct (in_deq NVar deq_nvar v (remove_nvars vs vs2)) as [j|j];
        allrw in_remove_nvars; repnd.
      * apply cl in j0; sp; destruct i; sp.
      * rw (@sub_find_bot_sub_some_if_not_in o v (remove_nvars vs vs2)); auto.
        rw in_remove_nvars; sp.
    + rw (@sub_find_bot_sub_some_if_in o v (remove_nvars vs vs1)); auto.
      rw in_remove_nvars in i; repnd.
      rw subvars_prop in sv.
      applydup sv in i0.
      rw (@sub_find_bot_sub_some_if_in o v (remove_nvars vs vs2)); auto.
      rw in_remove_nvars; sp.
    + rw (@sub_find_bot_sub_some_if_not_in o v (remove_nvars vs vs1)); auto.
      destruct (in_deq NVar deq_nvar v (remove_nvars vs vs2)) as [j|j];
        allrw in_remove_nvars; repnd.
      * apply cl in j0; sp; destruct i; sp.
      * rw (@sub_find_bot_sub_some_if_not_in o v (remove_nvars vs vs2)); auto.
        rw in_remove_nvars; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; intros b i; destruct b as [l t]; allsimpl.
    boolvar; f_equal; allsimpl; boolvar; tcsp;
    allrw @sub_filter_bot_sub.
    + pose proof (ind t l i x m (remove_nvars l vs1) (remove_nvars l vs2) vs) as h;
      boolvar; tcsp.
      repeat (autodimp h hyp).
      * apply implies_subvars_remove_nvars; auto.
      * introv j k.
        allrw in_remove_nvars; repnd; dands; auto.
        apply cl; auto.
        rw lin_flat_map; eexists; dands; eauto.
        simpl; rw in_remove_nvars; dands; auto.
      * allrw @sub_filter_bot_sub.
        rw (remove_nvars_comm l vs vs2).
        rw (remove_nvars_comm l vs vs1); auto.
    + pose proof (ind t l i x m (remove_nvars l vs1) (remove_nvars l vs2) (l ++ vs)) as h;
      boolvar; tcsp.
      repeat (autodimp h hyp).
      * apply implies_subvars_remove_nvars; auto.
      * introv j k.
        allrw in_remove_nvars; repnd; dands; auto.
        apply cl; auto.
        rw lin_flat_map; eexists; dands; eauto.
        simpl; rw in_remove_nvars; dands; auto.
      * allrw @sub_filter_bot_sub.
        allrw <- remove_nvars_app_l.
        repeat (rw (remove_nvars_comm l vs) in h).
        rw (remove_nvars_comm l vs vs1); auto.
        rw (remove_nvars_comm l vs vs2); auto.
        allrw remove_nvars_twice; auto.
      * provefalse.
        allrw in_app_iff; allrw not_over_or; sp.
    + pose proof (ind t l i x m (remove_nvars l vs1) (remove_nvars l vs2) vs) as h;
      boolvar; tcsp.
      repeat (autodimp h hyp).
      * apply implies_subvars_remove_nvars; auto.
      * introv j k.
        allrw in_remove_nvars; repnd; dands; auto.
        apply cl; auto.
        rw lin_flat_map; eexists; dands; eauto.
        simpl; rw in_remove_nvars; dands; auto.
      * allrw @sub_filter_bot_sub.
        allrw <- remove_nvars_app_l.
        repeat (rw (remove_nvars_comm l vs) in h).
        rw (remove_nvars_comm l vs vs1); auto.
        rw (remove_nvars_comm l vs vs2); auto.
Qed.

Lemma eq_lsubst_aux_bot_sub2 {o} :
  forall (t u : @NTerm o) x m,
    subvars (free_vars t) (free_vars u)
    -> lsubst_aux t ((x, mk_marker m) :: bot_sub_fv u)
       = lsubst_aux t ((x, mk_marker m) :: bot_sub_fv t).
Proof.
  introv sv.
  pose proof (eq_lsubst_aux_bot_sub t x m (free_vars t) (free_vars u) [] sv) as h.
  allrw @sub_filter_nil_r.
  apply h; sp.
Qed.

Lemma computes_to_marker_lsubst_aux_bot_sub {o} :
  forall lib (t : @NTerm o) m x,
    wf_term t
    -> not_marked_lib m t lib
    -> computes_to_marker
         lib
         (lsubst_aux t ((x, mk_marker m) :: bot_sub_fv t))
         m
    -> reduces_to lib t (mk_var x).
Proof.
  introv wf ffa comp.
  unfold computes_to_marker in comp.
  destruct comp as [comp ism].
  unfold reduces_to in comp; exrepnd.
  revert dependent t.
  induction k; introv wf ffa c.

  - rw @reduces_in_atmost_k_steps_0 in c.
    destruct t; allsimpl; boolvar; auto; ginv.

    + apply reduces_to_symm.

    + destruct o0; ginv.
      destruct l; ginv.
      allsimpl.
      inversion c; subst.
      provefalse.
      destruct ffa; simpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in c; exrepnd.
    apply compute_step_to_atom2 in c1; auto;
    [| unfold converges_to_value_like; exists (@mk_marker o m); dands;
       [exists k; auto|unfold is_value_like; simpl; auto]
    ].
    exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u (lsubst_aux w ((x, mk_marker m) :: bot_sub_fv t))
                  c1 k (mk_marker m) c0) as r; exrepnd.
    apply alpha_eq_marker in r0; subst.

    pose proof (reduces_to_preserves lib t w) as sv; autodimp sv hyp; repnd.
    autodimp sv hyp.

    pose proof (IHk w) as h; repeat (autodimp h hyp);
    [ eapply not_marked_if_subset; eauto
    | idtac
    | apply (reduces_to_trans lib _ w); auto].

    assert (lsubst_aux w ((x, mk_marker m) :: bot_sub_fv t)
            = lsubst_aux w ((x, mk_marker m) :: bot_sub_fv w))
           as e; [|rw <- e; auto].
    apply eq_lsubst_aux_bot_sub2; auto.
Qed.
*)

Lemma wf_sub_cons_iff {o} :
  forall v (t : @NTerm o) sub,
    wf_sub ((v,t) :: sub) <=> (wf_term t # wf_sub sub).
Proof.
  introv.
  unfold wf_sub, sub_range_sat; simpl; split; introv k; repnd; dands.
  - pose proof (k v t) as h; autodimp h hyp.
    apply wf_term_eq; auto.
  - introv i.
    eapply k; eauto.
  - introv i; dorn i; cpx.
    + apply nt_wf_eq; auto.
    + eapply k; eauto.
Qed.

Lemma wf_sub_bot_sub_fv {o} :
  forall (t : @NTerm o), wf_sub (bot_sub_fv t).
Proof.
  unfold bot_sub_fv; eauto with slow.
Qed.
Hint Resolve wf_sub_bot_sub_fv.

Lemma isprogram_marker {o} :
  forall m, @isprogram o (mk_marker m).
Proof.
  introv; repeat constructor; simpl; sp.
Qed.
Hint Resolve isprogram_marker : slow.

Lemma in_bot_sub {o} :
  forall v (u : @NTerm o) vs,
    LIn (v, u) (bot_sub vs)
    -> (LIn v vs # u = mk_bot).
Proof.
  induction vs; introv i; allsimpl; tcsp.
  dorn i; cpx.
Qed.

Lemma in_bot_sub_fv {o} :
  forall v (u t : @NTerm o),
    LIn (v, u) (bot_sub_fv t)
    -> (LIn v (free_vars t) # u = mk_bot).
Proof.
  introv i.
  unfold bot_sub_fv in i.
  apply in_bot_sub; auto.
Qed.

Lemma computes_to_marker_refl {o} :
  forall (lib : @library o) m,
    is_mrk lib m
    -> computes_to_marker lib (mk_marker m) m.
Proof.
  introv ism.
  unfold computes_to_marker; dands; auto.
  apply reduces_to_symm.
Qed.

Lemma sub_free_vars_bot_sub {o} :
  forall vs, @sub_free_vars o (bot_sub vs) = [].
Proof.
  induction vs; simpl; auto.
Qed.

Lemma sub_free_vars_bot_sub_fv {o} :
  forall t : @NTerm o, sub_free_vars (bot_sub_fv t) = [].
Proof.
  introv; unfold bot_sub_fv.
  rw @sub_free_vars_bot_sub; auto.
Qed.

(*
Lemma computes_to_marker_lsubst_bot_sub {o} :
  forall lib (t : @NTerm o) m x,
    wf_term t
    -> not_marked_lib m t lib
    -> computes_to_marker
         lib
         (lsubst t ((x, mk_marker m) :: bot_sub_fv t))
         m
    -> reduces_to lib t (mk_var x).
Proof.
  introv wf nm comp.
  unfold lsubst in comp.
  allsimpl.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_bot_sub_fv in comp; boolvar;
  try (complete (provefalse; sp)).
  apply computes_to_marker_lsubst_aux_bot_sub in comp; auto.
Qed.

Lemma exists_marker {o} :
  forall (lib : @library o) (t : @NTerm o),
    {m : marker & not_marked_lib m t lib}.
Proof.
  introv.
  unfold not_marked_lib.
  remember (get_markers t ++ get_markers_lib lib) as ms; clear Heqms.

  exists (String.append "x" (append_string_list ms)).
  remember ("x") as extra.
  assert (0 < String.length extra) as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction ms; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  rw not_over_or; dands; auto;[|apply IHms;rw string_length_append; omega].

  intro k.
  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list ms))) as e by (rw <- k; auto).
  allrw string_length_append.
  omega.
Qed.
*)
