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


Require Export substitution3.


Fixpoint sosub2_aux {o} (sub : @SOSub o) (t : SOTerm) : NTerm :=
  match t with
  | sovar var ts =>
    match sosub_find sub (var,length ts) with
    | Some (sosk vs u) => lsubst u (combine vs (map (sosub2_aux sub) ts))
    | None => apply_list (mk_var var) (map (sosub2_aux sub) ts)
    end
  | soseq s => sterm s
  | soterm opid bts => oterm opid (map (sosub2_b_aux sub) bts)
  end
with sosub2_b_aux {o} (sub : @SOSub o) (bt : SOBTerm) : BTerm :=
       match bt with
       | sobterm vs t =>
         bterm vs (sosub2_aux (sosub_filter sub (vars2sovars vs)) t)
       end.

Definition sosub2 {o} (sub : @SOSub o) (t : SOTerm) : NTerm :=
  let fvars_s := free_vars_sosub sub in
  if dec_disjointv (fo_bound_vars t) fvars_s
  then sosub2_aux sub t
  else sosub2_aux sub (fo_change_bvars_alpha (fvars_s ++ all_fo_vars t) [] t).

Lemma disjoint_flat_map_left_implies {o} :
  forall {A} (ts : list (@SOTerm o)) f t (l : list A),
    disjoint (flat_map f ts) l
    -> LIn t ts
    -> disjoint (f t) l.
Proof.
  introv disj i j k; apply disj in k; auto.
  apply lin_flat_map.
  eexists; dands; eauto.
Qed.
Hint Resolve disjoint_flat_map_left_implies : slow.

Hint Resolve subvars_bound_vars_in_sosub_bound_vars_sosub : slow.
Hint Resolve subvars_disjoint_l : slow.
Hint Resolve subvars_disjoint_r : slow.

Lemma disjoint_flat_map_fo_bound_vars_bterm_left_implies {o} :
  forall (bs : list (@SOBTerm o)) l t (k : list NVar),
    disjoint (flat_map fo_bound_vars_bterm bs) k
    -> LIn (sobterm l t) bs
    -> disjoint (fo_bound_vars t) k.
Proof.
  introv disj i j w; apply disj in w; auto.
  apply lin_flat_map.
  eexists; dands; eauto.
  simpl.
  allrw in_app_iff; tcsp.
Qed.
Hint Resolve disjoint_flat_map_fo_bound_vars_bterm_left_implies : slow.

Lemma subvars_free_vars_sosub_filter {o} :
  forall (sub : @SOSub o) vs,
    subvars (free_vars_sosub (sosub_filter sub vs)) (free_vars_sosub sub).
Proof.
  introv.
  apply subvars_flat_map; introv i; repnd; simpl.
  destruct x; simpl.
  apply in_sosub_filter in i; repnd.
  eapply implies_subvars_flat_map_r;[eauto|]; tcsp.
Qed.
Hint Resolve subvars_free_vars_sosub_filter : slow.

Hint Resolve subvars_bound_vars_sosub_filter : slow.

Lemma subvars_flat_map_all_fo_vars_bterm {o} :
  forall l (t : @SOTerm o) bs,
    LIn (sobterm l t) bs
    -> subvars (all_fo_vars t) (flat_map all_fo_vars_bterm bs).
Proof.
  introv i.
  eapply implies_subvars_flat_map_r; eauto.
  simpl; eauto 3 with slow.
Qed.
Hint Resolve subvars_flat_map_all_fo_vars_bterm : slow.

Hint Resolve eqvars_disjoint : slow.
Hint Resolve eqvars_disjoint_r : slow.

Lemma alphaeq_sk_implies_eqvars_free_vars_sk {o} :
  forall (sk1 sk2 : @sosub_kind o),
    alphaeq_sk sk1 sk2
    -> eqvars (free_vars_sk sk1) (free_vars_sk sk2).
Proof.
  introv aeq; destruct sk1, sk2; simpl in *.
  unfold alphaeq_sk in aeq; simpl in *.
  apply alphaeqbt_eq in aeq.
  apply alphaeqbt_preserves_fvars in aeq; simpl in aeq; auto.
Qed.
Hint Resolve  alphaeq_sk_implies_eqvars_free_vars_sk : slow.

Lemma alphaeq_sosub_implies_eqvars_free_vars_sosub {o} :
  forall (s1 s2 : @SOSub o),
    alphaeq_sosub s1 s2
    -> eqvars (free_vars_sosub s1) (free_vars_sosub s2).
Proof.
  introv aeq.
  induction aeq; simpl; auto.
  apply eqvars_app; eauto 3 with slow.
Qed.
Hint Resolve alphaeq_sosub_implies_eqvars_free_vars_sosub : slow.

Lemma eqvars_implies_subvars :
  forall s1 s2, eqvars s1 s2 -> subvars s1 s2.
Proof.
  introv eqv.
  apply eqvars_is_eqset in eqv.
  apply subvars_eq.
  introv i; apply eqv in i; auto.
Qed.
Hint Resolve eqvars_implies_subvars : slow.

Lemma free_vars_sosub_subvars_allvars_range_sosub {o} :
  forall (s : @SOSub o),
    subvars (free_vars_sosub s) (allvars_range_sosub s).
Proof.
  introv.
  eapply subvars_eqvars_r;[|apply eqvars_sym;apply eqvars_allvars_range_sosub].
  eauto 3 with slow.
Qed.
Hint Resolve free_vars_sosub_subvars_allvars_range_sosub : slow.

Lemma implies_alphaeq_sub_range_combine {o} :
  forall l1 l2 (ts1 ts2 : list (@NTerm o)),
    length l1 = length l2
    -> length l1 = length ts1
    -> length l2 = length ts2
    -> (forall a b, LIn (a,b) (combine ts1 ts2) -> alpha_eq a b)
    -> alphaeq_sub_range (combine l1 ts1) (combine l2 ts2).
Proof.
  induction l1; introv len1 len2 len3 imp; simpl in *; ginv;
    destruct l2, ts1, ts2; simpl in *; ginv; cpx.
  constructor; tcsp.
  apply alphaeq_eq; apply imp; tcsp.
Qed.

Lemma sosub_find_none_if_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o) (v : sovar_sig),
    alphaeq_sosub sub1 sub2
    -> sosub_find sub1 v = None
    -> sosub_find sub2 v = None.
Proof.
  introv aeq.
  induction aeq; introv f; simpl in *; auto.
  destruct sk1, sk2, v, v0, n1; simpl in *; boolvar; ginv.
  autodimp IHaeq hyp; auto.
  apply alphaeq_sk_eq_length in a; simpl in *; rewrite a in *; tcsp.
Qed.

Lemma implies_alphaeq_sosub_sosub_filter {o} :
  forall (s1 s2 : @SOSub o) l,
    alphaeq_sosub s1 s2
    -> alphaeq_sosub (sosub_filter s1 l) (sosub_filter s2 l).
Proof.
  introv aeq.
  induction aeq; simpl; auto.
  destruct sk1, sk2; simpl.
  applydup @alphaeq_sk_eq_length in a as eqlen; simpl in eqlen; rewrite eqlen.
  boolvar; auto.
Qed.
Hint Resolve implies_alphaeq_sosub_sosub_filter : slow.

Lemma alpha_eq_sosub2_aub_1 {o} :
  forall (t : @SOTerm o) s1 s2,
    alphaeq_sosub s1 s2
    -> alpha_eq (sosub2_aux s1 t) (sosub2_aux s2 t).
Proof.
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv aeq; simpl in *; auto.

  - Case "sovar".

    allrw disjoint_cons_l; repnd.
    remember (sosub_find s1 (v, length ts)) as sf; symmetry in Heqsf; destruct sf.

    + destruct s; simpl.
      pose proof (sosub_find_some_if_alphaeq_sosub s1 s2 (v,length ts) (sosk l n)) as q.
      repeat (autodimp q hyp); exrepnd.
      allrw.
      destruct sk'.

      applydup @sosub_find_some in Heqsf; repnd.
      applydup @sosub_find_some in q0; repnd.

      apply alphaeq_sk_iff_alphaeq_bterm2 in q1.
      apply (lsubst_alpha_congr4 l l0); auto;
        try (complete (rewrite dom_sub_combine; autorewrite with list; auto)).

      apply implies_alphaeq_sub_range_combine; autorewrite with list; auto; try congruence.

      introv i.
      rw <- @map_combine in i.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      apply ind; auto; eauto 3 with slow.

    + pose proof (sosub_find_none_if_alphaeq_sosub s1 s2 (v,length ts)) as q.
      repeat (autodimp q hyp); rewrite q.

      apply alphaeq_eq; apply alphaeq_apply_list; eauto 2 with slow.
      apply bin_rel_nterm_if_combine; autorewrite with list; auto.
      introv i.
      allrw <- @map_combine.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      apply ind; eauto 3 with slow.

  - Case "soterm".

    apply alpha_eq_oterm_combine; autorewrite with list; dands; auto.
    introv i.
    allrw <- @map_combine.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a; simpl.
    apply alpha_eq_bterm_congr.
    eapply ind; eauto; eauto 4 with slow.
Qed.
Hint Resolve alpha_eq_sosub2_aub_1 : slow.

Lemma alpha_eq_sosub_aux_sosub2_aub_1 {o} :
  forall (t : @SOTerm o) s,
    disjoint (free_vars_sosub s) (bound_vars_sosub s)
    -> disjoint (all_fo_vars t) (bound_vars_sosub s)
    -> alpha_eq (sosub_aux s t) (sosub2_aux s t).
Proof.
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv disj2 disj3; simpl in *; auto.

  - Case "sovar".

    allrw disjoint_cons_l; repnd.
    remember (sosub_find s (v, length ts)) as sf; symmetry in Heqsf; destruct sf.

    + destruct s0; simpl.
      applydup @sosub_find_some in Heqsf; repnd.

      assert (alpha_eq
                (lsubst n (combine l (map (sosub_aux s) ts)))
                (lsubst n (combine l (map (sosub2_aux s) ts)))) as aeq.

      * apply lsubst_alpha_congr; autorewrite with list; auto.
        apply bin_rel_nterm_if_combine; autorewrite with list; auto.
        introv i.
        allrw <- @map_combine.
        apply in_map_iff in i; exrepnd; ginv.
        apply in_combine_same in i1; repnd; subst.
        apply ind; eauto 3 with slow.

      * eapply alpha_eq_trans;[|exact aeq];clear aeq.
        pose proof (unfold_lsubst (combine l (map (sosub_aux s) ts)) n) as q.
        exrepnd.
        rewrite q0; clear q0.
        rewrite sub_free_vars_combine in q2; autorewrite with list; auto.
        apply lsubst_aux_alpha_congr; autorewrite with list; auto; eauto 3 with slow;
          try (complete (unfold bin_rel_nterm, binrel_list; simpl; autorewrite with list; tcsp)).

        rewrite flat_map_map; unfold compose.
        apply disjoint_sym.
        eapply disjoint_bound_vars_prop1; eauto; eauto 5 with slow.

    + apply alphaeq_eq; apply alphaeq_apply_list; eauto 3 with slow.
      apply bin_rel_nterm_if_combine; autorewrite with list; auto.
      introv i.
      allrw <- @map_combine.
      apply in_map_iff in i; exrepnd; ginv.
      apply in_combine_same in i1; repnd; subst.
      apply ind; eauto 3 with slow.

  - Case "soterm".

    apply alpha_eq_oterm_combine; autorewrite with list; dands; auto.
    introv i.
    allrw <- @map_combine.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a; simpl.
    apply alpha_eq_bterm_congr.
    eapply ind; eauto 5 with slow.
Qed.

Lemma sosub_aeq_sosub2 {o} :
  forall (t : @SOTerm o) (s : @SOSub o),
    alpha_eq (sosub s t) (sosub2 s t).
Proof.
  introv.
  unfold sosub, sosub2; boolvar.

  - allrw disjoint_app_l; repnd.
    apply alpha_eq_sosub_aux_sosub2_aub_1; auto.

  - pose proof (sosub_change_bvars_alpha_spec (allvars_range_sosub s ++ all_fo_vars t) s) as q.
    simpl in q; repnd.
    remember (sosub_change_bvars_alpha (allvars_range_sosub s ++ all_fo_vars t) s) as s'.
    clear Heqs'.
    allrw disjoint_app_l; repnd.

    eapply alpha_eq_trans;
      [apply alpha_eq_sosub_aux_sosub2_aub_1; auto|];
      eauto 3 with slow.

    { eapply subvars_disjoint_l;[|exact q1].
      apply alphaeq_sosub_implies_eqvars_free_vars_sosub in q.
      apply eqvars_sym in q.
      apply eqvars_implies_subvars in q.
      eapply subvars_trans;[exact q|]; eauto 3 with slow. }

  - pose proof (fo_change_bvars_alpha_spec (free_vars_sosub s ++ all_fo_vars t) t) as q.
    simpl in q; repnd.
    remember (fo_change_bvars_alpha (free_vars_sosub s ++ all_fo_vars t) [] t) as u.
    clear Hequ.
    allrw disjoint_app_l; repnd.
    apply alpha_eq_sosub_aux_sosub2_aub_1; auto.

  - pose proof (fo_change_bvars_alpha_spec (free_vars_sosub s ++ all_fo_vars t) t) as q.
    simpl in q; repnd.
    remember (fo_change_bvars_alpha (free_vars_sosub s ++ all_fo_vars t) [] t) as u.
    clear Hequ.
    allrw disjoint_app_l; repnd.

    pose proof (sosub_change_bvars_alpha_spec (allvars_range_sosub s ++ all_fo_vars u) s) as h.
    simpl in h; repnd.
    remember (sosub_change_bvars_alpha (allvars_range_sosub s ++ all_fo_vars u) s) as s'.
    clear Heqs'.
    allrw disjoint_app_l; repnd.

    eapply alpha_eq_trans;
      [apply alpha_eq_sosub_aux_sosub2_aub_1; auto|];
      eauto 3 with slow.

    { eapply subvars_disjoint_l;[|exact h1].
      apply alphaeq_sosub_implies_eqvars_free_vars_sosub in h.
      apply eqvars_sym in h.
      apply eqvars_implies_subvars in h.
      eapply subvars_trans;[exact h|]; eauto 3 with slow. }
Qed.
