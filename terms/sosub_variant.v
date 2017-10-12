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


Require Export sovar_alpha.


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
  let bvars_s := bound_vars_sosub sub in
  let bvars_t := fo_bound_vars t in
  if dec_disjointv bvars_t fvars_s
  then sosub2_aux sub t
  else let t' := fo_change_bvars_alpha (fvars_s ++ all_fo_vars t) [] t
       in sosub2_aux sub t'.

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

Lemma alpha_eq_sosub_aux_sosub2_aub_1 {o} :
  forall (t : @SOTerm o) s,
    disjoint (fo_bound_vars t) (free_vars_sosub s)
    -> disjoint (free_vars_sosub s) (bound_vars_sosub s)
    -> disjoint (all_fo_vars t) (bound_vars_sosub s)
    -> alpha_eq (sosub_aux s t) (sosub2_aux s t).
Proof.
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv disj1 disj2 disj3; simpl in *; auto.

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

  -
Qed.
