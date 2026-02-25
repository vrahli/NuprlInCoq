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


Require Export computation_seq.
Require Export continuity_defs.
(*Require Export list.  (* Why?? *)*)


Inductive differ {o} (b : nat) : @NTerm o -> @NTerm o -> Type :=
| differ_force_int :
    forall t1 t2 e v,
      !LIn v (free_vars e)
      -> differ b t1 t2
      -> differ b (force_int_bound v b t1 e) (force_int t2)
| differ_var :
    forall v, differ b (mk_var v) (mk_var v)
| differ_sterm :
    forall f, differ b (sterm f) (sterm f)
| differ_oterm :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> differ_b b b1 b2)
      -> differ b (oterm op bs1) (oterm op bs2)
with differ_b {o} (b : nat) : @BTerm o -> @BTerm o -> Type :=
     | differ_bterm :
         forall vs t1 t2,
           differ b t1 t2
           -> differ_b b (bterm vs t1) (bterm vs t2).
Hint Constructors differ differ_b.

(*
Lemma free_vars_differ {o} :
  forall b (t1 t2 : @NTerm o),
    differ b t1 t2
    -> free_vars t1 = free_vars t2.
Proof.
  nterm_ind t1 as [x|op bs ind] Case; introv d.

  - Case "vterm".
    inversion d; subst.
    allsimpl; auto.

  - Case "oterm".
    inversion d as [|?|? ? ? len imp]; subst.

    + allsimpl.
      allrw remove_nvars_nil_l.
      allrw app_nil_r.
      allrw remove_nvars_cons_r; allsimpl.
      boolvar; tcsp; allrw not_over_or; tcsp.
      allrw remove_nvars_nil_r.
      allrw app_nil_r.
      apply (ind t1 []); auto.

    + allsimpl.
      apply eq_flat_maps_diff; auto.
      introv i.
      applydup imp in i.
      destruct t1 as [l1 t1].
      destruct t2 as [l2 t2].
      simpl.
      inversion i0 as [? ? ? d1]; subst.
      applydup in_combine in i; repnd.
      eapply ind in d1; eauto.
      rw d1; auto.
Qed.
*)

(*
Lemma bound_vars_differ {o} :
  forall b (t1 t2 : @NTerm o),
    differ b t1 t2
    -> eqvars (bound_vars t1) (bound_vars t2).
Proof.
  nterm_ind t1 as [x|op bs ind] Case; introv d.

  - Case "vterm".
    inversion d; subst; allsimpl; auto.

  - Case "oterm".
    inversion d as [|?|? ? ? len imp]; subst.

    + allsimpl.
      apply eqvars_app; auto.

      * apply (ind t1 []); auto.

      * rw eqvars_prop; simpl; introv; split; sp.

    + allsimpl.
      apply implies_eqvars_flat_map_diff; auto.
      introv i.
      applydup imp in i.
      destruct x as [l1 t1].
      destruct y as [l2 t2].
      simpl.
      inversion i0 as [? ? ? d1]; subst.
      applydup in_combine in i; repnd.
      eapply ind in d1; eauto.
      apply eqvars_app; auto.
Qed.
*)

Inductive differ_subs {o} b : @Sub o -> @Sub o -> Type :=
| dsub_nil : differ_subs b [] []
| dsub_cons :
    forall v t1 t2 sub1 sub2,
      differ b t1 t2
      -> differ_subs b sub1 sub2
      -> differ_subs b ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors differ_subs.

(*
Lemma free_vars_differ_subs {o} :
  forall b (sub1 sub2 : @Sub o),
    differ_subs b sub1 sub2
    -> sub_free_vars sub1 = sub_free_vars sub2.
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; tcsp;
  try (complete (inversion d)).

  destruct a, p.
  inversion d; subst.
  apply app_if; auto.
  eapply free_vars_differ; eauto.
Qed.
*)

Lemma differ_subs_sub_find_some {o} :
  forall b (sub1 sub2 : @Sub o) v t,
    differ_subs b sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # differ b t u}.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma differ_subs_sub_find_none {o} :
  forall b (sub1 sub2 : @Sub o) v,
    differ_subs b sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma differ_subs_filter {o} :
  forall b (sub1 sub2 : @Sub o) l,
    differ_subs b sub1 sub2
    -> differ_subs b (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.

Lemma differ_lsubst_aux {o} :
  forall b (t1 t2 : @NTerm o) sub1 sub2,
    differ b t1 t2
    -> differ_subs b sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> differ b (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case;
  introv dt ds disj1 disj2; allsimpl.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ_subs_sub_find_some b sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ_subs_sub_find_none b sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "sterm".
    inversion dt; subst; clear dt; allsimpl; auto.

  - Case "oterm".
    inversion dt as [|?|?|? ? ? len imp]; subst; allsimpl.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      rw @sub_find_sub_filter; tcsp.
      fold_terms.
      apply differ_force_int.

      * pose proof (free_vars_lsubst_aux_subvars e (sub_filter sub1 [v])) as sv.
        rw subvars_prop in sv; intro k; apply sv in k; clear sv.
        rw <- @dom_sub_sub_filter in k.
        rw in_app_iff in k.
        allrw in_remove_nvars; allsimpl.
        dorn k; repnd; tcsp.
        pose proof (subvars_sub_free_vars_sub_filter sub1 [v]) as sv.
        rw subvars_prop in sv; apply sv in k; clear sv; tcsp.

      * apply (ind t1 []); auto.

    + apply differ_oterm; allrw map_length; auto.

      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      applydup imp in i1.
      destruct a0 as [l1 t1].
      destruct a as [l2 t2].
      applydup in_combine in i1; repnd.
      allsimpl.
      inversion i0 as [? ? ? d]; subst; clear i0.
      constructor.
      apply (ind t1 l2); auto.

      * apply differ_subs_filter; auto.

      * pose proof (subvars_sub_free_vars_sub_filter sub1 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.

      * pose proof (subvars_sub_free_vars_sub_filter sub2 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.
Qed.

Lemma differ_refl {o} :
  forall b (t : @NTerm o),
    differ b t t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; auto.

  Case "oterm".
  apply differ_oterm; auto.
  introv i.
  rw in_combine_same in i; repnd; subst.
  destruct b2 as [l t].
  constructor.
  eapply ind; eauto.
Qed.
Hint Resolve differ_refl : slow.

Lemma differ_subs_refl {o} :
  forall b (sub : @Sub o),
    differ_subs b sub sub.
Proof.
  induction sub; auto.
  destruct a.
  constructor; eauto with slow.
Qed.
Hint Resolve differ_subs_refl : slow.

(*
Lemma differ_change_bvars_alpha {o} :
  forall b (t1 t2 : @NTerm o) vs,
    differ b t1 t2
    -> differ
         b
         (change_bvars_alpha vs t1)
         (change_bvars_alpha vs t2).
Proof.
  nterm_ind t1 as [v|op bs ind] Case; introv d; allsimpl.

  - Case "vterm".
    inversion d; subst; allsimpl; auto.

  - Case "oterm".
    inversion d as [|?|? ? ? len imp]; subst; allsimpl.

    + boolvar; allsimpl;
      allrw @var_ren_nil_l;
      allrw @lsubst_aux_nil;
      allunfold @all_vars; allsimpl;
      allrw remove_nvars_nil_l; allrw app_nil_r; allsimpl;
      allrw remove_nvars_eq; allsimpl;
      boolvar; allsimpl; auto;
      allrw not_over_or; repnd; tcsp.

      apply differ_force_int.
      apply (ind t1 []); auto.

    + apply differ_oterm; allrw map_length; auto.
      introv i.
      allrw <- @map_combine.
      allrw in_map_iff; exrepnd; cpx; allsimpl.
      destruct a0 as [l1 t1].
      destruct a as [l2 t2].
      simpl.
      applydup imp in i1.
      inversion i0 as [? ? ? d1]; subst; clear i0.
      applydup in_combine in i1; repnd.
      pose proof (ind t1 l2) as h; repeat (autodimp h hyp).
      pose proof (h t2 vs) as k; autodimp k hyp.
      applydup @free_vars_differ in k.
      applydup @bound_vars_differ in k.

      assert (eqvars
                (vs ++ all_vars (change_bvars_alpha vs t1))
                (vs ++ all_vars (change_bvars_alpha vs t2))) as eqv.
      { apply eqvars_app; auto.
        unfold all_vars.
        apply eqvars_app; auto.
        rw k0; auto. }

      assert (fresh_distinct_vars
                (length l2)
                (vs ++ all_vars (change_bvars_alpha vs t1))
              = fresh_distinct_vars
                  (length l2)
                  (vs ++ all_vars (change_bvars_alpha vs t2))) as e.
      { erewrite fresh_distinct_vars_if_eqvars; eauto. }
      rw e.
      constructor.

      apply differ_lsubst_aux; eauto with slow.

      * gen_fresh.
        rw @sub_free_vars_var_ren; auto.
        apply disjoint_sym.
        eapply subvars_disjoint_r;[|eauto].
        unfold all_vars.
        apply subvars_app_weak_r.
        apply subvars_app_weak_r.
        apply eqvars_sym in k1.
        eapply subvars_eqvars;[|eauto]; auto.

      * gen_fresh.
        rw @sub_free_vars_var_ren; auto.
        apply disjoint_sym.
        eapply subvars_disjoint_r;[|eauto].
        unfold all_vars.
        apply subvars_app_weak_r.
        apply subvars_app_weak_r.
        apply eqvars_sym in k1.
        eapply subvars_eqvars;[|eauto]; auto.
Qed.
*)

Definition differ_alpha {o} (b : nat) (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
      & alpha_eq t1 u1
      # alpha_eq t2 u2
      # differ b u1 u2}}.

Definition differ_implies_differ_alpha {o} :
  forall (b : nat) (t1 t2 : @NTerm o),
    differ b t1 t2 -> differ_alpha b t1 t2.
Proof.
  introv d.
  exists t1 t2; auto.
Qed.
Hint Resolve differ_implies_differ_alpha : slow.

Definition differ_bterms {o} b (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ_b b) bs1 bs2.

Lemma differ_change_bound_vars {o} :
  forall b vs (t1 t2 : @NTerm o),
    differ b t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
           & differ b u1 u2
           # alpha_eq t1 u1
           # alpha_eq t2 u2
           # disjoint (bound_vars u1) vs
           # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case; introv d.

  - Case "vterm".
    inversion d; subst.
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto with slow.

  - Case "sterm".
    inversion d; subst; clear d.
    exists (sterm f) (sterm f); dands; simpl; auto.

  - Case "oterm".
    inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.

    + pose proof (ex_fresh_var (vs ++ free_vars e)) as h; exrepnd.
      allrw in_app_iff; allrw not_over_or; repnd.
      pose proof (ind t1 []) as h; repeat (autodimp h hyp).
      pose proof (h t0 d1) as k; clear h; exrepnd.
      pose proof (change_bvars_alpha_spec e vs) as k; simpl in k; repnd.
      remember (change_bvars_alpha vs e) as e'; clear Heqe'.

      allrw disjoint_cons_l; repnd.

      fold_terms.

      applydup @alphaeq_preserves_free_vars in k as k'.

      exists
        (mk_cbv u1 v0 (less_bound b (mk_var v0) e'))
        (force_int u2); dands; auto.

      * apply differ_force_int; auto.
        rw <- k'; auto.

      * apply alpha_eq_force_int_bound; auto.
        rw <- k'; auto.

      * apply alpha_eq_force_int; auto.

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; rw disjoint_cons_l; dands; eauto with slow.

      * simpl; allrw app_nil_r; eauto with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
                  & alpha_eq_bterms bs bs'
                  # alpha_eq_bterms bs2 bs2'
                  # differ_bterms b bs' bs2'
                  # disjoint (flat_map bound_vars_bterm bs') vs
                  # disjoint (flat_map bound_vars_bterm bs2') vs}}) as h.

      { revert dependent bs2.
        induction bs; destruct bs2; introv len imp; allsimpl; ginv.
        - exists ([] : list (@BTerm o)) ([] : list (@BTerm o));
            dands; simpl; eauto with slow; try (apply br_bterms_nil).
        - cpx.
          destruct a as [l1 t1].
          destruct b0 as [l2 t2].
          pose proof (imp (bterm l1 t1) (bterm l2 t2)) as h; autodimp h hyp.
          inversion h as [? ? ? d1]; subst; clear h.
          pose proof (ind t1 l2) as h; autodimp h hyp.
          pose proof (h t2 d1) as k; clear h.
          exrepnd.

          autodimp IHbs hyp.
          { introv i d; eapply ind; eauto. }
          pose proof (IHbs bs2) as k.
          repeat (autodimp k hyp).
          exrepnd.

          pose proof (fresh_vars
                        (length l2)
                        (vs
                           ++ l2
                           ++ all_vars t1
                           ++ all_vars t2
                           ++ all_vars u1
                           ++ all_vars u2
                        )) as fv; exrepnd.
          allrw disjoint_app_r; repnd.

          exists ((bterm lvn (lsubst_aux u1 (var_ren l2 lvn))) :: bs')
                 ((bterm lvn (lsubst_aux u2 (var_ren l2 lvn))) :: bs2');
            dands; simpl;
            try (apply br_bterms_cons);
            try (apply alpha_eq_bterm_congr);
            tcsp.
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply alpha_bterm_change_aux; eauto 3 with slow.
            allrw disjoint_app_l; dands; eauto 3 with slow. }
          { apply differ_bterm.
            apply differ_lsubst_aux; eauto 3 with slow;
            rw @sub_free_vars_var_ren; eauto 3 with slow. }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u1 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
          { allrw disjoint_app_l; dands; eauto 3 with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u2 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
      }

      exrepnd.
      allunfold @alpha_eq_bterms.
      allunfold @differ_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands; eauto with slow.

      * apply alpha_eq_oterm_combine; dands; auto.

      * apply alpha_eq_oterm_combine; dands; auto.
Qed.

Lemma differ_subst {o} :
  forall b (t1 t2 : @NTerm o) sub1 sub2,
    differ b t1 t2
    -> differ_subs b sub1 sub2
    -> differ_alpha b (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  rw h0; rw k0.

  pose proof (differ_change_bound_vars
                b (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2 dt) as d; exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply differ_lsubst_aux; auto.
Qed.
Hint Resolve differ_subst : slow.

Lemma differ_bterms_implies_eq_map_num_bvars {o} :
  forall b (bs1 bs2 : list (@BTerm o)),
    differ_bterms b bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv d; allsimpl; auto;
  allunfold @differ_bterms; allunfold @br_bterms; allunfold @br_list;
  allsimpl; repnd; cpx.
  pose proof (d a b0) as h; autodimp h hyp.
  inversion h; subst.
  f_equal.
  unfold num_bvars; simpl; auto.
Qed.

Definition differ_sk {o} b (sk1 sk2 : @sosub_kind o) :=
  differ_b b (sk2bterm sk1) (sk2bterm sk2).

Inductive differ_sosubs {o} b : @SOSub o -> @SOSub o -> Type :=
| dsosub_nil : differ_sosubs b [] []
| dsosub_cons :
    forall v sk1 sk2 sub1 sub2,
      differ_sk b sk1 sk2
      -> differ_sosubs b sub1 sub2
      -> differ_sosubs b ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors differ_sosubs.

Lemma differ_bterms_cons {o} :
  forall b (b1 b2 : @BTerm o) bs1 bs2,
    differ_bterms b (b1 :: bs1) (b2 :: bs2)
    <=> (differ_b b b1 b2 # differ_bterms b bs1 bs2).
Proof.
  unfold differ_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma differ_mk_abs_substs {o} :
  forall b (bs1 bs2 : list (@BTerm o)) vars,
    differ_bterms b bs1 bs2
    -> length vars = length bs1
    -> differ_sosubs b (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv d m; allsimpl; cpx; tcsp.
  - provefalse.
    apply differ_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx.
  - apply differ_bterms_cons in d; repnd.
    destruct s, a, b0.
    inversion d0; subst.
    boolvar; auto.
Qed.

Lemma differ_sosubs_implies_eq_length {o} :
  forall b (sub1 sub2 : @SOSub o),
    differ_sosubs b sub1 sub2
    -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv d; inversion d; subst; allsimpl; tcsp.
Qed.

Lemma differ_b_change_bound_vars {o} :
  forall b vs (b1 b2 : @BTerm o),
    differ_b b b1 b2
    -> {u1 : BTerm
        & {u2 : BTerm
           & differ_b b u1 u2
           # alpha_eq_bterm b1 u1
           # alpha_eq_bterm b2 u2
           # disjoint (bound_vars_bterm u1) vs
           # disjoint (bound_vars_bterm u2) vs}}.
Proof.
  introv d.
  pose proof (differ_change_bound_vars
                b vs (oterm Exc [b1]) (oterm Exc [b2])) as h.
  autodimp h hyp.
  - apply differ_oterm; simpl; auto.
    introv i; dorn i; tcsp; cpx.
  - exrepnd.
    inversion h2 as [|?|? ? ? len1 imp1]; subst; allsimpl; cpx.
    inversion h3 as [|?|? ? ? len2 imp2]; subst; allsimpl; cpx.
    pose proof (imp1 0) as k1; autodimp k1 hyp; allsimpl; clear imp1.
    pose proof (imp2 0) as k2; autodimp k2 hyp; allsimpl; clear imp2.
    allunfold @selectbt; allsimpl.
    allrw app_nil_r.
    exists x x0; dands; auto.
    inversion h0 as [|?|?|? ? ? ? i]; subst; allsimpl; GC.
    apply i; sp.
Qed.

Lemma differ_sk_change_bound_vars {o} :
  forall b vs (sk1 sk2 : @sosub_kind o),
    differ_sk b sk1 sk2
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
           & differ_sk b u1 u2
           # alphaeq_sk sk1 u1
           # alphaeq_sk sk2 u2
           # disjoint (bound_vars_sk u1) vs
           # disjoint (bound_vars_sk u2) vs}}.
Proof.
  introv d.
  unfold differ_sk in d.
  apply (differ_b_change_bound_vars b vs) in d; exrepnd; allsimpl.
  exists (bterm2sk u1) (bterm2sk u2).
  destruct u1, u2, sk1, sk2; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ_sosubs_change_bound_vars {o} :
  forall b vs (sub1 sub2 : @SOSub o),
    differ_sosubs b sub1 sub2
    -> {sub1' : SOSub
        & {sub2' : SOSub
           & differ_sosubs b sub1' sub2'
           # alphaeq_sosub sub1 sub1'
           # alphaeq_sosub sub2 sub2'
           # disjoint (bound_vars_sosub sub1') vs
           # disjoint (bound_vars_sosub sub2') vs}}.
Proof.
  induction sub1; destruct sub2; introv d.
  - exists ([] : @SOSub o) ([] : @SOSub o); dands; simpl; tcsp.
  - inversion d.
  - inversion d.
  - inversion d as [|? ? ? ? ? dsk dso]; subst; clear d.
    apply IHsub1 in dso; exrepnd.
    apply (differ_sk_change_bound_vars b vs) in dsk; exrepnd.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto with slow.
Qed.

Lemma sosub_find_some_if_differ_sosubs {o} :
  forall b (sub1 sub2 : @SOSub o) v sk,
    differ_sosubs b sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind & differ_sk b sk sk' # sosub_find sub2 v = Some sk'}.
Proof.
  induction sub1; destruct sub2; introv aeq sf; allsimpl; tcsp.
  - inversion aeq.
  - destruct a, p; destruct s, s0.
    inversion aeq as [|? ? ? ? ? dsk dso]; subst; clear aeq.
    boolvar; subst; cpx; tcsp.
    + eexists; dands; eauto.
    + inversion dsk; subst; tcsp.
    + inversion dsk; subst; tcsp.
Qed.

Lemma sosub_find_none_if_differ_sosubs {o} :
  forall b (sub1 sub2 : @SOSub o) v,
    differ_sosubs b sub1 sub2
    -> sosub_find sub1 v = None
    -> sosub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv aeq sf; allsimpl; tcsp.
  - inversion aeq.
  - destruct a, p; destruct s, s0.
    inversion aeq as [|? ? ? ? ? dsk dso]; subst; clear aeq.
    boolvar; subst; cpx; tcsp.
    inversion dsk; subst; tcsp.
Qed.

Lemma differ_subs_combine {o} :
  forall b (ts1 ts2 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> (forall t1 t2,
          LIn (t1,t2) (combine ts1 ts2)
          -> differ b t1 t2)
    -> differ_subs b (combine vs ts1) (combine vs ts2).
Proof.
  induction ts1; destruct ts2; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma differ_apply_list {o} :
  forall b (ts1 ts2 : list (@NTerm o)) t1 t2,
    differ b t1 t2
    -> length ts1 = length ts2
    -> (forall x y, LIn (x,y) (combine ts1 ts2) -> differ b x y)
    -> differ b (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; destruct ts2; introv d l i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ_oterm; simpl; auto.
  introv k.
  dorn k;[|dorn k]; cpx; constructor; auto.
Qed.

Lemma differ_sosub_filter {o} :
  forall b (sub1 sub2 : @SOSub o) vs,
    differ_sosubs b sub1 sub2
    -> differ_sosubs b (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ_sosub_filter : slow.

Lemma differ_sosub_aux {o} :
  forall b (t : @SOTerm o) sub1 sub2,
    differ_sosubs b sub1 sub2
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ b (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv ds disj1 disj2 disj3 disj4 disj5 disj6 cov1 cov2; allsimpl; auto.

  - Case "sovar".
    allrw @cover_so_vars_sovar; repnd.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ_sosubs b sub1 sub2) in Heqf1; auto.
      exrepnd.
      rw Heqf2.
      destruct s as [l1 t1].
      destruct sk' as [l2 t2].
      inversion Heqf0; subst.
      apply differ_lsubst_aux; auto.

      * apply differ_subs_combine; allrw map_length; auto.
        introv i.
        rw <- @map_combine in i.
        rw in_map_iff in i; exrepnd; cpx.
        apply in_combine_same in i1; repnd; subst; allsimpl.
        disj_flat_map.
        apply ind; auto.

      * apply sosub_find_some in Heqf1; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto 3 with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

      * apply sosub_find_some in Heqf2; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto 3 with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

    + applydup (sosub_find_none_if_differ_sosubs b sub1 sub2) in Heqf1; auto.
      rw Heqf0.
      apply differ_apply_list; allrw map_length; auto.
      introv i.
      rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
      apply in_combine_same in i1; repnd; subst; allsimpl.
      disj_flat_map.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm.
    apply differ_oterm; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
    apply in_combine_same in i1; repnd; subst; allsimpl.
    destruct a as [l t].
    disj_flat_map.
    allsimpl; allrw disjoint_app_l; repnd.
    constructor.
    eapply ind; eauto 3 with slow.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub1 (vars2sovars l)) as sv.
      eapply subvars_disjoint_r;[exact sv|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub1 (vars2sovars l)) as sv1.
      pose proof (subvars_bound_vars_sosub_filter sub1 (vars2sovars l)) as sv2.
      eapply subvars_disjoint_r;[exact sv2|]; auto.
      eapply subvars_disjoint_l;[exact sv1|]; auto.

    + pose proof (subvars_bound_vars_sosub_filter sub1 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub2 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + pose proof (subvars_free_vars_sosub_sosub_filter sub2 (vars2sovars l)) as sv1.
      pose proof (subvars_bound_vars_sosub_filter sub2 (vars2sovars l)) as sv2.
      eapply subvars_disjoint_r;[exact sv2|]; auto.
      eapply subvars_disjoint_l;[exact sv1|]; auto.

    + pose proof (subvars_bound_vars_sosub_filter sub2 (vars2sovars l)) as sv1.
      eapply subvars_disjoint_r;[exact sv1|]; auto.

    + discover.
      apply cover_so_vars_sosub_filter; auto.

    + discover.
      apply cover_so_vars_sosub_filter; auto.
Qed.

Lemma differ_sosub {o} :
  forall b (t : @SOTerm o) (sub1 sub2 : SOSub),
    differ_sosubs b sub1 sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ_alpha b (sosub sub1 t) (sosub sub2 t).
Proof.
  introv d c1 c2.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.

  pose proof (differ_sosubs_change_bound_vars
                b (all_fo_vars t1
                                 ++ all_fo_vars t2
                                 ++ free_vars_sosub sub1
                                 ++ free_vars_sosub sub2
                  )
                sub1 sub2
                d) as e.
  destruct e as [sub1'' e]; destruct e as [sub2'' e]; repnd.

  pose proof (fo_change_bvars_alpha_spec
                (free_vars_sosub sub1''
                                 ++ free_vars_sosub sub2''
                                 ++ bound_vars_sosub sub1''
                                 ++ bound_vars_sosub sub2''
                )
                t) as q.
  revert q.
  fo_change t0; simpl; intro q; repnd; GC.

  allrw disjoint_app_l; allrw disjoint_app_r; repnd.

  assert (so_alphaeq t1 t0) as a1 by eauto 3 with slow.
  assert (so_alphaeq t2 t0) as a2 by eauto 3 with slow.

  pose proof (fovars_subvars_all_fo_vars t1) as sv1.
  pose proof (fovars_subvars_all_fo_vars t2) as sv2.
  pose proof (alphaeq_sosub_preserves_free_vars sub1 sub1'') as ev1; autodimp ev1 hyp.
  pose proof (alphaeq_sosub_preserves_free_vars sub2 sub2'') as ev2; autodimp ev2 hyp.
  pose proof (fovars_subvars_all_fo_vars t0) as sv3.
  pose proof (all_fo_vars_eqvars t0) as ev3.
  pose proof (all_fo_vars_eqvars t1) as ev4.
  pose proof (so_alphaeq_preserves_free_vars t1 t0 a1) as efv1.
  pose proof (so_alphaeq_preserves_free_vars t2 t0 a2) as efv2.
  applydup eqvars_app_r_implies_subvars in ev4 as ev; destruct ev as [ev5 ev6].

  assert (disjoint (fo_bound_vars t0) (free_vars_sosub sub1'')
          # disjoint (free_vars_sosub sub1'') (bound_vars_sosub sub1'')
          # disjoint (all_fo_vars t0) (bound_vars_sosub sub1'')
          # disjoint (fo_bound_vars t0) (free_vars_sosub sub2'')
          # disjoint (free_vars_sosub sub2'') (bound_vars_sosub sub2'')
          # disjoint (all_fo_vars t0) (bound_vars_sosub sub2'')) as disj.

  { dands; eauto 3 with slow.
    - rw <- ev1; eauto 3with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto 3 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto 3 with slow.
    - rw <- ev2; eauto 3 with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto 3 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto 3 with slow. }

  repnd.

  pose proof (sosub_aux_alpha_congr2 t1 t0 sub1' sub1'') as aeq1.
  repeat (autodimp aeq1 hyp); eauto 3 with slow.
  { rw disjoint_app_r; dands; eauto 3 with slow. }
  { rw disjoint_app_r; dands; eauto 3 with slow. }

  pose proof (sosub_aux_alpha_congr2 t2 t0 sub2' sub2'') as aeq2.
  repeat (autodimp aeq2 hyp); eauto 3 with slow.
  { rw disjoint_app_r; dands; eauto 3 with slow. }
  { rw disjoint_app_r; dands; eauto 3 with slow. }

  exists (sosub_aux sub1'' t0) (sosub_aux sub2'' t0); dands;
  try (apply alphaeq_eq; complete auto).

  apply differ_sosub_aux; auto.

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub1 sub1''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub1); auto. }

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub2 sub2''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub2); auto. }
Qed.

Lemma differ_mk_instance {o} :
  forall b (t : @SOTerm o) vars bs1 bs2,
    matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered t vars
    -> socovered t vars
    -> differ_bterms b bs1 bs2
    -> differ_alpha b (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv m1 m2 sc1 sc2 dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ_mk_abs_substs o b bs1 bs2 vars) in dbs; auto.

  apply differ_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Lemma implies_differ_alpha_force_int {o} :
  forall v b (t1 t2 : @NTerm o) e,
    !LIn v (free_vars e)
    -> differ_alpha b t1 t2
    -> differ_alpha b (force_int_bound v b t1 e) (force_int t2).
Proof.
  introv ni d.
  unfold differ_alpha in d; exrepnd.
  exists (force_int_bound v b u1 e) (force_int u2); dands.
  - apply alpha_eq_force_int_bound; auto.
  - apply alpha_eq_force_int; auto.
  - apply differ_force_int; auto.
Qed.

Lemma differ_alpha_mk_atom_eq {o} :
  forall b (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    differ_alpha b a1 a2
    -> differ_alpha b b1 b2
    -> differ_alpha b c1 c2
    -> differ_alpha b d1 d2
    -> differ_alpha b (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv da1 da2 da3 da4.
  allunfold @differ_alpha; exrepnd.
  exists (mk_atom_eq u6 u4 u0 u1) (mk_atom_eq u7 u5 u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_alpha_mk_exception {o} :
  forall b (a1 a2 b1 b2 : @NTerm o),
    differ_alpha b a1 a2
    -> differ_alpha b b1 b2
    -> differ_alpha b (mk_exception a1 b1) (mk_exception a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ_alpha; exrepnd.
  exists (mk_exception u0 u1) (mk_exception u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_preserves_isvalue_like {o} :
  forall b (t1 t2 : @NTerm o),
    differ b t1 t2
    -> isvalue_like t2
    -> isvalue_like t1.
Proof.
  introv d ivl.
  allunfold @isvalue_like; exrepnd.
  repndors;[left|right].
  - apply iscan_implies in ivl; repndors; exrepnd; subst;
    inversion d; subst; eauto 3 with slow.
  - apply isexc_implies2 in ivl; exrepnd; subst.
    inversion d; subst; eauto 3 with slow.
Qed.

Definition differ_b_alpha {o} (b : nat) (b1 b2 : @BTerm o) :=
  {u1 : BTerm
   & {u2 : BTerm
      & alpha_eq_bterm b1 u1
      # alpha_eq_bterm b2 u2
      # differ_b b u1 u2}}.

Definition differ_bs_alpha {o} b (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ_b_alpha b) bs1 bs2.

Lemma differ_bterms_nil {o} :
  forall b, @differ_bterms o b [] [].
Proof.
  unfold differ_bterms, br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve differ_bterms_nil : slow.

Lemma differ_bterms_cons_if {o} :
  forall b (b1 b2 : @BTerm o) bs1 bs2,
    differ_b b b1 b2
    -> differ_bterms b bs1 bs2
    -> differ_bterms b (b1 :: bs1) (b2 :: bs2).
Proof.
  introv d1 d2; apply differ_bterms_cons; sp.
Qed.
Hint Resolve differ_bterms_cons_if : slow.

Lemma implies_differ_alpha_oterm {o} :
  forall b op (bs1 bs2 : list (@BTerm o)),
    differ_bs_alpha b bs1 bs2
    -> differ_alpha b (oterm op bs1) (oterm op bs2).
Proof.
  introv diff.
  unfold differ_bs_alpha, br_bterms, br_list in diff; repnd.

  assert {bs1' : list BTerm
          & {bs2' : list BTerm
          & alpha_eq_bterms bs1 bs1'
          # alpha_eq_bterms bs2 bs2'
          # differ_bterms b bs1' bs2'}} as hbs.
  { revert dependent bs2.
    induction bs1; introv len imp; destruct bs2; allsimpl; cpx; GC.
    - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)); dands; eauto 3 with slow.
    - pose proof (imp a b0) as h; autodimp h hyp.
      pose proof (IHbs1 bs2) as k; repeat (autodimp k hyp).
      exrepnd.
      unfold differ_b_alpha in h; exrepnd.
      exists (u1 :: bs1') (u2 :: bs2'); dands; eauto 3 with slow. }

  exrepnd.
  applydup @alpha_eq_bterms_implies_same_length in hbs0.
  applydup @alpha_eq_bterms_implies_same_length in hbs2.
  exists (oterm op bs1') (oterm op bs2'); dands; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs0; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs2; auto.

  - constructor; try lia.
    introv i; apply hbs1; auto.
Qed.

Lemma differ_alpha_pushdown_fresh_isvalue_like {o} :
  forall b v (t1 t2 : @NTerm o),
    isvalue_like t1
    -> differ b t1 t2
    -> differ_alpha b (pushdown_fresh v t1) (pushdown_fresh v t2).
Proof.
  introv ivl d.
  destruct t1 as [v1|f1|op1 bs1].
  - inversion d; allsimpl; subst; allsimpl; eauto 3 with slow.
  - inversion d; allsimpl; subst; allsimpl; eauto 3 with slow.
  - inversion d as [? ? d1 d2|?|?|? ? ? len imp d1]; subst; allsimpl; fold_terms; clear d.
    + unfold isvalue_like in ivl; repndors; inversion ivl.
    + apply implies_differ_alpha_oterm.
      unfold differ_bs_alpha, br_bterms, br_list.
      allrw @length_mk_fresh_bterms; dands; auto.
      introv i.
      unfold mk_fresh_bterms in i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
      applydup imp in i1.
      destruct a0 as [l1 t1].
      destruct a as [l2 t2].
      inversion i0 as [? ? ? d]; subst; clear i0.
      simpl.
      unfold maybe_new_var; boolvar.

      * pose proof (ex_fresh_var (all_vars t1 ++ all_vars t2)) as fv; exrepnd.
        allrw in_app_iff; allrw not_over_or; repnd.
        exists (bterm l2 (mk_fresh v0 t1)) (bterm l2 (mk_fresh v0 t2)).
        dands; auto.

        { apply alpha_eq_bterm_congr.
          apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp.
          repeat (rw @lsubst_trivial3); allsimpl; auto.
          - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
            dands; auto.
          - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
            dands; auto.
            apply newvar_prop. }

        { apply alpha_eq_bterm_congr.
          apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp.
          repeat (rw @lsubst_trivial3); allsimpl; auto.
          - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
            dands; auto.
          - introv i; repndors; tcsp; cpx; allsimpl; allrw disjoint_singleton_l.
            dands; auto.
            apply newvar_prop. }

        { constructor; constructor; simpl; auto.
          introv i; repndors; cpx. }

      * exists (bterm l2 (mk_fresh v t1)) (bterm l2 (mk_fresh v t2)).
        dands; auto.
        constructor; constructor; auto.
        introv i; allsimpl; repndors; cpx.
Qed.

Lemma differ_preserves_isnoncan_like {o} :
  forall (b : nat) (t1 t2 : @NTerm o),
    differ b t1 t2
    -> isnoncan_like t2
    -> isnoncan_like t1.
Proof.
  introv d isn.
  allunfold @isnoncan_like; exrepnd.
  repndors;[left|right].
  - apply isnoncan_implies in isn; exrepnd; subst.
    inversion d; subst; eauto 3 with slow.
    unfold force_int_bound, mk_cbv; eauto 3 with slow.
  - apply isabs_implies in isn; exrepnd; subst.
    inversion d; subst; eauto 3 with slow.
Qed.

Lemma get_ints_lsubst_aux_allvars {o} :
  forall (t : @NTerm o) sub,
    allvars_sub sub
    -> get_ints (lsubst_aux t sub) = get_ints t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv avs; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_allvars in Heqsf; auto; exrepnd; subst; allsimpl; auto.

  - Case "oterm".
    f_equal.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; allsimpl.
    erewrite ind; eauto 3 with slow.
Qed.

Lemma get_ints_lsubst_aux_nr_ut {o} :
  forall (t : @NTerm o) sub u,
    nr_ut_sub u sub
    -> disjoint (free_vars u) (bound_vars t)
    -> get_ints (lsubst_aux t sub) = get_ints t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv avs disj; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; auto.
    apply sub_find_some in Heqsf.
    eapply in_nr_ut_sub in Heqsf; eauto; exrepnd; subst; allsimpl; auto.

  - Case "oterm".
    f_equal.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [l t]; allsimpl.
    disj_flat_map; allsimpl; allrw disjoint_app_r; repnd.
    erewrite ind; eauto 3 with slow.
Qed.

Lemma alpha_eq_preserves_get_ints {o} :
  forall t1 t2 : @NTerm o,
    alpha_eq t1 t2 -> get_ints t1 = get_ints t2.
Proof.
  nterm_ind1s t1 as [v|f ind|op bs ind] Case; introv aeq; simpl; auto.

  - Case "vterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "sterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst.
    simpl; f_equal.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup in_combine in i; repnd.
    applydup aeq0 in i.
    destruct t1 as [l1 u1].
    destruct t2 as [l2 u2].
    allsimpl.
    inversion i2 as [? ? ? ? ? disj len1 len2 norep a]; subst.
    pose proof (ind u1 (lsubst u1 (var_ren l1 lv)) l1) as q; repeat (autodimp q hyp).
    { rw @lsubst_allvars_preserves_osize; eauto 3 with slow. }
    apply q in a; clear q.
    allrw disjoint_app_r; repnd.
    repeat (rw @lsubst_lsubst_aux in a;[|rw @flat_map_free_var_vars_range;eauto 3 with slow];try lia).
    repeat (rw @get_ints_lsubst_aux_allvars in a; eauto 3 with slow).
Qed.

Lemma differ_alpha_l {o} :
  forall b (t1 t2 t3 : @NTerm o),
    alpha_eq t1 t2
    -> differ_alpha b t2 t3
    -> differ_alpha b t1 t3.
Proof.
  introv aeq d.
  allunfold @differ_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Lemma differ_alpha_r {o} :
  forall b (t1 t2 t3 : @NTerm o),
    differ_alpha b t1 t2
    -> alpha_eq t2 t3
    -> differ_alpha b t1 t3.
Proof.
  introv aeq d.
  allunfold @differ_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Lemma differ_alpha_mk_fresh {o} :
  forall b v (t1 t2 : @NTerm o),
    differ_alpha b t1 t2
    -> differ_alpha b (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv d.
  allunfold @differ_alpha; exrepnd.
  exists (mk_fresh v u1) (mk_fresh v u2); dands;
  try (apply implies_alpha_eq_mk_fresh; eauto 3 with slow).
  constructor; simpl; auto; introv i; repndors; cpx.
Qed.

Lemma differ_subst_utokens_aux {o} :
  forall b (t1 t2 : @NTerm o) sub,
    disjoint (bound_vars t1) (free_vars_utok_sub sub)
    -> disjoint (bound_vars t2) (free_vars_utok_sub sub)
    -> differ b t1 t2
    -> differ b (subst_utokens_aux t1 sub) (subst_utokens_aux t2 sub).
Proof.
  nterm_ind t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv disj1 disj2 d; auto.

  - Case "vterm".
    inversion d; subst; allsimpl; eauto 3 with slow.

  - Case "sterm".
    inversion d; subst; allsimpl; eauto 3 with slow.

  - Case "oterm".
    inversion d as [? ? ? ? ni d1|?|?|? ? ? len1 imp1]; subst; clear d.

    + allsimpl; allrw app_nil_r; fold_terms.
      allrw disjoint_app_l; allrw disjoint_cons_l; repnd.
      constructor.
      { intro i; apply free_vars_subst_utokens_aux_subset in i.
        rw in_app_iff in i; repndors; tcsp. }

      pose proof (ind1 t1 []) as q; autodimp q hyp.

    + allrw @subst_utokens_aux_oterm; allsimpl.
      remember (get_utok op1) as guo1; symmetry in Heqguo1; destruct guo1.

      * unfold subst_utok.
        remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
        constructor; allrw map_length; auto.
        introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
        applydup imp1 in i1; applydup in_combine in i1; repnd.
        disj_flat_map.
        destruct a0 as [l1 u1].
        destruct a as [l2 u2].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? d1]; subst; clear i0.
        constructor.

        pose proof (ind1 u1 l2) as q; autodimp q hyp.

      * constructor; allrw map_length; auto.
        introv i; allrw <- @map_combine; allrw in_map_iff; exrepnd; cpx; allsimpl.
        applydup imp1 in i1; applydup in_combine in i1; repnd.
        disj_flat_map.
        destruct a0 as [l1 u1].
        destruct a as [l2 u2].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? d1]; subst; clear i0.
        constructor.

        pose proof (ind1 u1 l2) as q; autodimp q hyp.
Qed.

Lemma differ_alpha_subst_utokens {o} :
  forall b (t1 t2 : @NTerm o) sub,
    differ_alpha b t1 t2
    -> differ_alpha b (subst_utokens t1 sub) (subst_utokens t2 sub).
Proof.
  introv d.
  unfold differ_alpha in d; exrepnd.

  eapply differ_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d0|].
  eapply differ_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d2].
  clear dependent t1.
  clear dependent t2.

  pose proof (differ_change_bound_vars
                b (free_vars_utok_sub sub)
                u1 u2 d1) as d; exrepnd.
  rename u0 into t1.
  rename u3 into t2.

  eapply differ_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d3|].
  eapply differ_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d4].
  clear dependent u1.
  clear dependent u2.

  pose proof (unfold_subst_utokens sub t1) as h; exrepnd.
  pose proof (unfold_subst_utokens sub t2) as k; exrepnd.
  rename t' into u1.
  rename t'0 into u2.
  rw h0; rw k0.

  eapply differ_alpha_l;[apply (alpha_eq_subst_utokens_aux u1 t1 sub sub); eauto 3 with slow|].
  eapply differ_alpha_r;[|apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u2 t2 sub sub); eauto 3 with slow].

  apply differ_implies_differ_alpha.
  apply differ_subst_utokens_aux; auto.
Qed.

Lemma differ_alpha_mk_eapply {o} :
  forall b (a1 a2 b1 b2 : @NTerm o),
    differ_alpha b a1 a2
    -> differ_alpha b b1 b2
    -> differ_alpha b (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ_alpha; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_mk_eapply {o} :
  forall b (a1 a2 b1 b2 : @NTerm o),
    differ b a1 a2
    -> differ b b1 b2
    -> differ b (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  constructor; simpl; auto.
  introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_exception_implies {o} :
  forall b (a e t : @NTerm o),
    differ b (mk_exception a e) t
    -> {a' : NTerm
        & {e' : NTerm
        & t = mk_exception a' e'
        # differ b a a'
        # differ b e e' }}.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d; allsimpl.

  pose proof (imp (nobnd a) x) as d1; autodimp d1 hyp.
  pose proof (imp (nobnd e) y) as d2; autodimp d2 hyp.
  clear imp.

  inversion d1 as [? ? ? d3]; subst; clear d1.
  inversion d2 as [? ? ? d4]; subst; clear d2.
  fold_terms.

  eexists; eexists; dands; eauto.
Qed.

Lemma differ_lam_implies {o} :
  forall b v a (t : @NTerm o),
    differ b (mk_lam v a) t
    -> {a' : NTerm
        & t = mk_lam v a'
        # differ b a a' }.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d; allsimpl.

  pose proof (imp (bterm [v] a) x) as d1; autodimp d1 hyp.
  clear imp.

  inversion d1 as [? ? ? d2]; subst; clear d1.
  fold_terms.

  eexists; eexists; dands; eauto.
Qed.

Lemma differ_exception_implies2 {o} :
  forall b (a e t : @NTerm o),
    differ b t (mk_exception a e)
    -> {a' : NTerm
        & {e' : NTerm
        & t = mk_exception a' e'
        # differ b a' a
        # differ b e' e }}.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d; allsimpl.

  pose proof (imp x (nobnd a)) as d1; autodimp d1 hyp.
  pose proof (imp y (nobnd e)) as d2; autodimp d2 hyp.
  clear imp.

  inversion d1 as [? ? ? d3]; subst; clear d1.
  inversion d2 as [? ? ? d4]; subst; clear d2.
  fold_terms.

  eexists; eexists; dands; eauto.
Qed.

Lemma differ_lam_implies2 {o} :
  forall b v a (t : @NTerm o),
    differ b t (mk_lam v a)
    -> {a' : NTerm
        & t = mk_lam v a'
        # differ b a' a }.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d; allsimpl.

  pose proof (imp x (bterm [v] a)) as d1; autodimp d1 hyp.
  clear imp.

  inversion d1 as [? ? ? d2]; subst; clear d1.
  fold_terms.

  eexists; eexists; dands; eauto.
Qed.

Lemma differ_preserves_iscan2 {o} :
  forall b (t1 t2 : @NTerm o),
    differ b t1 t2
    -> iscan t2
    -> iscan t1.
Proof.
  introv diff isc.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  inversion diff; subst; simpl; auto.
Qed.

Lemma differ_alpha_mk_lam {o} :
  forall b v (t1 t2 : @NTerm o),
    differ_alpha b t1 t2
    -> differ_alpha b (mk_lam v t1) (mk_lam v t2).
Proof.
  introv d.
  allunfold @differ_alpha; exrepnd.
  exists (mk_lam v u1) (mk_lam v u2); dands;
  try (apply implies_alpha_eq_mk_lam; eauto with slow).
  constructor; simpl; auto; introv i; repndors; cpx.
Qed.

(* right now let's just worry about successful computations *)
Lemma comp_force_int_step {o} :
  forall lib (t2 t1 : @NTerm o) b u,
    wf_term t1
    -> wf_term t2
    -> differ b t1 t2
    -> compute_step lib t2 = csuccess u
    -> (forall z, LIn z (get_ints t2) -> Z.abs_nat z < b)
    -> {t : NTerm
        & {u' : NTerm
           & reduces_to lib t1 t
           # reduces_to lib u u'
           # differ_alpha b t u'}}.
Proof.
  nterm_ind1s t2 as [v|f ind|op bs ind] Case; introv wft1 wft2 d comp i.

  -  Case "vterm".
     simpl.
     inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    inversion d; subst; clear d.
    exists (sterm f) (sterm f); dands; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase; ginv.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      inversion d; subst.
      exists (oterm (Can can) bs1) (oterm (Can can) bs); dands; eauto 3 with slow.

    + SCase "NCan".
      destruct bs as [|b2 bs];
        try (complete (allsimpl; ginv));[].

      destruct b2 as [l2 t2].
      destruct l2; try (complete (simpl in comp; ginv)).

      {
      destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d)).

      * destruct t1 as [v1|f1|op1 bs1]; try (complete (inversion d));[].
        inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv.

      * destruct t1 as [v1|f1|op1 bs1]; try (complete (inversion d));[].
        csunf comp; allsimpl.
        dopid_noncan ncan SSCase; allsimpl; ginv.

        { SSCase "NApply".
          apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          allsimpl.

          pose proof (imp x (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          pose proof (imp y (nobnd arg)) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.

          exists (mk_eapply (sterm f2) t0) (mk_eapply (sterm f2) arg); dands; eauto 3 with slow.
          apply differ_implies_differ_alpha.
          apply differ_mk_eapply; auto.
        }

        { SSCase "NEApply".
          apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          rw @wf_term_eq in wft1; rw @nt_wf_eapply_iff in wft1; exrepnd; allunfold @nobnd; subst; ginv.
          simpl in len; repeat cpx.
          simpl in imp.

          pose proof (imp (nobnd a) (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd b0) (nobnd arg2)) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.
          allrw <- @wf_eapply_iff; repnd.

          repndors; exrepnd; subst.

          - apply compute_step_eapply2_success in comp1; repnd; GC.
            repndors; exrepnd; subst; ginv; allsimpl; GC.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl;
            clear d4; cpx; clear imp1; fold_terms.

            exists (f n) (f n); dands; eauto 3 with slow.
            apply reduces_to_if_step.
            csunf; simpl.
            dcwf h; simpl; boolvar; try lia.
            rw @Znat.Nat2Z.id; auto.

          - apply isexc_implies2 in comp0; exrepnd; subst.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.
            exists (oterm Exc bs1) (oterm Exc l); dands; eauto 3 with slow.

          - pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            pose proof (h b0 b x) as ih; clear h.
            applydup @preserve_nt_wf_compute_step in comp1; eauto 3 with slow.
            allsimpl; autorewrite with slow in *; auto.
            repeat (autodimp ih hyp); eauto 3 with slow.
            exrepnd.

            exists (mk_eapply (sterm f2) t) (mk_eapply (sterm f2) u'); dands; eauto 3 with slow.
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply differ_alpha_mk_eapply; eauto 3 with slow. }
        }

        { SSCase "NFix".
          apply compute_step_fix_success in comp; repnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl.

          pose proof (imp x (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          clear imp.

          inversion d1 as [? ? ? d2]; subst; clear d1.
          inversion d2; subst; clear d2.
          fold_terms.

          exists (mk_apply (sterm f2) (mk_fix (sterm f2)))
                 (mk_apply (sterm f2) (mk_fix (sterm f2))).
          dands; eauto 3 with slow.
        }

        { SSCase "NCbv".
          apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp x0 (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          pose proof (imp y (bterm [v] x)) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? d3]; subst; clear d1.
          inversion d3; subst; clear d3.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          fold_terms.

          exists (subst t1 v (sterm f2))
                 (subst x v (sterm f2)).
          dands; eauto 3 with slow.
          apply differ_subst; auto.
        }

        { SSCase "NTryCatch".
          apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp x0 (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          pose proof (imp y (nobnd a)) as d2; autodimp d2 hyp.
          pose proof (imp z (bterm [v] x)) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3 as [? ? ? d5]; subst; clear d3.
          fold_terms.

          exists (mk_atom_eq t1 t1 (sterm f2) mk_bot)
                 (mk_atom_eq a a (sterm f2) mk_bot).
          dands; eauto 3 with slow.
          apply differ_alpha_mk_atom_eq; eauto 3 with slow.
        }

        { SSCase "NCanTest".
          apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp x (nobnd (sterm f2))) as d1; autodimp d1 hyp.
          pose proof (imp y (nobnd a)) as d2; autodimp d2 hyp.
          pose proof (imp z (nobnd b0)) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3 as [? ? ? d5]; subst; clear d3.
          fold_terms.

          exists t0 b0.
          dands; eauto 3 with slow.
        }

      * (* Now destruct op2 *)
        dopid op2 as [can2|ncan2|exc2|abs2] SSCase; ginv.

        { SSCase "Can".
          allsimpl.

          (* Because the principal argument is canonical we can destruct ncan *)
          dopid_noncan ncan SSSCase.

          - SSSCase "NApply".
            csunf comp; allsimpl.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst.

            { inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
              destruct bs1; simphyps; cpx.
              destruct bs1; simphyps; cpx.
              cpx.

              pose proof (imp b1 (bterm [] (oterm (Can NLambda) [bterm [v] b0]))) as h1.
              autodimp h1 hyp.
              inversion h1 as [? ? ? k1]; subst; clear h1.
              inversion k1 as [|?|?|? ? ? len1 imp1]; subst; clear k1.
              allsimpl; cpx.

              destruct x.
              pose proof (imp1 (bterm l n) (bterm [v] b0)) as d1; clear imp1.
              simpl in d1.
              autodimp d1 hyp.
              inversion d1 as [? ? ? k1]; subst; clear d1.

              pose proof (imp b2 (bterm [] arg)) as h2.
              autodimp h2 hyp.
              inversion h2 as [? ? ? k2]; subst; clear h2.
              allsimpl; cpx.
              clear imp.

              exists (subst n v t1) (subst b0 v arg); dands; eauto 3 with slow.

              apply differ_subst; auto.
            }

            { inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
              cpx; allsimpl; fold_terms.

              pose proof (imp x (nobnd (mk_nseq f))) as h1; autodimp h1 hyp.
              pose proof (imp y (nobnd arg)) as h2; autodimp h2 hyp.
              clear imp.

              inversion h1 as [? ? ? k1]; subst; clear h1.
              inversion h2 as [? ? ? k2]; subst; clear h2.

              inversion k1 as [|?|?|? ? ? len1 imp1]; subst; clear k1.
              allsimpl; cpx.
              allsimpl; clear imp1; fold_terms.

              exists (mk_eapply (mk_nseq f) t0) (mk_eapply (mk_nseq f) arg); dands; eauto 3 with slow.

              apply differ_implies_differ_alpha.
              apply differ_oterm; simpl; auto.
              introv j; repndors; cpx; repeat (constructor; auto).
              simpl; introv; tcsp.
            }

          - SSSCase "NEApply".
            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst.
            rw @wf_term_eq in wft2; rw @nt_wf_eapply_iff in wft2; exrepnd; allunfold @nobnd; ginv.

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            simpl in len; cpx; simpl in imp.

            pose proof (imp x (nobnd (oterm (Can can2) bs2))) as d1; autodimp d1 hyp.
            pose proof (imp y (nobnd b0)) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            fold_terms.
            allrw <- @wf_eapply_iff; repnd.
            apply eapply_wf_def_oterm_implies in comp2.
            destruct comp2 as [comp2|comp2]; exrepnd; ginv; fold_terms.

            { apply differ_lam_implies2 in d3; exrepnd; subst; fold_terms.

              repndors; exrepnd; subst.

              + apply compute_step_eapply2_success in comp1; repnd; GC.
                repndors; exrepnd; subst; ginv; allsimpl; GC.
                allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                exists (subst a' v0 t0) (subst b1 v0 b0); dands; eauto 3 with slow.
                { apply eapply_lam_can_implies.
                  apply differ_preserves_iscan2 in d4; auto.
                  unfold computes_to_can; dands; eauto 3 with slow. }
                { apply differ_subst; auto. }

              + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ_exception_implies2 in d4; exrepnd; subst.
                exists (mk_exception a'0 e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ_alpha_mk_exception; eauto 3 with slow.

              + pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 b x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                allsimpl; autorewrite with slow in *.
                repeat (autodimp ih hyp); eauto 3 with slow.
                { introv j; apply i; rw in_app_iff; tcsp. }
                exrepnd.

                exists (mk_eapply (mk_lam v a') t1) (mk_eapply (mk_lam v t) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ_alpha_mk_eapply; eauto 3 with slow.
                  apply differ_alpha_mk_lam; eauto 3 with slow. }
            }

            { inversion d3 as [|?|?|? ? ? len imp]; subst; simphyps; clear d3.
              clear imp.
              allsimpl; cpx; allsimpl; fold_terms.
              repndors; exrepnd; subst; allsimpl.

              - destruct b0 as [v|f|op bs]; ginv;[].
                dopid op as [can|ncan|exc|abs] SSSSCase; ginv;[].
                destruct can; ginv;[].
                destruct bs; allsimpl; ginv; GC.
                boolvar; ginv; try lia; fold_terms.
                inversion d4 as [|?|?|? ? ? len imp]; subst; simphyps; clear d4.
                allsimpl; cpx; fold_terms; allsimpl.
                clear imp.

                exists (@mk_nat o (s (Z.to_nat z))) (@mk_nat o (s (Z.to_nat z))); dands; eauto 3 with slow.
                apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
                boolvar; try lia; auto.

              - apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ_exception_implies2 in d4; exrepnd; subst.
                exists (mk_exception a' e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ_alpha_mk_exception; eauto 3 with slow.

              - pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 b x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                allsimpl; autorewrite with slow in *.
                repeat (autodimp ih hyp); eauto 3 with slow.
                exrepnd.

                exists (mk_eapply (mk_nseq s) t) (mk_eapply (mk_nseq s) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ_alpha_mk_eapply; eauto 3 with slow. }
            }

(*          - SSSCase "NApseq".
            csunf comp; allsimpl.
            apply compute_step_apseq_success in comp; repndors; exrepnd; subst.

            { inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
              allsimpl; cpx; allsimpl; fold_terms.

              pose proof (imp x (nobnd (mk_nat n0))) as h1.
              autodimp h1 hyp.
              clear imp.
              inversion h1 as [? ? ? k1]; subst; clear h1.
              inversion k1 as [|?|?|? ? ? len1 imp1]; subst; clear k1.
              allsimpl; cpx.
              allsimpl; clear imp1; fold_terms.

              exists (@mk_nat o (n n0)) (@mk_nat o (n n0)); dands; eauto 3 with slow.
              apply reduces_to_if_step; csunf; simpl.
              rw @Znat.Nat2Z.id.
              boolvar; try lia; auto.
            }*)

          - SSSCase "NFix".
            csunf comp; allsimpl.
            apply compute_step_fix_success in comp; repnd; subst.
            inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
            cpx; allsimpl.
            allrw app_nil_r.
            destruct x.
            pose proof (imp (bterm l n) (bterm [] (oterm (Can can2) bs2))) as d.
            autodimp d hyp.
            inversion d as [? ? ? d1]; subst; clear d.
            inversion d1 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d1.
            exists (mk_apply
                      (oterm (Can can2) bs1)
                      (oterm (NCan NFix) [bterm [] (oterm (Can can2) bs1)]))
                   (mk_apply (oterm (Can can2) bs2)
                             (oterm (NCan NFix) [bterm [] (oterm (Can can2) bs2)])).
            dands; eauto 3 with slow.

            apply differ_implies_differ_alpha.
            apply differ_oterm; simpl; auto.
            introv j.
            dorn j; cpx.
            dorn j; cpx.
            constructor.
            apply differ_oterm; simpl; auto.

          - SSSCase "NSpread".
            csunf comp; allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b1 (bterm [] (mk_pair a b0))) as d1.
            autodimp d1 hyp.
            pose proof (imp b2 (bterm [va,vb] arg)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp1 b1 (nobnd a)) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            pose proof (imp1 b2 (nobnd b0)) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d3]; subst; clear d1.
            clear imp1.

            exists (lsubst t0 [(va,t1),(vb,t2)]) (lsubst arg [(va, a), (vb, b0)]);
              dands; eauto 4 with slow.

          - SSSCase "NDsup".
            csunf comp; allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b1 (bterm [] (mk_sup a b0))) as d1.
            autodimp d1 hyp.
            pose proof (imp b2 (bterm [va,vb] arg)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp1 b1 (nobnd a)) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            pose proof (imp1 b2 (nobnd b0)) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d3]; subst; clear d1.
            clear imp1.

            exists (lsubst t0 [(va,t1),(vb,t2)]) (lsubst arg [(va, a), (vb, b0)]);
              dands; eauto 4 with slow.

          - SSSCase "NDecide".
            csunf comp; allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; simphyps; clear d.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can can2) [bterm [] d0]))) as d1.
            autodimp d1 hyp.
            pose proof (imp b1 (bterm [v1] t0)) as d2.
            autodimp d2 hyp.
            pose proof (imp b2 (bterm [v2] t2)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d4.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp1 b0 (bterm [] d0)) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            clear imp1.

            dorn comp0; repnd; subst.

            + exists (lsubst t3 [(v1,t1)]) (subst t0 v1 d0); dands; eauto 3 with slow.
              apply differ_subst; auto.

            + exists (lsubst t4 [(v2,t1)]) (subst t2 v2 d0); dands; eauto 3 with slow.
              apply differ_subst; auto.

          - SSSCase "NCbv".
            csunf comp; allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.

            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can can2) bs2))) as d1.
            autodimp d1 hyp.
            pose proof (imp b1 (bterm [v] x)) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3.

            exists (subst t0 v (oterm (Can can2) bs1))
                   (subst x v (oterm (Can can2) bs2));
              dands; eauto 3 with slow.

            apply differ_subst; auto.

          - SSSCase "NSleep".
            csunf comp; allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.

            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can (Nint z)) []))) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3; cpx.

            exists (@mk_axiom o) (@mk_axiom o);
              dands; eauto 3 with slow.

          - SSSCase "NTUni".
            csunf comp; allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.

            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can (Nint (Z.of_nat n))) []))) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3; cpx.

            exists (@mk_uni o n) (@mk_uni o n);
              dands; eauto 3 with slow.

            apply reduces_to_if_step; simpl.
            csunf; simpl; unfold compute_step_tuni; simpl; boolvar; try lia; auto.
            rw Znat.Nat2Z.id; auto.

          - SSSCase "NMinus".
            csunf comp; allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.

            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can (Nint z)) []))) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d3; cpx.

            exists (@mk_integer o (- z)) (@mk_integer o (- z));
              dands; eauto 3 with slow.

          - SSSCase "NFresh".
            allsimpl; ginv.

          - SSSCase "NTryCatch".
            csunf comp; allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.
            cpx; allsimpl.

            pose proof (imp x0 (bterm [] (oterm (Can can2) bs2))) as d1.
            autodimp d1 hyp.
            pose proof (imp y (bterm [] a)) as d2.
            autodimp d2 hyp.
            pose proof (imp z (bterm [v] x)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d4.

            exists (mk_atom_eq t0 t0 (oterm (Can can2) bs1) mk_bot)
                   (mk_atom_eq a a (oterm (Can can2) bs2) mk_bot);
              dands; eauto 3 with slow.

            apply differ_implies_differ_alpha.
            constructor; simpl; auto.
            introv j; repndors; ginv; tcsp; constructor; auto.
            apply differ_refl.

          - SSSCase "NParallel".
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; allsimpl; subst; clear d.
            destruct bs1; allsimpl; cpx.
            pose proof (imp b0 (bterm [] (oterm (Can can2) bs2))) as d.
            autodimp d hyp.
            inversion d as [? ? ? d1]; subst; clear d.
            inversion d1 as [|?|?|? ? ? len' imp']; subst; clear d1.
            exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.

          - SSSCase "NCompOp".
            destruct bs;[csunf comp; allsimpl; complete (dcwf h)|].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f|op bs1];
            try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            simpl in len.

            destruct bs0; simpl in len; cpx.
            destruct bs0; simpl in len; cpx.
            simpl in imp.

            pose proof (imp b0 (bterm [] (oterm (Can can2) bs2))) as d1.
            autodimp d1 hyp.
            pose proof (imp b1 (bterm [] (oterm op bs1))) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; simpl in comp.
              dcwf h.
              apply compute_step_compop_success_can_can in comp.
              exrepnd; subst.
              allsimpl; cpx; allrw app_nil_r; allsimpl.

              clear imp1.

              pose proof (imp (nobnd (oterm (Can can2) [])) (nobnd (oterm (Can can2) []))) as dd1.
              autodimp dd1 hyp.
              pose proof (imp (bterm [] t0) (bterm [] (oterm (Can can3) []))) as dd2.
              autodimp dd2 hyp.
              pose proof (imp x (nobnd t1)) as dd3.
              autodimp dd3 hyp.
              pose proof (imp y (nobnd t2)) as dd4.
              autodimp dd4 hyp.
              clear imp.

              inversion dd1 as [? ? ? dd5]; subst; clear dd1.
              inversion dd2 as [? ? ? dd6]; subst; clear dd2.
              inversion dd3 as [? ? ? dd7]; subst; clear dd3.
              inversion dd4 as [? ? ? dd8]; subst; clear dd4.

              inversion dd6 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear dd6; cpx.
              allsimpl; clear imp1.

              repndors; exrepnd; subst;
              allrw @get_param_from_cop_some;
              subst; allsimpl.

              * exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                       (if Z_lt_le_dec n1 n2 then t1 else t2);
                  dands; eauto 3 with slow.
                { boolvar; eauto 3 with slow. }

              * exists (if param_kind_deq pk1 pk2 then t3 else t4)
                       (if param_kind_deq pk1 pk2 then t1 else t2);
                dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h.
                  unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto. }

                { boolvar; eauto 3 with slow. }

           + SSSSCase "NCan".
             rw @compute_step_ncompop_ncan2 in comp.
             dcwf h; allsimpl.
             remember (compute_step lib (oterm (NCan ncan3) bs1)) as comp1;
               symmetry in Heqcomp1.
             destruct comp1; ginv.

             pose proof (ind (oterm (NCan ncan3) bs1) (oterm (NCan ncan3) bs1) []) as h; clear ind.
             repeat (autodimp h hyp; tcsp); eauto 3 with slow.

             pose proof (h t0 b n) as k; clear h.
             repeat (autodimp k hyp).

             { apply wf_term_ncompop_iff in wft1; exrepnd; ginv; auto. }
             { apply wf_term_ncompop_iff in wft2; exrepnd; ginv; auto. }
             { simpl in i; simpl; introv j; apply i; allrw in_app_iff; sp. }

             exrepnd.

             exists (oterm (NCan (NCompOp c))
                           (bterm [] (oterm (Can can2) bs3)
                                  :: bterm [] t
                                  :: bs0))
                    (oterm (NCan (NCompOp c))
                           (bterm [] (oterm (Can can2) bs2)
                                  :: bterm [] u'
                                  :: bs)).
             dands; eauto 3 with slow.

             * apply reduce_to_prinargs_comp2; eauto 3 with slow; sp.
               apply co_wf_def_implies_iswfpk.
               eapply co_wf_def_len_implies;[|eauto];auto.

             * apply reduce_to_prinargs_comp2; eauto 3 with slow; sp.

             * unfold differ_alpha in k1; exrepnd.
               exists (oterm (NCan (NCompOp c))
                             (bterm [] (oterm (Can can2) bs3)
                                    :: bterm [] u1
                                    :: bs0))
                      (oterm (NCan (NCompOp c))
                             (bterm [] (oterm (Can can2) bs2)
                                    :: bterm [] u2
                                    :: bs)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n0;[|destruct n0]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n0;[|destruct n0]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ_oterm; simpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

           + SSSSCase "Exc".
             csunf comp; allsimpl; ginv.
             dcwf h; allsimpl; ginv.
             inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4; cpx.

             exists (oterm Exc bs4) (oterm Exc bs1); dands; eauto 3 with slow.
             apply reduces_to_if_step; csunf; simpl; dcwf h.

           + SSSSCase "Abs".
             rw @compute_step_ncompop_abs2 in comp.
             dcwf h; allsimpl.
             simpl in comp.
             remember (compute_step_lib lib abs3 bs1) as comp1;
               symmetry in Heqcomp1.
             destruct comp1; ginv.
             apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

             inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

             assert (differ_bterms b bs4 bs1) as dbs.
             { unfold differ_bterms, br_bterms, br_list; auto. }

             pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs1 correct bs4) as fe2.
             repeat (autodimp fe2 hyp).

             { apply differ_bterms_implies_eq_map_num_bvars in dbs; auto. }

             exists (oterm (NCan (NCompOp c))
                           (bterm [] (oterm (Can can2) bs3)
                                  :: bterm [] (mk_instance vars bs4 rhs)
                                  :: bs0))
             (oterm (NCan (NCompOp c))
                    (bterm [] (oterm (Can can2) bs2)
                           :: bterm [] (mk_instance vars bs1 rhs)
                           :: bs)).

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl; unfold on_success; csunf; simpl.
               dcwf h; allsimpl.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ_mk_instance b rhs vars bs4 bs1) as h.
               repeat (autodimp h hyp).
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ_alpha in h.
               exrepnd.

               exists
                 (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can can2) bs3)
                               :: bterm [] u1
                               :: bs0))
                 (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can can2) bs2)
                               :: bterm [] u2
                               :: bs)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ_oterm; allsimpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

          - SSSCase "NArithOp".
            destruct bs;[csunf comp; allsimpl; complete (dcwf h)|].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f|op bs1];
            try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; clear d.

            {
              csunf comp; simpl in comp.
              dcwf h; allsimpl.
              apply compute_step_arithop_success_can_can in comp; exrepnd; subst; GC.
              inversion d1 as [?|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear imp d1.
              allapply @get_param_from_cop_pki; subst; ginv.
              clear ind.

              exists (@mk_integer o n1) (@mk_integer o n1); dands; eauto 3 with slow.

              - allrw app_nil_r; allsimpl.
                fold_terms.
                apply (reduces_to_if_split2
                         _ _
                         (less_bound b (mk_integer n1) e)); simpl.

                + csunf; simpl.
                  unfold apply_bterm, lsubst; simpl; boolvar; tcsp.
                  * rw @lsubst_aux_trivial_cl_term; simpl; auto.
                    rw disjoint_singleton_r; auto.
                  * provefalse; allrw app_nil_r; sp.

                + apply (reduces_to_if_split2
                           _ _
                           (mk_less
                              (if Z_lt_le_dec n1 0 then mk_minus (mk_integer n1) else mk_integer n1)
                              (mk_nat b)
                              (mk_integer n1)
                              e)); try csunf; simpl; auto.

                  boolvar; tcsp.

                  * apply (reduces_to_if_split2
                             _ _
                             (mk_less
                                (mk_integer (- n1))
                                (mk_nat b)
                                (mk_integer n1)
                                e)); try csunf; simpl; auto.

                    apply reduces_to_if_step; simpl.
                    csunf; simpl.
                    dcwf h; allsimpl.
                    unfold compute_step_comp; simpl.

                    boolvar; tcsp.
                    provefalse.
                    pose proof (i n1) as h; clear i.
                    autodimp h hyp.

                    pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (- n1)) as k.
                    autodimp k hyp; try lia.

                  * apply reduces_to_if_step; simpl.
                    csunf; simpl.
                    dcwf h; allsimpl.
                    unfold compute_step_comp; simpl.

                    boolvar; tcsp.
                    pose proof (i n1) as h; clear i.
                    autodimp h hyp.
                    provefalse.

                    pose proof (Zabs.Zabs_nat_le (Z.of_nat b) n1) as k.
                    autodimp k hyp; try lia.

              - apply reduces_to_if_step; simpl.
                allrw <- Zplus_0_r_reverse; auto.
            }

            simpl in len.

            destruct bs0; simpl in len; cpx.
            destruct bs0; simpl in len; cpx.
            simpl in imp.

            pose proof (imp b0 (bterm [] (oterm (Can can2) bs2))) as d1.
            autodimp d1 hyp.
            pose proof (imp b1 (bterm [] (oterm op bs1))) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; simpl in comp.
              dcwf h; allsimpl.
              apply compute_step_arithop_success_can_can in comp.
              exrepnd; subst.

              destruct bs3; allsimpl; cpx; GC.

              clear imp1.

              inversion d4 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d4; cpx.
              clear imp1 imp.

              allapply @get_param_from_cop_pki; subst.

              exists (@mk_integer o (get_arith_op a n1 n2))
                     (@mk_integer o (get_arith_op a n1 n2));
                  dands; eauto 3 with slow.

           + SSSSCase "NCan".
             rw @compute_step_narithop_ncan2 in comp.
             dcwf h; allsimpl.
             remember (compute_step lib (oterm (NCan ncan3) bs1)) as comp1;
               symmetry in Heqcomp1.
             destruct comp1; ginv.

             pose proof (ind (oterm (NCan ncan3) bs1) (oterm (NCan ncan3) bs1) []) as h; clear ind.
             repeat (autodimp h hyp; tcsp); eauto 3 with slow.

             pose proof (h t0 b n) as k; clear h.
             repeat (autodimp k hyp).

             { apply wf_term_narithop_iff in wft1; exrepnd; ginv; auto. }
             { apply wf_term_narithop_iff in wft2; exrepnd; ginv; auto. }
             { simpl in i; simpl; introv j; apply i; allrw in_app_iff; sp. }

             exrepnd.

             exists (oterm (NCan (NArithOp a))
                           (bterm [] (oterm (Can can2) bs3)
                                  :: bterm [] t
                                  :: bs0))
                    (oterm (NCan (NArithOp a))
                           (bterm [] (oterm (Can can2) bs2)
                                  :: bterm [] u'
                                  :: bs)).
             dands; eauto 3 with slow.

             * apply reduce_to_prinargs_arith2; eauto 3 with slow; sp.
               allunfold @ca_wf_def; exrepnd; subst; allsimpl; cpx; fold_terms; eauto 3 with slow.

             * apply reduce_to_prinargs_arith2; eauto 3 with slow; sp.

             * unfold differ_alpha in k1; exrepnd.
               exists (oterm (NCan (NArithOp a))
                             (bterm [] (oterm (Can can2) bs3)
                                    :: bterm [] u1
                                    :: bs0))
                      (oterm (NCan (NArithOp a))
                             (bterm [] (oterm (Can can2) bs2)
                                    :: bterm [] u2
                                    :: bs)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n0;[|destruct n0]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n0;[|destruct n0]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ_oterm; simpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

           + SSSSCase "Exc".
             csunf comp; allsimpl; ginv.
             dcwf h; allsimpl; ginv.
             inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4; cpx.

             exists (oterm Exc bs4) (oterm Exc bs1); dands; eauto 3 with slow.
             apply reduces_to_if_step; csunf; allsimpl; dcwf h.

           + SSSSCase "Abs".
             rw @compute_step_narithop_abs2 in comp.
             dcwf h; allsimpl.
             remember (compute_step_lib lib abs3 bs1) as comp1;
               symmetry in Heqcomp1.
             destruct comp1; ginv.
             apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

             inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

             assert (differ_bterms b bs4 bs1) as dbs.
             { unfold differ_bterms, br_bterms, br_list; auto. }

             pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs1 correct bs4) as fe2.
             repeat (autodimp fe2 hyp).

             { apply differ_bterms_implies_eq_map_num_bvars in dbs; auto. }

             exists (oterm (NCan (NArithOp a))
                           (bterm [] (oterm (Can can2) bs3)
                                  :: bterm [] (mk_instance vars bs4 rhs)
                                  :: bs0))
             (oterm (NCan (NArithOp a))
                    (bterm [] (oterm (Can can2) bs2)
                           :: bterm [] (mk_instance vars bs1 rhs)
                           :: bs)).

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl.
               dcwf h; allsimpl.
               unfold on_success; csunf; simpl.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ_mk_instance b rhs vars bs4 bs1) as h.
               repeat (autodimp h hyp).
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ_alpha in h.
               exrepnd.

               exists
                 (oterm (NCan (NArithOp a))
                        (bterm [] (oterm (Can can2) bs3)
                               :: bterm [] u1
                               :: bs0))
                 (oterm (NCan (NArithOp a))
                        (bterm [] (oterm (Can can2) bs2)
                               :: bterm [] u2
                               :: bs)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ_oterm; allsimpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

          - SSSCase "NCanTest".
            csunf comp; allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; clear d.

            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx.
            destruct bs1; allsimpl; cpx; GC.

            pose proof (imp b0 (bterm [] (oterm (Can can2) bs2))) as d1.
            autodimp d1 hyp.
            pose proof (imp b1 (bterm [] arg2nt)) as d2.
            autodimp d2 hyp.
            pose proof (imp b2 (bterm [] arg3nt)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; simphyps; clear d4; cpx.

            exists (if canonical_form_test_for c can2 then t0 else t2)
                   (if canonical_form_test_for c can2 then arg2nt else arg3nt);
              dands; eauto 3 with slow.

            destruct (canonical_form_test_for c can2); eauto 3 with slow.
        }

        { SSCase "NCan".
          rw @compute_step_ncan_ncan in comp.
          remember (compute_step lib (oterm (NCan ncan2) bs2)) as comp1.
          symmetry in Heqcomp1; destruct comp1; ginv.

          inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; clear d.

          - pose proof (ind (oterm (NCan ncan2) bs2) (oterm (NCan ncan2) bs2) []) as h; clear ind.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.

            pose proof (h t0 b n) as k; clear h.
            repeat (autodimp k hyp); eauto 3 with slow.

            { apply wf_force_int_bound in wft1; sp. }
            { allunfold @nobnd; apply wf_term_narithop_iff in wft2; exrepnd; ginv; auto. }
            { simpl in i; simpl; introv j; apply i; allrw in_app_iff; sp. }

            exrepnd.

            exists (force_int_bound v b t e) (force_int u'); dands; tcsp.

            + apply reduces_to_prinarg; auto.

            + apply reduces_to_prinarg; auto.

            + apply implies_differ_alpha_force_int; auto.

          - pose proof (ind (oterm (NCan ncan2) bs2) (oterm (NCan ncan2) bs2) []) as h; clear ind.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.
            destruct bs1; cpx.
            simpl in len, imp.

            pose proof (imp b0 (bterm [] (oterm (NCan ncan2) bs2))) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (h t1 b n) as k; clear h.
            repeat (autodimp k hyp); eauto 3 with slow.

            { apply wf_oterm_iff in wft1; repnd; allsimpl.
              pose proof (wft1 (bterm [] t1)) as w; autodimp w hyp. }

            { apply wf_oterm_iff in wft2; repnd; allsimpl.
              pose proof (wft2 (bterm [] (oterm (NCan ncan2) bs2))) as w; autodimp w hyp. }

            { simpl in i; simpl.
              introv j; apply i; allrw in_app_iff; sp. }

            exrepnd.

            exists (oterm (NCan ncan) (nobnd t :: bs1))
                   (oterm (NCan ncan) (nobnd u' :: bs)); dands; auto.

            + apply reduces_to_prinarg; auto.

            + apply reduces_to_prinarg; auto.

            + unfold differ_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (nobnd u1 :: bs1))
                     (oterm (NCan ncan) (nobnd u2 :: bs)); dands; auto.

              * prove_alpha_eq4; introv k.
                destruct n0; cpx.
                apply alphaeqbt_nilv2; auto.

              * prove_alpha_eq4; introv k.
                destruct n0; cpx.
                apply alphaeqbt_nilv2; auto.

              * apply differ_oterm; simpl; auto.
                introv k; dorn k; cpx.
                constructor; auto.
        }

        { SSCase "Exc".
          csunf comp; allsimpl.
          apply compute_step_catch_success in comp.
          dorn comp; exrepnd; subst.

          - inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; clear d.
            allsimpl.
            cpx; allsimpl.

            pose proof (imp x (bterm [] (oterm Exc [bterm [] a', bterm [] e]))) as d1.
            autodimp d1 hyp.
            pose proof (imp y (bterm [] a)) as d2.
            autodimp d2 hyp.
            pose proof (imp z (bterm [v] b0)) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [? ? ? ? ni d1|?|?|? ? ? len1 imp1]; subst; clear d4.
            allsimpl; cpx; allsimpl.

            pose proof (imp1 x (bterm [] a')) as d1.
            autodimp d1 hyp.
            pose proof (imp1 y (bterm [] e)) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            exists (mk_atom_eq t0 t1 (subst t2 v t3) (mk_exception t1 t3))
                   (mk_atom_eq a a' (subst b0 v e) (mk_exception a' e));
              dands; eauto 3 with slow.

            apply differ_alpha_mk_atom_eq; eauto 3 with slow.

            { apply differ_subst; auto. }

            { apply differ_alpha_mk_exception; eauto 3 with slow. }

          - inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; clear d.

            + inversion d1 as [? ? ? ?|?|?|? ? ? len imp]; subst; clear d1.

              exists (oterm Exc bs1) (oterm Exc bs2); dands; eauto 3 with slow.

            + allsimpl.
              destruct bs1; allsimpl; cpx.
              pose proof (imp b0 (bterm [] (oterm Exc bs2))) as d1.
              autodimp d1 hyp.
              inversion d1 as [? ? ? d2]; subst; clear d1.
              inversion d2 as [? ? ? ?|?|?|? ? ? len1 imp1]; subst; clear d2.

              exists (oterm Exc bs0) (oterm Exc bs2); dands; eauto 3 with slow.
              apply reduces_to_if_step.
              csunf; simpl.
              unfold compute_step_catch.
              destruct ncan; tcsp.
        }

        { SSCase "Abs".
          csunf comp; allsimpl.
          unfold on_success in comp; csunf comp; allsimpl.
          remember (compute_step_lib lib abs2 bs2) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.
          apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

          inversion d as [? ? ? ? ni d1|?|?|? ? ? len imp]; subst; clear d.

          - inversion d1 as [|?|?|? ? ? len imp]; subst; clear d1.

            assert (differ_bterms b bs1 bs2) as dbs.
            { unfold differ_bterms, br_bterms, br_list; auto. }

            pose proof (found_entry_change_bs abs2 oa2 vars rhs lib bs2 correct bs1) as fe2.
            repeat (autodimp fe2 hyp).

            { apply differ_bterms_implies_eq_map_num_bvars in dbs; auto. }

            exists (force_int_bound v b (mk_instance vars bs1 rhs) e)
                   (force_int (mk_instance vars bs2 rhs)); dands; eauto 3 with slow.

            + apply reduces_to_if_step.
              csunf; simpl.
              unfold on_success; csunf; simpl.
              applydup @compute_step_lib_if_found_entry in fe2.
              rw fe0; auto.

            + pose proof (differ_mk_instance b rhs vars bs1 bs2) as h.
              repeat (autodimp h hyp).
              { allapply @found_entry_implies_matching_entry.
                allunfold @matching_entry; sp. }
              { allapply @found_entry_implies_matching_entry.
                allunfold @matching_entry; sp. }
              { allunfold @correct_abs; sp. }
              { allunfold @correct_abs; sp. }
               unfold differ_alpha in h.
              exrepnd.

              exists (force_int_bound v b u1 e) (force_int u2).
              dands; tcsp.

              * apply alpha_eq_force_int_bound; auto.

              * apply alpha_eq_force_int; auto.

          - allsimpl.
            destruct bs1; allsimpl; cpx.
            pose proof (imp b0 (bterm [] (oterm (Abs abs2) bs2))) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            inversion d2 as [|?|?|? ? ? len1 imp1]; subst; clear d2.

            assert (differ_bterms b bs0 bs2) as dbs.
            { unfold differ_bterms, br_bterms, br_list; auto. }

            pose proof (found_entry_change_bs abs2 oa2 vars rhs lib bs2 correct bs0) as fe2.
            repeat (autodimp fe2 hyp).

            { apply differ_bterms_implies_eq_map_num_bvars in dbs; auto. }

            exists (oterm (NCan ncan) (bterm [] (mk_instance vars bs0 rhs) :: bs1))
                   (oterm (NCan ncan) (bterm [] (mk_instance vars bs2 rhs) :: bs)).
            dands; eauto 3 with slow.

            + apply reduces_to_if_step.
              csunf; simpl.
              unfold on_success; csunf; simpl.
              applydup @compute_step_lib_if_found_entry in fe2.
              rw fe0; auto.

            + pose proof (differ_mk_instance b rhs vars bs0 bs2) as h.
              repeat (autodimp h hyp).
              { allapply @found_entry_implies_matching_entry.
                allunfold @matching_entry; sp. }
              { allapply @found_entry_implies_matching_entry.
                allunfold @matching_entry; sp. }
              { allunfold @correct_abs; sp. }
              { allunfold @correct_abs; sp. }
               unfold differ_alpha in h.
              exrepnd.

              exists (oterm (NCan ncan) (bterm [] u1 :: bs1))
                     (oterm (NCan ncan) (bterm [] u2 :: bs));
                dands; tcsp.

              * prove_alpha_eq4; introv k.
                destruct n; cpx.
                apply alphaeqbt_nilv2; auto.

              * prove_alpha_eq4; introv k.
                destruct n; cpx.
                apply alphaeqbt_nilv2; auto.

              * apply differ_oterm; simpl; auto.
                introv k; dorn k; cpx.
        }
      }

      { (* fresh case *)
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst; allsimpl.

        inversion d as [|?|?|? ? ? len1 imp1]; subst; clear d.
        allsimpl; cpx; allsimpl.
        pose proof (imp1 x (bterm [n] t2)) as d1.
        autodimp d1 hyp.
        clear imp1.
        inversion d1 as [? ? ? d2]; subst; clear d1.

        repndors; exrepnd; subst.

        - inversion d2; subst.
          exists (@mk_fresh o n (mk_var n)) (@mk_fresh o n (mk_var n)).
          dands; eauto 3 with slow.

        - applydup @differ_preserves_isvalue_like in d2; auto.
          exists (pushdown_fresh n t1) (pushdown_fresh n t2); dands; eauto 3 with slow.
          { apply reduces_to_if_step.
            apply compute_step_fresh_if_isvalue_like; auto. }
          { apply differ_alpha_pushdown_fresh_isvalue_like; auto. }

        - applydup @differ_preserves_isnoncan_like in d2; auto;[].
          allrw app_nil_r.

          pose proof (fresh_atom o (get_utokens t1 ++ get_utokens t2)) as fa; exrepnd.
          allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a.

          allrw @wf_fresh_iff.

          pose proof (compute_step_subst_utoken lib t2 x [(n,mk_utoken (get_fresh_atom t2))]) as comp'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp comp' hyp); try (apply get_fresh_atom_prop); eauto 3 with slow.
          { apply nr_ut_sub_cons; eauto 3 with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          pose proof (comp'0 [(n,mk_utoken a)]) as comp''; clear comp'0.
          allsimpl.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp comp'' hyp); exrepnd.

          pose proof (differ_subst b t1 t2 [(n, mk_utoken a)] [(n, mk_utoken a)]) as daeq.
          repeat (autodimp daeq hyp); eauto 3 with slow.
          unfold differ_alpha in daeq; exrepnd.

          pose proof (compute_step_alpha lib (lsubst t2 [(n, mk_utoken a)]) u2 s) as comp'''.
          repeat (autodimp comp''' hyp); exrepnd; eauto 4 with slow.
          rename t2' into s'.

          applydup @alphaeq_preserves_wf_term in daeq0;
            [|apply wf_term_subst; eauto 3 with slow].
          applydup @alphaeq_preserves_wf_term in daeq2;
            [|apply wf_term_subst; eauto 3 with slow].
          applydup @compute_step_preserves_wf in comp'''1; auto;[].
          applydup @alphaeq_preserves_wf_term_inv in comp'''0; auto;[].

          pose proof (ind t2 u2 [n]) as q; clear ind.
          repeat (autodimp q hyp).
          { apply alpha_eq_preserves_osize in daeq2; rw <- daeq2; allrw @fold_subst.
            rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (q u1 b s') as ih; clear q.
          repeat (autodimp ih hyp); fold_terms.
          { introv j; apply i.
            apply alpha_eq_preserves_get_ints in daeq2.
            unflsubst in daeq2.
            rw (get_ints_lsubst_aux_nr_ut t2 [(n, mk_utoken a)] mk_axiom) in daeq2; simpl; eauto 3 with slow.
            - rw daeq2; auto. }
          exrepnd.

          pose proof (reduces_to_alpha lib u1 (lsubst t1 [(n, mk_utoken a)]) t) as r1.
          repeat (autodimp r1 hyp); eauto 3 with slow.
          exrepnd.

          pose proof (reduces_to_change_utok_sub
                        lib t1 t2' [(n,mk_utoken a)] [(n,mk_utoken (get_fresh_atom t1))]) as r1'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp r1' hyp); try (apply get_fresh_atom_prop); eauto 3 with slow.
          { apply nr_ut_sub_cons; eauto 3 with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          allrw disjoint_singleton_l.
          fold_terms; allrw @fold_subst.

          pose proof (reduces_to_fresh lib t1 s0 n) as q; simpl in q.
          repeat (autodimp q hyp).
          exrepnd.

          (* 1st exists *)
          exists (mk_fresh n z).

          assert (!LIn a (get_utokens w)) as niaw.
          { intro k; apply comp'4 in k; sp. }

          pose proof (alpha_eq_subst_utokens
                        x (subst w n (mk_utoken (get_fresh_atom t2)))
                        [(get_fresh_atom t2, mk_var n)]
                        [(get_fresh_atom t2, mk_var n)]) as aeqs.
          repeat (autodimp aeqs hyp); eauto 3 with slow.
          pose proof (simple_alphaeq_subst_utokens_subst
                        w n (get_fresh_atom t2)) as aeqs1.
          autodimp aeqs1 hyp.
          eapply alpha_eq_trans in aeqs1;[|exact aeqs]; clear aeqs.

          pose proof (reduces_to_alpha lib s' (subst w n (mk_utoken a)) u') as raeq.
          repeat (autodimp raeq hyp); eauto 3 with slow; exrepnd;[].
          rename t2'0 into u''.

          assert (wf_term w) as wfw.
          { allrw @wf_fresh_iff.
            apply compute_step_preserves_wf in comp2;
              [|apply wf_term_subst;eauto 3 with slow].
            apply alphaeq_preserves_wf_term in comp'1; auto.
            apply lsubst_wf_term in comp'1; auto.
          }

          pose proof (reduces_to_fresh2 lib w u'' n a) as rf.
          repeat (autodimp rf hyp); exrepnd.

          pose proof (reduces_to_alpha
                        lib
                        (mk_fresh n w)
                        (mk_fresh n (subst_utokens x [(get_fresh_atom t2, mk_var n)]))
                        (mk_fresh n z0)) as r'.
          repeat (autodimp r' hyp).
          { apply nt_wf_fresh; eauto 3 with slow. }
          { apply implies_alpha_eq_mk_fresh; eauto 3 with slow. }
          exrepnd.
          rename t2'0 into f'.

          (* 2nd exists *)
          exists f'; dands; auto.
          eapply differ_alpha_r;[|exact r'0].
          apply differ_alpha_mk_fresh.
          eapply differ_alpha_r;[|apply alpha_eq_sym in rf0; exact rf0].
          eapply differ_alpha_l;[exact q0|].
          eapply differ_alpha_r;[|apply alpha_eq_subst_utokens_same; exact raeq0].
          eapply differ_alpha_l;[apply alpha_eq_subst_utokens_same;exact r1'1|].

          pose proof (simple_alphaeq_subst_utokens_subst w0 n (get_fresh_atom t1)) as aeqsu.
          autodimp aeqsu hyp.
          { intro j; apply r1'4 in j; apply get_fresh_atom_prop in j; sp. }

          eapply differ_alpha_l;[exact aeqsu|];clear aeqsu.

          apply (alpha_eq_subst_utokens_same _ _ [(a, mk_var n)]) in r1'0.
          pose proof (simple_alphaeq_subst_utokens_subst w0 n a) as aeqsu.
          autodimp aeqsu hyp.

          eapply differ_alpha_l;[apply alpha_eq_sym; exact aeqsu|];clear aeqsu.
          eapply differ_alpha_l;[apply alpha_eq_sym; exact r1'0|].
          eapply differ_alpha_l;[apply alpha_eq_subst_utokens_same; apply alpha_eq_sym; exact r0|].
          apply differ_alpha_subst_utokens; auto.
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.
      inversion d as [|?|?|? ? ? len1 imp1]; subst; clear d.
      exists (oterm Exc bs1) (oterm Exc bs); dands; eauto 3 with slow.

    + SCase "Abs".
      csunf comp; allsimpl.
      apply compute_step_lib_success in comp; exrepnd; subst.

      inversion d as [|?|?|? ? ? len imp]; subst; clear d.

      assert (differ_bterms b bs1 bs) as dbs.
      { unfold differ_bterms, br_bterms, br_list; auto. }

      pose proof (found_entry_change_bs abs oa2 vars rhs lib bs correct bs1) as fe2.
      repeat (autodimp fe2 hyp).

      { apply differ_bterms_implies_eq_map_num_bvars in dbs; auto. }

      exists (mk_instance vars bs1 rhs)
             (mk_instance vars bs rhs).
      dands; eauto 3 with slow.

      * apply reduces_to_if_step.
        csunf; simpl.
        unfold on_success.
        applydup @compute_step_lib_if_found_entry in fe2.
        rw fe0; auto.

      * pose proof (differ_mk_instance b rhs vars bs1 bs) as h.
        repeat (autodimp h hyp).
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allunfold @correct_abs; sp. }
        { allunfold @correct_abs; sp. }
Qed.

Fixpoint get_ints_from_comp_at_most_k_steps {o}
           (lib : @library o)
           (t : @NTerm o)
           (k : nat) : list Z :=
  match k with
    | 0 => []
    | S n =>
      get_ints t
               ++ match compute_step lib t with
                    | csuccess u => get_ints_from_comp_at_most_k_steps lib u n
                    | cfailure _ _ => []
                  end
  end.

Lemma implies_reduces_in_atmost_k_steps_S {o} :
  forall (lib : library) (t v : @NTerm o) (k : nat),
    reduces_in_atmost_k_steps lib t v (S k)
    -> {u : NTerm
        & compute_step lib t = csuccess u
        # reduces_in_atmost_k_steps lib u v k}.
Proof.
  introv comp.
  apply reduces_in_atmost_k_steps_S; auto.
Qed.

Fixpoint get_ints_from_red_atmost {o}
           (lib : @library o)
           (t u : @NTerm o)
           (k : nat) : reduces_in_atmost_k_steps lib t u k -> list Z :=
  match k with
    | 0 => fun comp => get_ints t
    | S n =>
      fun comp =>
        get_ints t
                 ++ match implies_reduces_in_atmost_k_steps_S lib t u n comp with
                      | existT _ w (c,r) => get_ints_from_red_atmost lib w u n r
                    end
  end.

Definition get_ints_from_computation {o}
           (lib : @library o)
           (t u : @NTerm o)
           (comp : reduces_to lib t u) : list Z :=
  match comp with
    | existT _ k r => get_ints_from_red_atmost lib t u k r
  end.

Lemma get_ints_from_red_atmost_head {o} :
  forall lib k (t1 t2 : @NTerm o) z
         (c : reduces_in_atmost_k_steps lib t1 t2 k),
    LIn z (get_ints t1)
    -> LIn z (get_ints_from_red_atmost lib t1 t2 k c).
Proof.
  induction k; introv i; allsimpl.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    remember (implies_reduces_in_atmost_k_steps_S lib t1 t2 k c) as s.
    exrepnd.
    clear Heqs c.
    rw in_app_iff; sp.
Qed.

Lemma get_ints_from_red_atmost_head_if_isvalue_like {o} :
  forall lib k (t1 t2 : @NTerm o) z
         (c : reduces_in_atmost_k_steps lib t1 t2 k),
    isvalue_like t1
    -> LIn z (get_ints_from_red_atmost lib t1 t2 k c)
    -> LIn z (get_ints t1).
Proof.
  induction k; introv iv i; allsimpl.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    remember (implies_reduces_in_atmost_k_steps_S lib t1 t2 k c) as s.
    exrepnd.
    clear Heqs c.
    allrw in_app_iff; dorn i; tcsp.
    rw @compute_step_value_like in s1; auto; ginv.
    apply IHk in i; auto.
Qed.

Lemma get_ints_from_red_atmost_isvalue_like_diff_num_steps {o} :
  forall lib k1 k2 (t : @NTerm o) v z
         (c1 : reduces_in_atmost_k_steps lib t v k1)
         (c2 : reduces_in_atmost_k_steps lib t v k2),
    isvalue_like v
    -> LIn z (get_ints_from_red_atmost lib t v k1 c1)
    -> LIn z (get_ints_from_red_atmost lib t v k2 c2).
Proof.
  induction k1; introv iv i; allsimpl.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    apply get_ints_from_red_atmost_head; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    remember (implies_reduces_in_atmost_k_steps_S lib t v k1 c1) as s.
    exrepnd.
    clear Heqs c1.
    allrw in_app_iff; dorn i.
    + apply get_ints_from_red_atmost_head; auto.
    + destruct k2; allsimpl.
      * allrw @reduces_in_atmost_k_steps_0; subst.
        rw @compute_step_value_like in s1; auto; ginv.
        apply get_ints_from_red_atmost_head_if_isvalue_like in i; auto.
      * remember (implies_reduces_in_atmost_k_steps_S lib t v k2 c2) as p.
        exrepnd.
        clear Heqp c2.
        rw p1 in s1; ginv.
        rw in_app_iff.
        pose proof (IHk1 k2 u v z s0 p0 iv); sp.
Qed.

Lemma get_ints_from_red_atmost_if_reduces_to {o} :
  forall lib k1 k2 (t1 t2 v : @NTerm o) z
         (c1 : reduces_in_atmost_k_steps lib t1 v k1)
         (c2 : reduces_in_atmost_k_steps lib t2 v k2),
    reduces_to lib t1 t2
    -> isvalue_like v
    -> LIn z (get_ints_from_red_atmost lib t2 v k2 c2)
    -> LIn z (get_ints_from_red_atmost lib t1 v k1 c1).
Proof.
  introv r hv i.
  unfold reduces_to in r; exrepnd.
  revert k1 k2 t1 t2 c1 c2 hv r0 i.
  induction k; introv hv r i.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    eapply get_ints_from_red_atmost_isvalue_like_diff_num_steps; eauto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct k1; allsimpl.
    + allrw @reduces_in_atmost_k_steps_0; subst.
      rw @compute_step_value_like in r1; auto; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; auto; subst.
      apply get_ints_from_red_atmost_head_if_isvalue_like in i; auto.
    + remember (implies_reduces_in_atmost_k_steps_S lib t1 v k1 c1) as s.
      exrepnd.
      clear Heqs c1.
      rw s1 in r1; ginv.
      allrw in_app_iff.
      pose proof (IHk k1 k2 u t2 s0 c2) as h.
      repeat (autodimp h hyp).
Qed.

Lemma get_ints_swap {o} :
  forall s (t : @NTerm o),
    get_ints (swap s t) = get_ints t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; allsimpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_ints_cswap {o} :
  forall s (t : @NTerm o),
    get_ints (cswap s t) = get_ints t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; allsimpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_ints_alpha_eq {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_ints t1 = get_ints t2.
Proof.
  nterm_ind1s t1 as [v|f ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "sterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    inversion aeq as [|?|? ? ? len imp]; subst.
    clear len imp.
    apply alpha_eq_oterm_combine in aeq; repnd; allsimpl.
    apply app_if; auto.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup aeq in i.
    applydup in_combine in i; repnd.
    destruct t1 as [l1 t1].
    destruct t2 as [l2 t2]; simpl.
    apply alphaeqbt_eq in i0.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst; allsimpl; clear i0.

    pose proof (ind t1 (cswap (mk_swapping l1 vs) t1) l1) as h.
    repeat (autodimp h hyp).
    { rw @osize_cswap; eauto 3 with slow. }

    apply alphaeq_eq in a.
    apply h in a; clear h.
    allrw @get_ints_cswap; auto.
Qed.

Lemma get_ints_from_red_atmost_alpha_eq {o} :
  forall lib k (t1 t2 t : @NTerm o)
         (c1 : reduces_in_atmost_k_steps lib t1 t k)
         (c2 : reduces_in_atmost_k_steps lib t2 t k),
    nt_wf t1
    -> alpha_eq t1 t2
    -> get_ints_from_red_atmost lib t1 t k c1
       = get_ints_from_red_atmost lib t2 t k c2.
Proof.
  induction k; introv wf aeq; allsimpl.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - remember (implies_reduces_in_atmost_k_steps_S lib t1 t k c1) as s.
    exrepnd.
    clear Heqs c1.
    remember (implies_reduces_in_atmost_k_steps_S lib t2 t k c2) as p.
    exrepnd.
    clear Heqp c2.
    applydup @preserve_nt_wf_compute_step in s1; auto.
    apply app_if.
    + apply get_ints_alpha_eq; auto.
    + pose proof (compute_step_alpha lib t1 t2 u wf aeq s1) as h; exrepnd.
      rw h1 in p1; ginv.
Qed.

Lemma comp_force_int {o} :
  forall lib (t2 t1 : @NTerm o) b z
         (comp : reduces_to lib t2 (mk_integer z)),
    wf_term t1
    -> wf_term t2
    -> differ b t1 t2
    -> (forall i,
          LIn i (get_ints_from_computation lib t2 (mk_integer z) comp)
          -> Z.abs_nat i < b)
    -> reduces_to lib t1 (mk_integer z).
Proof.
  introv w1 w2 d i.
  unfold reduces_to in comp; exrepnd.
  unfold get_ints_from_computation in i.
  revert dependent t1.
  revert dependent t2.
  induction k as [n ind] using comp_ind_type; introv w2 i w1 d.
  destruct n as [|k]; allsimpl.

  - rw @reduces_in_atmost_k_steps_0 in comp0; subst.
    inversion d as [|?|?|? ? ? len imp]; subst; clear d.
    allsimpl; cpx; eauto 3 with slow.

  - remember (implies_reduces_in_atmost_k_steps_S lib t2 (mk_integer z) k comp0) as s.
    exrepnd.
    clear Heqs comp0.

    pose proof (comp_force_int_step lib t2 t1 b u) as h.
    repeat (autodimp h hyp).

    { introv j; apply i; rw in_app_iff; sp. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to
                  lib k u u' (mk_integer z)) as h'.
    repeat (autodimp h' hyp).
    { left; sp. }
    exrepnd.

    unfold differ_alpha in h1; exrepnd.

    applydup @preserve_nt_wf_compute_step in s1; eauto 3 with slow.
    applydup @reduces_to_preserves_wf in h2; eauto 3 with slow.
    applydup @reduces_to_preserves_wf in h0; eauto 3 with slow.
    applydup @alphaeq_preserves_wf_term in h4; eauto 3 with slow.
    applydup @alphaeq_preserves_wf_term in h3; eauto 3 with slow.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u' u2) as h''.
    repeat (autodimp h'' hyp); eauto 3 with slow.
    pose proof (h'' k' (mk_integer z)) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.
    inversion h'''0 as [|?|? ? ? ? x]; subst; allsimpl; cpx;
    clear x h'''0.
    fold_terms.

    pose proof (ind k') as h.
    autodimp h hyp;[lia|].
    pose proof (h u2 h'''1) as r; clear h.
    repeat (autodimp r hyp).

    { introv j.
      apply i.
      rw in_app_iff; right.
      pose proof (get_ints_from_red_atmost_if_reduces_to
                    lib k k' u u' (mk_integer z) i0 s0 h'0) as h.
      repeat (autodimp h hyp); eauto 3 with slow.
      erewrite @get_ints_from_red_atmost_alpha_eq; eauto 3 with slow. }

    pose proof (r u1) as h; clear r; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (reduces_to_steps_alpha lib u1 t (mk_integer z)) as a.
    repeat (autodimp a hyp); eauto 3 with slow.
    exrepnd.
    inversion a0; subst; allsimpl; cpx; fold_terms.
    eapply reduces_to_trans; eauto.
Qed.

Lemma old_differ_app_F {o} :
  forall (F f e : @NTerm o) v x b,
    !LIn v (free_vars e)
    -> differ
         b
         (mk_apply F (mk_lam x (mk_apply f (force_int_bound v b (mk_var x) e))))
         (mk_apply F (mk_lam x (mk_apply f (force_int (mk_var x))))).
Proof.
  introv ni.
  constructor; simpl; auto.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto 3 with slow.
  - constructor; constructor; simpl; auto.
    introv i; dorn i; cpx.
    constructor; constructor; simpl; auto.
    introv i; dorn i;[|dorn i]; cpx; auto.
    + constructor; eauto 3 with slow.
    + constructor; constructor; auto.
Qed.

Lemma differ_app_F {o} :
  forall (F f e : @NTerm o) v b,
    !LIn v (free_vars e)
    -> differ b (force_int_bound_F v b F f e) (force_int_F v F f).
Proof.
  introv ni.
  constructor; simpl; auto.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto 3 with slow.
  - constructor; constructor; simpl; auto.
    introv i; dorn i; cpx.
    constructor; constructor; simpl; auto.
    introv i; dorn i;[|dorn i]; cpx; auto.
    + constructor; eauto 3 with slow.
    + constructor; constructor; auto.
      introv i; allsimpl; dorn i;[|dorn i]; cpx.
      * constructor; eauto 3 with slow.
      * constructor; constructor.
Qed.

Fixpoint bigger_Z (l : list Z) : nat :=
  match l with
    | [] => 0
    | x :: xs =>
      let n := bigger_Z xs in
      if le_lt_dec n (Z.abs_nat x)
      then (Z.abs_nat x) + 1
      else n
  end.

Lemma bigger_Z_is_bigger :
  forall z (l : list Z), LIn z l -> Z.abs_nat z < bigger_Z l.
Proof.
  induction l; introv i; allsimpl; tcsp.
  dorn i; subst; boolvar; try lia.
  - autodimp IHl hyp; lia.
  - autodimp IHl hyp; lia.
Qed.

Lemma exists_bigger_than_list_Z :
  forall (l : list Z),
    {n : nat & forall z, LIn z l -> Z.abs_nat z < n}.
Proof.
  introv.
  exists (bigger_Z l).
  introv i.
  apply bigger_Z_is_bigger; auto.
Qed.

(*

  F (\x.let x:=(x+0) in f(x)) -> z
  =>
  exists b.
    F (\x.let x:=(let x:=x in if |x|<b then x else e) in f(x)) -> z

*)
Lemma comp_force_int_app_F {o} :
  forall lib (F f : @NTerm o) x z,
    wf_term F
    -> wf_term f
    -> reduces_to
         lib
         (force_int_F x F f)
         (mk_integer z)
    -> {b : nat
        & forall e b',
            wf_term e
            -> !LIn x (free_vars e)
            -> b <= b'
            -> reduces_to
                 lib
                 (force_int_bound_F x b' F f e)
                 (mk_integer z)}.
Proof.
  introv wF wf r.

  pose proof (exists_bigger_than_list_Z
                (get_ints_from_computation
                   lib
                   (force_int_F x F f)
                   (mk_integer z)
                   r)) as h; exrepnd.

  exists n.
  introv we ni l.

  pose proof (comp_force_int
                lib
                (force_int_F x F f)
                (force_int_bound_F x b' F f e)
                b' z r
                (wf_term_force_int_bound_F_if x b' F f e wF wf we)
                (wf_term_force_int_F_if x F f wF wf)
                (differ_app_F F f e x b' ni)) as c.
  autodimp c hyp.
  introv j.
  apply h0 in j; lia.
Qed.
