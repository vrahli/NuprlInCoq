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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export continuity_defs.
Require Export atoms2.


Inductive differ3 {o} (b : nat) (a : get_patom_set o) (f g : NTerm)
: @NTerm o -> @NTerm o -> Type :=
| differ3_force_int :
    forall t1 t2 v fa ga,
      !LIn v (free_vars f)
      -> !LIn v (free_vars g)
      -> differ3 b a f g t1 t2
      -> alpha_eq f fa
      -> alpha_eq g ga
      -> differ3
           b a f g
           (force_int_bound_app v b t1 fa (uexc a))
           (force_int_bound_app v b t2 ga (uexc a))
| differ3_var :
    forall v, differ3 b a f g (mk_var v) (mk_var v)
| differ3_oterm :
    forall op bs1 bs2,
      !LIn a (get_utokens_o op)
      -> length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> differ3_b b a f g b1 b2)
      -> differ3 b a f g (oterm op bs1) (oterm op bs2)
with differ3_b {o} (b : nat) (a : get_patom_set o) (f g : NTerm)
     : @BTerm o -> @BTerm o -> Type :=
     | differ3_bterm :
         forall vs t1 t2,
           disjoint vs (free_vars f)
           -> disjoint vs (free_vars g)
           -> differ3 b a f g t1 t2
           -> differ3_b b a f g (bterm vs t1) (bterm vs t2).
Hint Constructors differ3 differ3_b.

Definition differ3_alpha {o} b a f g (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
      & alpha_eq t1 u1
      # alpha_eq t2 u2
      # differ3 b a f g u1 u2}}.

Definition differ3_implies_differ3_alpha {o} :
  forall b a f g (t1 t2 : @NTerm o),
    differ3 b a f g t1 t2 -> differ3_alpha b a f g t1 t2.
Proof.
  introv d.
  exists t1 t2; auto.
Qed.
Hint Resolve differ3_implies_differ3_alpha : slow.

Inductive differ3_subs {o} b a f g : @Sub o -> @Sub o -> Type :=
| dsub3_nil : differ3_subs b a f g [] []
| dsub3_cons :
    forall v t1 t2 sub1 sub2,
      differ3 b a f g t1 t2
      -> differ3_subs b a f g sub1 sub2
      -> differ3_subs b a f g ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors differ3_subs.

Definition differ3_bterms {o} b a f g (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ3_b b a f g) bs1 bs2.

Lemma differ3_subs_sub_find_some {o} :
  forall b a f g (sub1 sub2 : @Sub o) v t,
    differ3_subs b a f g sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # differ3 b a f g t u}.
Proof.
  induction sub1; destruct sub2; introv d fs; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma differ3_subs_sub_find_none {o} :
  forall b a f g (sub1 sub2 : @Sub o) v,
    differ3_subs b a f g sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d fn; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma differ3_subs_filter {o} :
  forall b a f g (sub1 sub2 : @Sub o) l,
    differ3_subs b a f g sub1 sub2
    -> differ3_subs b a f g (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.

Lemma differ3_force_int_bound {o} :
  forall b a f g v b' (t1 t2 : @NTerm o) e1 e2,
    !LIn v (free_vars f)
    -> !LIn v (free_vars g)
    -> differ3 b a f g t1 t2
    -> differ3 b a f g e1 e2
    -> differ3 b a f g
               (force_int_bound v b' t1 e1)
               (force_int_bound v b' t2 e2).
Proof.
  introv nif nig d1 d2.
  apply differ3_oterm; simpl; tcsp.
  introv i; repndors; cpx; tcsp.
  - constructor; auto.
  - constructor; allrw disjoint_singleton_l; auto.
    constructor; simpl; tcsp.
    introv i; repndors; cpx; tcsp.
    + constructor; allsimpl; auto.
      constructor; simpl; tcsp.
      introv i; repndors; cpx; tcsp.
      * constructor; auto.
      * constructor; auto.
        constructor; simpl; tcsp.
      * constructor; auto.
        constructor; simpl; tcsp.
        introv i; repndors; cpx; tcsp.
        constructor; auto; constructor.
      * constructor; auto; constructor.
    + constructor; auto; constructor; simpl; tcsp.
    + constructor; auto; constructor.
    + constructor; auto.
Qed.
Hint Resolve differ3_force_int_bound : slow.

Lemma alpha_eq_force_int_bound_app {o} :
  forall b v1 v2 (t1 t2 f1 f2 e1 e2 : @NTerm o),
    !LIn v1 (free_vars e1)
    -> !LIn v2 (free_vars e2)
    -> !LIn v1 (free_vars f1)
    -> !LIn v2 (free_vars f2)
    -> alpha_eq t1 t2
    -> alpha_eq e1 e2
    -> alpha_eq f1 f2
    -> alpha_eq
         (force_int_bound_app v1 b t1 f1 e1)
         (force_int_bound_app v2 b t2 f2 e2).
Proof.
  introv ni1 ni2 ni3 ni4 aeq1 aeq2 aeq3.
  unfold force_int_bound_app, mk_cbv, mk_less.
  prove_alpha_eq4.
  introv i.
  destruct n;[|destruct n]; try lia.

  - apply alphaeqbt_nilv2; auto.
    apply alpha_eq_force_int_bound; auto.

  - pose proof (ex_fresh_var
                  ([v1,v2]
                     ++ all_vars f1
                     ++ all_vars f2
               )) as h; exrepnd.
    allunfold @all_vars; allsimpl.
    allsimpl; allrw app_nil_r; allrw remove_nvars_nil_l.
    allrw in_app_iff; allsimpl; allrw in_app_iff.
    allrw not_over_or; repnd; GC.

    apply (al_bterm _ _ [v]); simpl; auto.

    + unfold all_vars; simpl.
      allrw remove_nvars_nil_l; allrw app_nil_r.
      rw disjoint_singleton_l; simpl.
      allrw in_app_iff; simpl; allrw in_app_iff; sp.

    + unfold lsubst; simpl; boolvar; allrw app_nil_r;
      allrw disjoint_singleton_r; tcsp.
      prove_alpha_eq4.
      introv j.
      destruct n;[|destruct n;[|destruct n;[|destruct n]]];
      try lia; eauto with slow.

      apply alphaeqbt_nilv2; auto.
      repeat (rw @lsubst_aux_trivial_cl_term); auto; simpl;
      allrw disjoint_singleton_r; auto.
Qed.

Lemma differ3_lsubst_aux {o} :
  forall b a f g (t1 t2 : @NTerm o) sub1 sub2,
    disjoint (free_vars f) (dom_sub sub1)
    -> disjoint (free_vars g) (dom_sub sub2)
    -> differ3 b a f g t1 t2
    -> differ3_subs b a f g sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> differ3 b a f g (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v|op bs ind] Case;
  introv clf clg dt ds disj1 disj2; allsimpl.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ3_subs_sub_find_some b a f g sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ3_subs_sub_find_none b a f g sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "oterm".
    inversion dt as [? ? ? ? ? ni1 ni2 d1 aeq1 aeq2|?|? ? ? ni len imp]; subst; allsimpl.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      allrw @sub_find_sub_filter; tcsp.
      fold_terms.
      apply differ3_force_int; auto.

      * apply (ind (force_int_bound v b t1 (uexc a)) t1 []); simpl; auto; try lia.

      * rw @lsubst_aux_trivial_cl_term; auto.
        apply alphaeq_preserves_free_vars in aeq1; rw <- aeq1; auto.
        rw <- @dom_sub_sub_filter.
        eapply subvars_disjoint_r;[|exact clf].
        apply subvars_remove_nvars; apply subvars_app_weak_l; auto.

      * rw @lsubst_aux_trivial_cl_term; auto.
        apply alphaeq_preserves_free_vars in aeq2; rw <- aeq2; auto.
        rw <- @dom_sub_sub_filter.
        eapply subvars_disjoint_r;[|exact clg].
        apply subvars_remove_nvars; apply subvars_app_weak_l; auto.

    + apply differ3_oterm; allrw map_length; auto.

      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      applydup imp in i1.
      destruct a1 as [l1 t1].
      destruct a0 as [l2 t2].
      applydup in_combine in i1; repnd.
      allsimpl.
      inversion i0 as [? ? ? df dg d]; subst; clear i0.
      constructor; auto.
      apply (ind t1 t1 l2); auto.

      * rw <- @dom_sub_sub_filter.
        eapply subvars_disjoint_r;[|exact clf].
        apply subvars_remove_nvars; apply subvars_app_weak_l; auto.

      * rw <- @dom_sub_sub_filter.
        eapply subvars_disjoint_r;[|exact clg].
        apply subvars_remove_nvars; apply subvars_app_weak_l; auto.

      * apply differ3_subs_filter; auto.

      * pose proof (subvars_sub_free_vars_sub_filter sub1 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.

      * pose proof (subvars_sub_free_vars_sub_filter sub2 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.
Qed.

Lemma differ3_refl {o} :
  forall b a f g (t : @NTerm o),
    !LIn a (get_utokens t)
    -> disjoint (bound_vars t) (free_vars f)
    -> disjoint (bound_vars t) (free_vars g)
    -> differ3 b a f g t t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv ni df dg; allsimpl; auto.

  Case "oterm".
  allrw in_app_iff; allrw not_over_or; repnd.
  apply differ3_oterm; auto.
  introv i.
  rw in_combine_same in i; repnd; subst.
  destruct b2 as [l t].
  disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.
  constructor; auto.
  eapply ind; eauto.
  intro k.
  destruct ni.
  rw lin_flat_map; eexists; eauto.
Qed.
Hint Resolve differ3_refl : slow.

Lemma differ3_subs_refl {o} :
  forall b a f g (sub : @Sub o),
    !LIn a (get_utokens_sub sub)
    -> disjoint (sub_bound_vars sub) (free_vars f)
    -> disjoint (sub_bound_vars sub) (free_vars g)
    -> differ3_subs b a f g sub sub.
Proof.
  induction sub; introv df dg ni; allsimpl; auto.
  destruct a0; allrw @get_utokens_sub_cons; allrw in_app_iff; allrw not_over_or; repnd.
  allrw disjoint_app_l; repnd.
  constructor; eauto with slow.
Qed.
Hint Resolve differ3_subs_refl : slow.

Lemma differ3_change_bound_vars {o} :
  forall b a f g vs (t1 t2 : @NTerm o),
    differ3 b a f g t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
           & differ3 b a f g u1 u2
           # alpha_eq t1 u1
           # alpha_eq t2 u2
           # disjoint (bound_vars u1) vs
           # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind1s t1 as [v|op bs ind] Case; introv (*clf clg*) d.

  - Case "vterm".
    inversion d; subst.
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto with slow.

  - Case "oterm".
    inversion d as [? ? ? ? ? ni1 ni2 d1 a1 a2|?|? ? ? ni len imp]; subst; simphyps; cpx; ginv; clear d.

    + pose proof (ex_fresh_var (vs ++ free_vars f ++ free_vars g)) as h; exrepnd.
      allrw in_app_iff; allrw not_over_or; repnd.
      pose proof (ind (force_int_bound v b t1 (uexc a)) t1 []) as h; clear ind.
      repeat (autodimp h hyp).
      { simpl; lia. }
      pose proof (h t0 (*clf clg*) d1) as k; clear h.
      exrepnd.

      fold_terms.

      pose proof (change_bvars_alpha_spec fa vs) as p1.
      remember (change_bvars_alpha vs fa) as fa1; clear Heqfa1; simpl in p1.
      pose proof (change_bvars_alpha_spec ga vs) as p2.
      remember (change_bvars_alpha vs ga) as ga1; clear Heqga1; simpl in p2.
      repnd.

      exists
        (force_int_bound_app v0 b u1 fa1 (uexc a))
        (force_int_bound_app v0 b u2 ga1 (uexc a)).
      dands; eauto with slow.

      * apply alpha_eq_force_int_bound_app; simpl; tcsp.
        { apply alphaeq_preserves_free_vars in a1; rw <- a1; auto. }
        { apply alphaeq_preserves_free_vars in p1; rw <- p1; auto.
          apply alphaeq_preserves_free_vars in a1; rw <- a1; auto. }

      * apply alpha_eq_force_int_bound_app; simpl; tcsp.
        { apply alphaeq_preserves_free_vars in a2; rw <- a2; auto. }
        { apply alphaeq_preserves_free_vars in p2; rw <- p2; auto.
          apply alphaeq_preserves_free_vars in a2; rw <- a2; auto. }

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; rw disjoint_cons_l; rw disjoint_app_l; rw disjoint_singleton_l.
        dands; eauto with slow.

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; rw disjoint_cons_l; rw disjoint_app_l; rw disjoint_singleton_l.
        dands; eauto with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
                  & alpha_eq_bterms bs bs'
                  # alpha_eq_bterms bs2 bs2'
                  # differ3_bterms b a f g bs' bs2'
                  # disjoint (flat_map bound_vars_bterm bs') vs
                  # disjoint (flat_map bound_vars_bterm bs2') vs}}) as h.

      { revert dependent bs2.
        induction bs; destruct bs2; introv len imp; allsimpl; ginv.
        - exists ([] : list (@BTerm o)) ([] : list (@BTerm o));
            dands; simpl; eauto with slow; try (apply br_bterms_nil).
        - cpx.
          destruct a0 as [l1 t1].
          destruct b0 as [l2 t2].
          pose proof (imp (bterm l1 t1) (bterm l2 t2)) as h; autodimp h hyp.
          inversion h as [? ? ? df dg d1]; subst; clear h.
          pose proof (ind t1 t1 l2) as h; repeat (autodimp h hyp).
          pose proof (h t2 (*clf clg*) d1) as k; clear h.
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
                           ++ all_vars f
                           ++ all_vars g
                        )) as fv; exrepnd.
          allrw disjoint_app_r; repnd.

          exists ((bterm lvn (lsubst_aux u1 (var_ren l2 lvn))) :: bs')
                 ((bterm lvn (lsubst_aux u2 (var_ren l2 lvn))) :: bs2');
            dands; simpl;
            try (apply br_bterms_cons);
            try (apply alpha_eq_bterm_congr);
            tcsp.
          { apply alpha_bterm_change_aux; eauto with slow.
            allrw disjoint_app_l; dands; eauto with slow. }
          { apply alpha_bterm_change_aux; eauto with slow.
            allrw disjoint_app_l; dands; eauto with slow. }
          { apply differ3_bterm; auto.
            apply differ3_lsubst_aux; eauto with slow;
            try (rw @sub_free_vars_var_ren; eauto with slow);
            try (rw @dom_sub_var_ren; eauto with slow).
            apply differ3_subs_refl; simpl;
            try (rw @sub_bound_vars_var_ren; auto).
            rw @get_utokens_sub_var_ren; simpl; tcsp. }
          { allrw disjoint_app_l; dands; eauto with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u1 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
          { allrw disjoint_app_l; dands; eauto with slow.
            pose proof (subvars_bound_vars_lsubst_aux
                          u2 (var_ren l2 lvn)) as sv.
            eapply subvars_disjoint_l;[exact sv|].
            apply disjoint_app_l; dands; auto.
            rw @sub_bound_vars_var_ren; auto. }
      }

      exrepnd.
      allunfold @alpha_eq_bterms.
      allunfold @differ3_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands; eauto with slow.

      * apply alpha_eq_oterm_combine; dands; auto.

      * apply alpha_eq_oterm_combine; dands; auto.
Qed.

Lemma differ3_subst {o} :
  forall b a f g (t1 t2 : @NTerm o) sub1 sub2,
    disjoint (free_vars f) (dom_sub sub1)
    -> disjoint (free_vars g) (dom_sub sub2)
    -> differ3 b a f g t1 t2
    -> differ3_subs b a f g sub1 sub2
    -> differ3_alpha b a f g (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv clf clg dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  rw h0; rw k0.

  pose proof (differ3_change_bound_vars
                b a f g (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2 dt) as d; exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply differ3_lsubst_aux; auto.
Qed.
Hint Resolve differ3_subst : slow.

Lemma differ3_bterms_implies_eq_map_num_bvars {o} :
  forall b a f g (bs1 bs2 : list (@BTerm o)),
    differ3_bterms b a f g bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv d; allsimpl; auto;
  allunfold @differ3_bterms; allunfold @br_bterms; allunfold @br_list;
  allsimpl; repnd; cpx.
  pose proof (d a0 b0) as h; autodimp h hyp.
  inversion h; subst.
  f_equal.
  unfold num_bvars; simpl; auto.
Qed.

Definition differ3_sk {o} b a f g (sk1 sk2 : @sosub_kind o) :=
  differ3_b b a f g (sk2bterm sk1) (sk2bterm sk2).

Inductive differ3_sosubs {o} b a f g : @SOSub o -> @SOSub o -> Type :=
| dsosub3_nil : differ3_sosubs b a f g [] []
| dsosub3_cons :
    forall v sk1 sk2 sub1 sub2,
      differ3_sk b a f g sk1 sk2
      -> differ3_sosubs b a f g sub1 sub2
      -> differ3_sosubs b a f g ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors differ3_sosubs.

Lemma differ3_bterms_cons {o} :
  forall b a f g (b1 b2 : @BTerm o) bs1 bs2,
    differ3_bterms b a f g (b1 :: bs1) (b2 :: bs2)
    <=> (differ3_b b a f g b1 b2 # differ3_bterms b a f g bs1 bs2).
Proof.
  unfold differ3_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma differ3_mk_abs_substs {o} :
  forall b a f g (bs1 bs2 : list (@BTerm o)) vars,
    differ3_bterms b a f g bs1 bs2
    -> length vars = length bs1
    -> differ3_sosubs b a f g (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv d m; allsimpl; cpx; tcsp.
  - provefalse.
    apply differ3_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx.
  - apply differ3_bterms_cons in d; repnd.
    destruct s, a0, b0.
    inversion d0; subst.
    boolvar; auto.
Qed.

Lemma differ3_b_change_bound_vars {o} :
  forall b a f g vs (b1 b2 : @BTerm o),
    differ3_b b a f g b1 b2
    -> {u1 : BTerm
        & {u2 : BTerm
           & differ3_b b a f g u1 u2
           # alpha_eq_bterm b1 u1
           # alpha_eq_bterm b2 u2
           # disjoint (bound_vars_bterm u1) vs
           # disjoint (bound_vars_bterm u2) vs}}.
Proof.
  introv d.
  pose proof (differ3_change_bound_vars
                b a f g vs (oterm (Exc None) [b1]) (oterm (Exc None) [b2])) as h.
  repeat (autodimp h hyp).
  - apply differ3_oterm; simpl; tcsp.
    introv i; dorn i; tcsp; cpx.
  - exrepnd.
    inversion h2 as [|? ? ? len1 imp1]; subst; allsimpl; cpx.
    inversion h3 as [|? ? ? len2 imp2]; subst; allsimpl; cpx.
    pose proof (imp1 0) as k1; autodimp k1 hyp; allsimpl; clear imp1.
    pose proof (imp2 0) as k2; autodimp k2 hyp; allsimpl; clear imp2.
    allunfold @selectbt; allsimpl.
    allrw app_nil_r.
    exists x x0; dands; auto.
    inversion h0 as [|?|? ? ? ? ? i]; subst; allsimpl; GC.
    apply i; sp.
Qed.

Lemma differ3_sk_change_bound_vars {o} :
  forall b a f g vs (sk1 sk2 : @sosub_kind o),
    differ3_sk b a f g sk1 sk2
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
           & differ3_sk b a f g u1 u2
           # alphaeq_sk sk1 u1
           # alphaeq_sk sk2 u2
           # disjoint (bound_vars_sk u1) vs
           # disjoint (bound_vars_sk u2) vs}}.
Proof.
  introv d.
  unfold differ3_sk in d.
  apply (differ3_b_change_bound_vars b a f g vs) in d; exrepnd; allsimpl; auto.
  exists (bterm2sk u1) (bterm2sk u2).
  destruct u1, u2, sk1, sk2; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ3_sosubs_change_bound_vars {o} :
  forall b a f g vs (sub1 sub2 : @SOSub o),
    differ3_sosubs b a f g sub1 sub2
    -> {sub1' : SOSub
        & {sub2' : SOSub
           & differ3_sosubs b a f g sub1' sub2'
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
    apply IHsub1 in dso; exrepnd; auto.
    apply (differ3_sk_change_bound_vars b a f g vs) in dsk; exrepnd; auto.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto with slow.
Qed.

Lemma sosub_find_some_if_differ3_sosubs {o} :
  forall b a f g (sub1 sub2 : @SOSub o) v sk,
    differ3_sosubs b a f g sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind
        & differ3_sk b a f g sk sk'
        # sosub_find sub2 v = Some sk'}.
Proof.
  induction sub1; destruct sub2; introv aeq sf; allsimpl; tcsp.
  - inversion aeq.
  - destruct a0, p; destruct s, s0.
    inversion aeq as [|? ? ? ? ? dsk dso]; subst; clear aeq.
    boolvar; subst; cpx; tcsp.
    + eexists; dands; eauto.
    + inversion dsk; subst; tcsp.
    + inversion dsk; subst; tcsp.
Qed.

Lemma sosub_find_none_if_differ3_sosubs {o} :
  forall b a f g (sub1 sub2 : @SOSub o) v,
    differ3_sosubs b a f g sub1 sub2
    -> sosub_find sub1 v = None
    -> sosub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv aeq sf; allsimpl; tcsp.
  - inversion aeq.
  - destruct a0, p; destruct s, s0.
    inversion aeq as [|? ? ? ? ? dsk dso]; subst; clear aeq.
    boolvar; subst; cpx; tcsp.
    inversion dsk; subst; tcsp.
Qed.

Lemma differ3_subs_combine {o} :
  forall b a f g (ts1 ts2 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> (forall t1 t2,
          LIn (t1,t2) (combine ts1 ts2)
          -> differ3 b a f g t1 t2)
    -> differ3_subs b a f g (combine vs ts1) (combine vs ts2).
Proof.
  induction ts1; destruct ts2; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma differ3_apply_list {o} :
  forall b a f g (ts1 ts2 : list (@NTerm o)) t1 t2,
    differ3 b a f g t1 t2
    -> length ts1 = length ts2
    -> (forall x y, LIn (x,y) (combine ts1 ts2) -> differ3 b a f g x y)
    -> differ3 b a f g (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; destruct ts2; introv d l i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ3_oterm; simpl; auto; tcsp.
  introv k; repndors; cpx; tcsp; constructor; auto.
Qed.

Lemma differ3_sosub_filter {o} :
  forall b a f g (sub1 sub2 : @SOSub o) vs,
    differ3_sosubs b a f g sub1 sub2
    -> differ3_sosubs b a f g (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ3_sosub_filter : slow.

Lemma no_utokens_sovar {o} :
  forall v (ts : list (@SOTerm o)),
    no_utokens (sovar v ts) <=> (forall t, LIn t ts -> no_utokens t).
Proof.
  introv.
  unfold no_utokens; simpl.
  induction ts; simpl; split; intro k; tcsp.
  - introv i; repndors; subst; tcsp.
    + rw app_eq_nil_iff in k; sp.
    + rw app_eq_nil_iff in k; repnd.
      rw IHts in k; sp.
  - rw app_eq_nil_iff; dands; tcsp.
    apply IHts; tcsp.
Qed.

Definition no_utokens_op {o} (op : @Opid o) :=
  get_utokens_o op = [].

Lemma no_utokens_soterm {o} :
  forall op (bs : list (@SOBTerm o)),
    no_utokens (soterm op bs)
    <=>
    (no_utokens_op op # (forall vs t, LIn (sobterm vs t) bs -> no_utokens t)).
Proof.
  introv; unfold cover_so_vars; simpl; split; intro k; repnd; dands; tcsp.
  - allunfold @no_utokens; allsimpl.
    rw app_eq_nil_iff in k; repnd; auto.
  - introv i.
    allunfold @no_utokens; allsimpl.
    rw app_eq_nil_iff in k; repnd; auto.
    rw flat_map_empty in k.
    apply k in i; allsimpl; auto.
  - allunfold @no_utokens; simpl.
    rw app_eq_nil_iff; dands; auto.
    rw flat_map_empty; introv i.
    destruct a; apply k in i; allsimpl; auto.
Qed.

Lemma differ3_sosub_aux {o} :
  forall b a f g (t : @SOTerm o) sub1 sub2,
    no_utokens t
    -> disjoint (fo_bound_vars t) (free_vars f)
    -> disjoint (fo_bound_vars t) (free_vars g)
    -> differ3_sosubs b a f g sub1 sub2
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ3 b a f g (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case;
  introv nut df dg ds;
  introv disj1 disj2 disj3 disj4 disj5 disj6 cov1 cov2; allsimpl.

  - Case "sovar".
    allrw @cover_so_vars_sovar; repnd.
    allrw @no_utokens_sovar.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ3_sosubs b a f g sub1 sub2) in Heqf1; auto.
      exrepnd.
      rw Heqf2.
      destruct s as [l1 t1].
      destruct sk' as [l2 t2].
      inversion Heqf0; subst.
      apply differ3_lsubst_aux; auto.

      * apply sosub_find_some in Heqf2; repnd.
        rw @dom_sub_combine; allrw map_length; eauto with slow.

      * apply sosub_find_some in Heqf2; repnd.
        rw @dom_sub_combine; allrw map_length; eauto with slow.

      * apply differ3_subs_combine; allrw map_length; auto.
        introv i.
        rw <- @map_combine in i.
        rw in_map_iff in i; exrepnd; cpx.
        apply in_combine_same in i1; repnd; subst; allsimpl.
        disj_flat_map.
        apply ind; auto.

      * apply sosub_find_some in Heqf1; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

      * apply sosub_find_some in Heqf2; repnd.
        rw @sub_free_vars_combine; allrw map_length; auto.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto with slow.
        eapply subvars_disjoint_r;[|apply disjoint_sym;eauto].
        apply subvars_flat_map2; introv i.
        apply fovars_subvars_all_fo_vars.

    + applydup (sosub_find_none_if_differ3_sosubs b a f g sub1 sub2) in Heqf1; auto.
      rw Heqf0.
      apply differ3_apply_list; allrw map_length; auto.
      introv i.
      rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
      apply in_combine_same in i1; repnd; subst; allsimpl.
      disj_flat_map.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm.
    allrw @no_utokens_soterm; repnd.
    apply differ3_oterm; allrw map_length; tcsp; try (complete (rw nut0; sp)).
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
    apply in_combine_same in i1; repnd; subst; allsimpl.
    destruct a0 as [l t].
    disj_flat_map.
    allsimpl; allrw disjoint_app_l; repnd.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.
    constructor; auto.
    eapply ind; eauto with slow.

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

Lemma differ3_sosub {o} :
  forall b a f g (t : @SOTerm o) (sub1 sub2 : SOSub),
    no_utokens t
    -> differ3_sosubs b a f g sub1 sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ3_alpha b a f g (sosub sub1 t) (sosub sub2 t).
Proof.
  introv nut d c1 c2.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.

  pose proof (differ3_sosubs_change_bound_vars
                b a
                f g
                (all_fo_vars t1
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
                                 ++ free_vars f
                                 ++ free_vars g
                )
                t) as q.
  revert q.
  fo_change t0; simpl; intro q; repnd; GC.

  allrw disjoint_app_l; allrw disjoint_app_r; repnd.

  assert (so_alphaeq t1 t0) as a1 by eauto with slow.
  assert (so_alphaeq t2 t0) as a2 by eauto with slow.

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

  { dands; eauto with slow.
    - rw <- ev1; eauto with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto with slow.
    - rw <- ev2; eauto with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto with slow. }

  repnd.

  pose proof (sosub_aux_alpha_congr2
                t1 t0 sub1' sub1'') as aeq1.
  repeat (autodimp aeq1 hyp); eauto with slow.

  { rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[exact sv1|]; eauto with slow. }

  { rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[exact sv3|].
    eapply eqvars_disjoint_r;[apply eqvars_sym; exact ev3|].
    apply disjoint_app_r; dands; eauto with slow.
    rw <- efv1.
    eapply subvars_disjoint_r;[exact ev6|]; auto. }

  pose proof (sosub_aux_alpha_congr2
                t2 t0 sub2' sub2'') as aeq2.
  repeat (autodimp aeq2 hyp); eauto with slow.

  { rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[exact sv2|]; eauto with slow. }

  { rw disjoint_app_r; dands; eauto with slow.
    eapply subvars_disjoint_r;[exact sv3|].
    eapply eqvars_disjoint_r;[apply eqvars_sym; exact ev3|].
    apply disjoint_app_r; dands; eauto with slow.
    rw <- efv1.
    eapply subvars_disjoint_r;[exact ev6|]; auto. }

  exists (sosub_aux sub1'' t0) (sosub_aux sub2'' t0); dands;
  try (apply alphaeq_eq; complete auto).

  apply differ3_sosub_aux; eauto with slow.

  { allapply @get_utokens_so_soalphaeq.
    unfold no_utokens; rw <- h5; auto. }
Qed.

Lemma differ3_mk_instance {o} :
  forall b a f g (t : @SOTerm o) vars bs1 bs2,
    no_utokens t
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered t vars
    -> socovered t vars
    -> differ3_bterms b a f g bs1 bs2
    -> differ3_alpha b a f g (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv nut m1 m2 sc1 sc2 dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ3_mk_abs_substs o b a f g bs1 bs2 vars) in dbs; auto.

  apply differ3_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Lemma exists_compute_step_if_reduces_to {o} :
  forall lib (t1 t2 : @NTerm o),
    reduces_to lib t1 t2
    -> isvalue_like t2
    -> {u : NTerm
        & compute_step lib t1 = csuccess u
        # reduces_to lib u t2}.
Proof.
  introv r isv.
  unfold reduces_to in r; exrepnd.
  destruct k.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; repndors.
    + apply iscan_implies in isv; exrepnd; subst; simpl.
      eexists; eauto with slow.
    + apply isexc_implies2 in isv; exrepnd; subst; simpl.
      eexists; eauto with slow.
    + apply ismrk_implies2 in isv; exrepnd; subst; simpl.
      eexists; eauto with slow.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eexists; dands; eauto with slow.
    exists k; auto.
Qed.

Definition red_to_can {p} lib (t : @NTerm p) :=
  {u : NTerm
   & reduces_to lib t u
   # iscan u}.

Lemma if_red_to_can_ncompop_can1 {o} :
  forall lib c can bs (t : @NTerm o) l,
    red_to_can
      lib
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> red_to_can lib t.
Proof.
  introv hv.
  unfold red_to_can in hv; exrepnd.

  pose proof (converges_to_value_like_ncompop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.

  - exists (@mk_token o s); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.

  - provefalse.
    apply isexc_implies2 in h0; exrepnd; subst.
    pose proof (compose_reduces_to_primarg_ncompop
                  lib c can bs t (oterm (Exc a) l0) u l) as h.
    repeat (autodimp h hyp); tcsp.
    apply iscan_implies in hv0; exrepnd; subst.
    apply reduces_to_split2 in h; dorn h; simpl in h; ginv.
    exrepnd; ginv.
    apply reduces_to_if_isvalue_like in h0; tcsp; ginv.
Qed.

Lemma if_red_to_can_narithop_can1 {o} :
  forall lib c can bs (t : @NTerm o) l,
    red_to_can
      lib
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> red_to_can lib t.
Proof.
  introv hv.
  unfold red_to_can in hv; exrepnd.

  pose proof (converges_to_value_like_narithop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.

  - provefalse.
    apply isexc_implies2 in h0; exrepnd; subst.
    pose proof (compose_reduces_to_primarg_arithop
                  lib c can bs t (oterm (Exc a) l0) u l) as h.
    repeat (autodimp h hyp); tcsp.
    apply iscan_implies in hv0; exrepnd; subst.
    apply reduces_to_split2 in h; dorn h; simpl in h; ginv.
    exrepnd; ginv.
    apply reduces_to_if_isvalue_like in h0; tcsp; ginv.
Qed.

Definition red_to_can_k {p} lib k (t : @NTerm p) :=
  {u : NTerm
   & reduces_in_atmost_k_steps lib t u k
   # iscan u}.

Lemma red_to_can_0 {o} :
  forall lib (t : @NTerm o),
    red_to_can_k lib 0 t <=> iscan t.
Proof.
  introv; unfold red_to_can_k; split; intro k; exrepnd.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - exists t; allrw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma red_to_can_S {o} :
  forall lib k (t : @NTerm o),
    red_to_can_k lib (S k) t
    <=> {u : NTerm
         & compute_step lib t = csuccess u
         # red_to_can_k lib k u}.
Proof.
  introv; unfold red_to_can_k; split; intro h; exrepnd.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eexists; eauto.
  - exists u0; dands; auto.
    allrw @reduces_in_atmost_k_steps_S.
    eexists; eauto.
Qed.

Lemma if_red_to_can_k_ncompop_can1 {o} :
  forall lib c can bs k (t : @NTerm o) l,
    red_to_can_k
      lib k
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # red_to_can_k lib j t}.
Proof.
  induction k; introv r.
  - allrw @red_to_can_0; inversion r.
  - allrw @red_to_can_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (allsimpl; ginv)).
    dopid op as [can2|ncan2|exc2|mrk2|abs2] Case.
    + exists 0; dands; try lia.
      rw @red_to_can_0; auto.
    + rw @compute_step_ncompop_ncan2 in r1.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S.
      exists n; tcsp.
    + simpl in r1; ginv.
      provefalse.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
    + allsimpl; ginv.
    + simpl in r1.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S.
      exists n; tcsp.
Qed.

Lemma if_red_to_can_k_narithop_can1 {o} :
  forall lib c can bs k (t : @NTerm o) l,
    red_to_can_k
      lib k
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # red_to_can_k lib j t}.
Proof.
  induction k; introv r.
  - allrw @red_to_can_0; inversion r.
  - allrw @red_to_can_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (allsimpl; ginv)).
    dopid op as [can2|ncan2|exc2|mrk2|abs2] Case.
    + exists 0; dands; try lia.
      rw @red_to_can_0; auto.
    + rw @compute_step_narithop_ncan2 in r1.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S.
      exists n; tcsp.
    + simpl in r1; ginv.
      provefalse.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
    + allsimpl; ginv.
    + simpl in r1.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S.
      exists n; tcsp.
Qed.

Lemma red_to_can_k_lt {o} :
  forall lib k1 k2 (t : @NTerm o),
    red_to_can_k lib k1 t
    -> k1 < k2
    -> red_to_can_k lib k2 t.
Proof.
  unfold red_to_can_k; introv r l; exrepnd.
  exists u; dands; auto.
  pose proof (no_change_after_value_like lib t k1 u) as h.
  repeat (autodimp h hyp); tcsp.
  pose proof (h (k2 - k1)) as hh.
  assert (k2 - k1 + k1 = k2) as e by lia.
  rw e in hh; auto.
Qed.

Lemma if_red_to_can_k_cbv_primarg {o} :
  forall lib k (t : @NTerm o) bs,
    red_to_can_k lib k (oterm (NCan NCbv) (bterm [] t :: bs))
    -> {j : nat & j < k # red_to_can_k lib j t}.
Proof.
  induction k; introv r.

  - allrw @red_to_can_0; subst.
    inversion r.

  - allrw @red_to_can_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|mrk1|abs1] Case.

    + Case "Can".
      exists 0; dands; try lia.
      rw @red_to_can_0; auto.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S; exists n; sp.

    + Case "Exc".
      allsimpl; ginv.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
      inversion r1.

    + Case "Mrk".
      allsimpl; ginv.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      inversion r1.

    + Case "Abs".
      allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @red_to_can_S; exists n; sp.
Qed.

Lemma if_red_to_can_k_force_int_bound {o} :
  forall lib a v b k (t : @NTerm o),
    red_to_can_k
      lib k
      (force_int_bound v b t (uexc a))
    -> {j : nat
        & {z : Z
        & reduces_in_atmost_k_steps lib t (mk_integer z) j
        # S (S j) < k
        # Z.abs_nat z < b}}.
Proof.
  induction k; introv r.
  - allrw @red_to_can_0; inversion r.
  - allrw @red_to_can_S; exrepnd.
    destruct t as [v1|op1 bs1].
    { simpl in r1; ginv. }
    dopid op1 as [can1|ncan1|exc1|mrk1|abs1] Case.

    + Case "Can".
      simpl in r1; ginv.
      unfold apply_bterm, lsubst in r0; allsimpl.
      boolvar; fold_terms.
      destruct k.

      { allrw @red_to_can_0; inversion r0. }

      allrw @red_to_can_S; exrepnd; allsimpl.
      unfold on_success in r0.
      fold_terms.
      match goal with
        | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
      end.
      symmetry in Heqcomp; destruct comp; ginv.
      apply compute_step_compop_success_can_can in Heqcomp.
      exrepnd; subst; allsimpl; cpx; GC.
      repndors; exrepnd; ginv.
      allapply @get_int_from_cop_some; subst.

      destruct k.

      { allrw @red_to_can_0; inversion r1. }

      allrw @red_to_can_S; exrepnd.
      boolvar; allsimpl; ginv.

      * destruct k.

        { allrw @red_to_can_0; inversion r0. }

        allrw @red_to_can_S; exrepnd.
        allsimpl.
        unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

        { exists 0 n1; dands; try lia; eauto with slow.
          - rw @reduces_in_atmost_k_steps_0; auto.
          - apply abs_of_neg; auto. }

        { unfold red_to_can_k in r1; exrepnd.
          apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; tcsp.
          inversion r0. }

      * unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

        { exists 0 n1; dands; try lia; eauto with slow.
          - rw @reduces_in_atmost_k_steps_0; auto.
          - apply abs_of_pos; auto. }

        { unfold red_to_can_k in r0; exrepnd.
          apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
          inversion r1. }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      apply IHk in r0; auto; exrepnd.

      exists (S j) z; dands; auto; try lia.
      rw @reduces_in_atmost_k_steps_S; eexists; eauto.

    + Case "Exc".
      allsimpl; ginv.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
      inversion r1.

    + Case "Mrk".
      allsimpl; ginv.
      unfold red_to_can_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      inversion r1.

    + Case "Abs".
      simpl in r1; unfold on_success in r1.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      apply IHk in r0; auto; exrepnd.

      exists (S j) z; dands; auto; try lia.
      rw @reduces_in_atmost_k_steps_S; eexists; eauto.
Qed.

Definition isvalue_like_except {o} a (t : @NTerm o) :=
  isvalue_like t # !isnexc (Some a) t.

Definition has_value_like_except_k {p} lib a k (t : @NTerm p) :=
  {u : NTerm
   & reduces_in_atmost_k_steps lib t u k
   # isvalue_like_except a u}.

Lemma has_value_like_except_0 {o} :
  forall lib a (t : @NTerm o),
    has_value_like_except_k lib a 0 t <=> isvalue_like_except a t.
Proof.
  introv; unfold has_value_like_except_k; split; intro k; exrepnd.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - exists t; allrw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma has_value_like_except_S {o} :
  forall lib k a (t : @NTerm o),
    has_value_like_except_k lib a (S k) t
    <=> {u : NTerm
         & compute_step lib t = csuccess u
         # has_value_like_except_k lib a k u}.
Proof.
  introv; unfold has_value_like_except_k; split; intro h; exrepnd.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eexists; eauto.
  - exists u0; dands; auto.
    allrw @reduces_in_atmost_k_steps_S.
    eexists; eauto.
Qed.

Lemma if_has_value_like_except_k_ncompop_can1 {o} :
  forall lib c can bs a k (t : @NTerm o) l,
    has_value_like_except_k
      lib a k
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # has_value_like_except_k lib a j t}.
Proof.
  induction k; introv r.
  - allrw @has_value_like_except_0; repnd.
    unfold isvalue_like_except in r; repnd.
    inversion r0; sp.
  - allrw @has_value_like_except_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (allsimpl; ginv)).
    dopid op as [can2|ncan2|exc2|mrk2|abs2] Case.
    + exists 0; dands; try lia.
      rw @has_value_like_except_0; dands; eauto with slow.
      unfold isvalue_like_except; simpl; sp.
    + rw @compute_step_ncompop_ncan2 in r1.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; tcsp.
    + simpl in r1; ginv.
      exists k; sp.
    + allsimpl; ginv.
    + simpl in r1.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; tcsp.
Qed.

Lemma if_has_value_like_except_k_narithop_can1 {o} :
  forall lib c can bs a k (t : @NTerm o) l,
    has_value_like_except_k
      lib a k
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> {j : nat & j < k # has_value_like_except_k lib a j t}.
Proof.
  induction k; introv r.
  - allrw @has_value_like_except_0; repnd.
    unfold isvalue_like_except in r; repnd.
    inversion r0; sp.
  - allrw @has_value_like_except_S; exrepnd.
    destruct t as [v|op bs1]; try (complete (allsimpl; ginv)).
    dopid op as [can2|ncan2|exc2|mrk2|abs2] Case.
    + exists 0; dands; try lia.
      rw @has_value_like_except_0; dands; eauto with slow.
      unfold isvalue_like_except; simpl; sp.
    + rw @compute_step_narithop_ncan2 in r1.
      remember (compute_step lib (oterm (NCan ncan2) bs1)) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; tcsp.
    + simpl in r1; ginv.
      exists k; sp.
    + allsimpl; ginv.
    + simpl in r1.
      unfold on_success in r1.
      remember (compute_step_lib lib abs2 bs1) as comp1.
      symmetry in Heqcomp1.
      destruct comp1; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; tcsp.
Qed.

Lemma has_value_like_except_k_lt {o} :
  forall lib a k1 k2 (t : @NTerm o),
    has_value_like_except_k lib a k1 t
    -> k1 < k2
    -> has_value_like_except_k lib a k2 t.
Proof.
  unfold has_value_like_except_k; introv r l; exrepnd.
  exists u; dands; auto.
  pose proof (no_change_after_value_like lib t k1 u) as h.
  repeat (autodimp h hyp); tcsp.
  { unfold isvalue_like_except in r0; sp. }
  pose proof (h (k2 - k1)) as hh.
  assert (k2 - k1 + k1 = k2) as e by lia.
  rw e in hh; auto.
Qed.

Lemma if_has_value_like_except_k_cbv_primarg {o} :
  forall lib a k (t : @NTerm o) bs,
    has_value_like_except_k lib a k (oterm (NCan NCbv) (bterm [] t :: bs))
    -> {j : nat & j < k # has_value_like_except_k lib a j t}.
Proof.
  induction k; introv r.

  - allrw @has_value_like_except_0; repnd.
    unfold isvalue_like_except in r; repnd.
    inversion r0; sp.

  - allrw @has_value_like_except_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|mrk1|abs1] Case.

    + Case "Can".
      exists 0; dands; try lia.
      rw @has_value_like_except_0; dands; eauto with slow; simpl; sp.
      unfold isvalue_like_except; simpl; dands; eauto with slow; sp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S; exists n; sp.

    + Case "Exc".
      allsimpl; ginv.
      unfold has_value_like_except_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
      exists 0; dands; try lia.
      rw @has_value_like_except_0; dands; eauto with slow.

    + Case "Mrk".
      allsimpl; ginv.
      unfold has_value_like_except_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      unfold isvalue_like_except in r1; repnd.
      inversion r0; tcsp.

    + Case "Abs".
      allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S; exists n; sp.
Qed.

Lemma isvalue_like_except_integer {o} :
  forall a z, @isvalue_like_except o a (mk_integer z).
Proof.
  introv; unfold isvalue_like_except; simpl; sp; eauto with slow.
Qed.
Hint Resolve isvalue_like_except_integer : slow.

Lemma isvalue_like_except_uni {o} :
  forall a n, @isvalue_like_except o a (mk_uni n).
Proof.
  introv; unfold isvalue_like_except; simpl; sp; eauto with slow.
Qed.
Hint Resolve isvalue_like_except_uni : slow.

Lemma if_has_value_like_except_k_force_int_bound {o} :
  forall lib a v b k (t : @NTerm o),
    has_value_like_except_k
      lib a k
      (force_int_bound v b t (uexc a))
    -> {j : nat
        & {u : NTerm
           & reduces_in_atmost_k_steps lib t u j
           # j < k
           # isvalue_like_except a u
           # ({z : Z & u = mk_integer z # Z.abs_nat z < b}[+]isexc u)
       }}.
Proof.
  induction k; introv r.

  - allrw @has_value_like_except_0; repnd.
    unfold isvalue_like_except in r; repnd.
    inversion r0; sp.

  - allrw @has_value_like_except_S; exrepnd.
    destruct t as [v1|op1 bs1].
    { simpl in r1; ginv. }
    dopid op1 as [can1|ncan1|exc1|mrk1|abs1] Case.

    + Case "Can".
      simpl in r1; ginv.
      unfold apply_bterm, lsubst in r0; allsimpl.
      boolvar; fold_terms.
      destruct k.

      { allrw @has_value_like_except_0; repnd.
        unfold isvalue_like_except in r0; repnd.
        inversion r1; sp. }

      allrw @has_value_like_except_S; exrepnd; allsimpl.
      unfold on_success in r0.
      fold_terms.
      match goal with
        | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
      end.
      symmetry in Heqcomp; destruct comp; ginv.
      apply compute_step_compop_success_can_can in Heqcomp.
      exrepnd; subst; allsimpl; cpx; GC.
      repndors; exrepnd; ginv.
      allapply @get_int_from_cop_some; subst.

      destruct k.

      { allrw @has_value_like_except_0; repnd.
        unfold isvalue_like_except in r1; repnd.
        inversion r0; sp. }

      allrw @has_value_like_except_S; exrepnd.
      boolvar; allsimpl; ginv.

      * destruct k.

        { allrw @has_value_like_except_0; repnd.
          unfold isvalue_like_except in r0; repnd.
          inversion r1; sp. }

        allrw @has_value_like_except_S; exrepnd.
        allsimpl.
        unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

        { exists 0 (@mk_integer o n1); dands; try lia; eauto with slow.
          - rw @reduces_in_atmost_k_steps_0; auto.
          - left; exists n1; dands; auto; apply abs_of_neg; auto. }

        { unfold has_value_like_except_k in r1; exrepnd.
          apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; tcsp.
          unfold isvalue_like_except in r0; repnd; allsimpl; boolvar; allsimpl; ginv; tcsp.
          destruct r0; sp. }

      * unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

        { exists 0 (@mk_integer o n1); dands; try lia; eauto with slow.
          - rw @reduces_in_atmost_k_steps_0; auto.
          - left; exists n1; dands; auto; apply abs_of_pos; auto. }

        { unfold has_value_like_except_k in r0; exrepnd.
          apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
          unfold isvalue_like_except in r1; repnd; allsimpl; boolvar; allsimpl; ginv; tcsp.
          destruct r1; sp. }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      apply IHk in r0; auto; exrepnd.

      exists (S j) u; dands; auto; try lia.
      rw @reduces_in_atmost_k_steps_S; eexists; eauto.

    + Case "Exc".
      allsimpl; ginv.
      unfold has_value_like_except_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; tcsp.
      allsimpl; boolvar; subst; try (complete (destruct r1; sp)); GC.
      exists 0 (oterm (Exc exc1) bs1); dands; eauto with slow; try lia.
      rw @reduces_in_atmost_k_steps_0; auto.

    + Case "Mrk".
      allsimpl; ginv.
      unfold has_value_like_except_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      unfold isvalue_like_except in r1; repnd.
      inversion r0; sp.

    + Case "Abs".
      simpl in r1; unfold on_success in r1.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      apply IHk in r0; auto; exrepnd.
      exists (S j) u; dands; auto; try lia.
      rw @reduces_in_atmost_k_steps_S; eexists; eauto.
Qed.


Lemma compute_step_force_int_bound {o} :
  forall lib v b a z k (t u : @NTerm o),
    compute_step lib (force_int_bound v b t (uexc a)) = csuccess u
    -> reduces_in_atmost_k_steps lib t (mk_integer z) k
    -> Z.abs_nat z < b
    -> reduces_to lib u (mk_integer z).
Proof.
  destruct t as [v1|op1 bs1];[allsimpl; ginv|];
  introv comp r l; ginv.
  dopid op1 as [can1|ncan2|exc1|mrk1|abs1] Case.

  - Case "Can".
    simpl in comp; ginv.
    apply reduces_in_atmost_k_steps_if_isvalue_like in r; tcsp.
    inversion r; subst.
    unfold apply_bterm, lsubst; simpl; boolvar; fold_terms; GC.
    destruct (Z_lt_le_dec z 0) as [i|i].
    + apply (reduces_to_if_split2
               _ _ (mk_less
                      (mk_minus (mk_integer z))
                      (mk_nat b)
                      (mk_integer z)
                      (uexc a)));
      simpl; boolvar; tcsp; try lia.
      apply (reduces_to_if_split2
               _ _ (mk_less
                      (mk_integer (- z))
                      (mk_nat b)
                      (mk_integer z)
                      (uexc a)));
        simpl; boolvar; tcsp; try lia.
      apply reduces_to_if_step.
      simpl.
      unfold compute_step_comp; simpl; boolvar; auto.
      provefalse.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as kk.
      autodimp kk hyp; try lia.
      allrw Znat.Zabs2Nat.id.
      destruct z; allsimpl; try lia.
    + apply (reduces_to_if_split2
               _ _ (mk_less
                      (mk_integer z)
                      (mk_nat b)
                      (mk_integer z)
                      (uexc a)));
      simpl; boolvar; tcsp; try lia.
      apply reduces_to_if_step.
      simpl.
      unfold compute_step_comp; simpl; boolvar; auto.
      provefalse.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as kk.
      autodimp kk hyp; try lia.
      allrw Znat.Zabs2Nat.id.
      destruct z; allsimpl; try lia.

  - Case "NCan".
    destruct k.
    + allrw @reduces_in_atmost_k_steps_0; ginv.
    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      unfold force_int_bound in comp.
      rw @compute_step_mk_cbv_ncan in comp.
      rw r1 in comp; ginv; clear r1.
      pose proof (reduces_to_prinarg
                    lib NCbv u0 (mk_integer z)
                    [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
      repeat (autodimp h hyp); eauto with slow.
      eapply reduces_to_trans;[exact h|].
      apply (reduces_to_if_split2
               _ _ (less_bound b (mk_integer z) (uexc a))).
      { simpl; unfold apply_bterm, lsubst; simpl; boolvar; tcsp. }
      destruct (Z_lt_le_dec z 0) as [i|i].
      * apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_minus (mk_integer z))
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
        simpl; boolvar; tcsp; try lia.
        apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_integer (- z))
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
          simpl; boolvar; tcsp; try lia.
        apply reduces_to_if_step.
        simpl.
        unfold compute_step_comp; simpl; boolvar; auto.
        provefalse.
        pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as kk.
        autodimp kk hyp; try lia.
        allrw Znat.Zabs2Nat.id.
        destruct z; allsimpl; try lia.
      * apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_integer z)
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
        simpl; boolvar; tcsp; try lia.
        apply reduces_to_if_step.
        simpl.
        unfold compute_step_comp; simpl; boolvar; auto.
        provefalse.
        pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as kk.
        autodimp kk hyp; try lia.
        allrw Znat.Zabs2Nat.id.
        destruct z; allsimpl; try lia.

  - Case "Exc".
    allsimpl; ginv.
    apply reduces_in_atmost_k_steps_if_isvalue_like in r; tcsp; ginv.

  - Case "Mrk".
    allsimpl; ginv.
    apply reduces_in_atmost_k_steps_if_isvalue_like in r; tcsp; ginv.

  - Case "Abs".
    destruct k.
    + allrw @reduces_in_atmost_k_steps_0; ginv.
    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      unfold force_int_bound in comp.
      rw @compute_step_mk_cbv_abs in comp.
      rw r1 in comp; ginv; clear r1.
      pose proof (reduces_to_prinarg
                    lib NCbv u0 (mk_integer z)
                    [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
      repeat (autodimp h hyp); eauto with slow.
      eapply reduces_to_trans;[exact h|].
      apply (reduces_to_if_split2
               _ _ (less_bound b (mk_integer z) (uexc a))).
      { simpl; unfold apply_bterm, lsubst; simpl; boolvar; tcsp. }
      destruct (Z_lt_le_dec z 0) as [i|i].
      * apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_minus (mk_integer z))
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
        simpl; boolvar; tcsp; try lia.
        apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_integer (- z))
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
          simpl; boolvar; tcsp; try lia.
        apply reduces_to_if_step.
        simpl.
        unfold compute_step_comp; simpl; boolvar; auto.
        provefalse.
        pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as kk.
        autodimp kk hyp; try lia.
        allrw Znat.Zabs2Nat.id.
        destruct z; allsimpl; try lia.
      * apply (reduces_to_if_split2
                 _ _ (mk_less
                        (mk_integer z)
                        (mk_nat b)
                        (mk_integer z)
                        (uexc a)));
        simpl; boolvar; tcsp; try lia.
        apply reduces_to_if_step.
        simpl.
        unfold compute_step_comp; simpl; boolvar; auto.
        provefalse.
        pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as kk.
        autodimp kk hyp; try lia.
        allrw Znat.Zabs2Nat.id.
        destruct z; allsimpl; try lia.
Qed.

Lemma compute_step_force_int_bound_exc {o} :
  forall lib v b a (t u e : @NTerm o),
    compute_step lib (force_int_bound v b t (uexc a)) = csuccess u
    -> reduces_to lib t e
    -> isexc e
    -> reduces_to lib u e.
Proof.
  destruct t as [v1|op1 bs1];[allsimpl; ginv|];
  introv comp r l; ginv.
  dopid op1 as [can1|ncan2|exc1|mrk1|abs1] Case.

  - Case "Can".
    apply reduces_to_if_isvalue_like in r; eauto with slow; subst.
    inversion l.

  - Case "NCan".
    apply reduces_to_split2 in r; dorn r; subst.
    + inversion l.
    + exrepnd.
      unfold force_int_bound in comp.
      rw @compute_step_mk_cbv_ncan in comp.
      rw r1 in comp; ginv; clear r1.
      pose proof (reduces_to_prinarg
                    lib NCbv v0 e
                    [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
      repeat (autodimp h hyp); eauto with slow.
      eapply reduces_to_trans;[exact h|].
      apply isexc_implies2 in l; exrepnd; subst; eauto with slow.

  - Case "Exc".
    allsimpl; ginv; auto.

  - Case "Mrk".
    allsimpl; ginv.
    apply reduces_to_if_isvalue_like in r; subst; eauto with slow.
    inversion l.

  - Case "Abs".
    apply reduces_to_split2 in r; dorn r; subst.
    + inversion l.
    + exrepnd.
      unfold force_int_bound in comp.
      rw @compute_step_mk_cbv_abs in comp.
      rw r1 in comp; ginv; clear r1.
      pose proof (reduces_to_prinarg
                    lib NCbv v0 e
                    [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
      repeat (autodimp h hyp); eauto with slow.
      eapply reduces_to_trans;[exact h|].
      apply isexc_implies2 in l; exrepnd; subst; eauto with slow.
Qed.

Lemma lsubst_aux_vterm_single {o} :
  forall v (t : @NTerm o),
    lsubst_aux (vterm v) [(v, t)] = t.
Proof.
  introv; simpl; boolvar; auto.
Qed.

(*
Lemma compute_step_lsubst_aux_int {o} :
  forall lib (t u : @NTerm o) v arg z,
    reduces_to lib arg (mk_integer z)
    -> compute_step lib (lsubst_aux t [(v, arg)]) = csuccess u
    -> red_to_can lib u
    -> {t' : NTerm
        & {x : NVar
        & !LIn x (bound_vars t)
        # alpha_eq t (lsubst_aux t' [(x,mk_var v)])
        # reduces_to
            lib u
            (lsubst_aux (lsubst_aux t' [(x,mk_integer z)]) [(v,arg)]) }}.
Proof.
  nterm_ind t as [y|op bs ind] Case; introv r comp rtc.

  - Case "vterm".
    allsimpl; boolvar; allsimpl; ginv.
    apply reduces_to_split2 in r; dorn r; subst; allsimpl; ginv.

    + exists (@mk_var o y) y; dands; simpl; boolvar; simpl; eauto with slow; tcsp.

    + exrepnd.
      rw r1 in comp; ginv.
      exists (@mk_var o y) y; dands; simpl; boolvar; simpl; eauto with slow; tcsp.

  - Case "oterm".
    dopid op as [can|ncan|exc|mrk|abs] SCase.

    + SCase "Can".
      allsimpl; ginv.
      pose proof (ex_fresh_var (all_vars (oterm (Can can) bs))) as f; exrepnd.
      unfold all_vars in f0; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
      exists (oterm (Can can) bs) v0; dands; auto.

      * rw @lsubst_aux_trivial_cl_term; auto; simpl.
        rw disjoint_singleton_r; auto.

      * rw (lsubst_aux_trivial_cl_term (oterm (Can can) bs)); eauto with slow; simpl.
        rw disjoint_singleton_r; auto.

    + SCase "NCan".
      destruct bs as [|b bs]; try (complete (allsimpl; ginv)).
      destruct b as [l t].
      destruct l; try (complete (allsimpl; ginv)).
      destruct t as [v1|op1 bs1]; try (complete (allsimpl; ginv)).

      * destruct (deq_nvar v1 v) as [i|i]; subst;
        [|simpl in comp; boolvar; tcsp; ginv].
        allrw @lsubst_aux_oterm.
        allrw map_cons.
        allrw @lsubst_aux_bterm_nil.
        allrw @lsubst_aux_vterm_single.

        destruct arg as [va|opa bsa]; try (complete (allsimpl; ginv)).
        dopid opa as [cana|ncana|exca|mrka|absa] SSCase.

        { SSCase "Can".
          apply reduces_to_if_isvalue_like in r; eauto with slow.
          inversion r; subst; fold_terms; GC.
          dopid_noncan ncan SSSCase; try (complete (allsimpl; ginv)).

          - SSSCase "NFix".
            allsimpl.
            apply compute_step_fix_success in comp; repnd; subst.
            unfold red_to_can in rtc; exrepnd.
            apply iscan_implies in rtc0; exrepnd; subst.
            apply reduces_to_split2 in rtc1; dorn rtc1; exrepnd; allsimpl; ginv.

          - SSSCase "NCbv".
            allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst.
            destruct bs; allsimpl; ginv; boolvar.
            destruct bs; allsimpl; ginv; boolvar.
            destruct b as [l t]; allsimpl; boolvar; ginv; allsimpl; repdors; tcsp; subst.

            * pose proof (ex_fresh_var (v :: bound_vars t ++ free_vars t)) as h; exrepnd.
              allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
              exists (oterm (NCan NCbv) [nobnd (mk_var v0), bterm [v] t]) v0; dands; auto.

              { allrw not_over_or; sp. }

              { simpl; boolvar; repndors; tcsp; subst.
                allrw not_over_or; repnd; GC.
                rw @lsubst_aux_trivial_cl_term; auto; simpl.
                rw disjoint_singleton_r; auto. }

              { simpl; boolvar; repndors; tcsp; subst; GC; allrw not_over_or; repnd; tcsp; GC.
                allsimpl.
                rw (lsubst_aux_trivial_cl_term t); simpl; tcsp.
                rw (lsubst_aux_trivial_cl_term t); simpl; tcsp;
                [|allrw disjoint_singleton_r; auto].

            *
Abort.
*)

Lemma reduces_to_lsubst_aux_int {o} :
  forall lib z1 z2 (b : @NTerm o) v arg,
    disjoint (bound_vars b) (free_vars arg)
    -> reduces_to lib arg (mk_integer z1)
    -> reduces_to lib (lsubst_aux b [(v,arg)]) (mk_integer z2)
    -> reduces_to lib (lsubst_aux b [(v,mk_integer z1)]) (mk_integer z2).
Proof.
  introv d r1 r2.
  unfold reduces_to in r2; exrepnd.
  revert dependent arg.
  revert dependent v.
  revert dependent b.
  induction k; introv d compa compf.

  - allrw @reduces_in_atmost_k_steps_0; ginv.
    destruct b as [x|op bs].

    + allsimpl; boolvar; ginv.
      apply reduces_to_if_isvalue_like in compa; eauto with slow; ginv; eauto with slow.

    + allsimpl; boolvar; inversion compf;
      subst; destruct bs; allsimpl; ginv; fold_terms; GC;
      eauto with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

(*
    nterm_ind b as [x|op bs indb] Case; ginv.

    + allsimpl; boolvar; allsimpl;
      unfold subst, lsubst; simpl; boolvar; ginv.
      assert (reduces_to lib arg (mk_integer z2)) as r.
      { eapply reduces_to_if_split2; eauto with slow. }
      pose proof (reduces_to_eq_val_like lib arg (mk_integer z1) (mk_integer z2)) as h.
      repeat (autodimp h hyp); eauto with slow; ginv; eauto with slow.

    + dopid op as [can|ncan|exc|mrk|abs] Case.

      * Case "Can".
        allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in compf0; eauto with slow.
        inversion compf0; subst; destruct bs; allsimpl; ginv; eauto with slow.

      * Case "NCan".
        destruct bs as [|b bs]; try (complete (allsimpl; ginv)).
        destruct b as [l t].
        destruct l; try (complete (allsimpl; ginv)).

        destruct t as [x|op1 bs1]; try (complete (allsimpl; ginv)).

        { destruct (deq_nvar x v) as [i|i]; subst;
          [|simpl in compf1; boolvar; tcsp; ginv].
          rw @lsubst_aux_oterm in compf1.
          rw map_cons in compf1.
          rw @lsubst_aux_bterm_nil in compf1.
          rw @lsubst_aux_vterm_single in compf1.

          destruct arg as [y|opa bsa]; try (complete (allsimpl; ginv)).
          dopid opa as [cana|ncana|exca|mrka|absa] SCase.

          - SCase "Can".
            apply reduces_to_if_isvalue_like in compa; eauto with slow.
            inversion compa; subst; fold_terms; GC.
            dopid_noncan ncan SSCase; try (complete (allsimpl; ginv)).

            + SSCase "NFix".
              allsimpl.
              apply compute_step_fix_success in compf1; repnd; subst.
              provefalse.
              apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
              apply reduces_to_split2 in compf0; dorn compf0; exrepnd; allsimpl; ginv.

            + SSCase "NCbv".
              simpl in compf1.
              apply compute_step_cbv_success in compf1; exrepnd; subst.
              destruct bs; allsimpl; ginv; boolvar.
              destruct bs; allsimpl; ginv; boolvar.
              destruct b as [l t]; allsimpl; boolvar; ginv; allsimpl; repdors; tcsp; subst.

              * apply (reduces_to_if_split2
                         _ _ (subst (lsubst_aux t []) v (mk_integer z1)));
                eauto with slow.

              * allrw not_over_or; repnd; GC.
                apply (reduces_to_if_split2
                         _ _ (subst (lsubst_aux t [(v, mk_integer z1)]) v0 (mk_integer z1)));
                  eauto with slow.

            + SSCase "NSleep".
              allsimpl.
              apply compute_step_sleep_success in compf1; exrepnd; subst.
              apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
              apply reduces_to_if_isvalue_like in compf0; eauto with slow; ginv.

            + SSCase "NTUni".
              allsimpl.
              apply compute_step_tuni_success in compf1; exrepnd; subst.
              apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
              apply reduces_to_if_isvalue_like in compf0; eauto with slow; ginv.

            + SSCase "NMinus".
              allsimpl.
              apply compute_step_minus_success in compf1; exrepnd; subst; ginv.
              apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
              apply reduces_to_if_isvalue_like in compf0; eauto with slow; ginv.
              destruct bs; allsimpl; ginv; fold_terms; GC; ginv.
              boolvar; eauto with slow.

            + SSCase "NTryCatch".
              allsimpl.
              apply compute_step_try_success in compf1; exrepnd; subst; allsimpl.
              apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
              apply reduces_to_if_isvalue_like in compf0; eauto with slow; ginv.
              inversion compf0; subst; fold_terms; GC.
              boolvar.
              destruct bs; allsimpl; ginv.
              destruct bs; allsimpl; ginv.
              destruct b; allsimpl.
              destruct l; allsimpl; cpx; allsimpl.
              boolvar; allsimpl; ginv; repndors; tcsp; subst; eauto with slow.

            + SSCase "NCompOp".
              destruct bs; try (complete (allsimpl; ginv)).
              destruct b as [l t].
              destruct l; destruct t as [v1|op1 bs1]; try (complete (allsimpl; ginv)).

              * destruct (deq_nvar v1 v) as [i|i]; subst;
                [|allsimpl; boolvar; tcsp; complete ginv].
                rw map_cons in compf1.
                rw @lsubst_aux_bterm_nil in compf1.
                rw @lsubst_aux_vterm_single in compf1.
                simpl in compf1.
                apply compute_step_compop_success_can_can in compf1; exrepnd; GC.
                destruct bs; try (complete (allsimpl; ginv)).
                destruct bs; try (complete (allsimpl; ginv)).
                destruct bs; try (complete (allsimpl; ginv)).
                allsimpl; cpx; boolvar.
                destruct b as [l3 t3]; allsimpl; ginv.
                destruct l3; allsimpl; ginv.
                destruct b0 as [l4 t4]; allsimpl; ginv.
                destruct l4; allsimpl; ginv.
                cpx; fold_terms; GC.
                apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
                repndors; exrepnd; subst; ginv; eauto with slow.

                { eapply reduces_to_if_split2; eauto; simpl.
                  unfold compute_step_comp; simpl; auto. }

                { eapply reduces_to_if_split2; eauto; simpl.
                  unfold compute_step_comp; simpl; auto. }

              * allrw map_cons.
                allrw @lsubst_aux_bterm_nil.
                dopid op1 as [can1|ncan1|exc1|mrk1|abs1] SSSSCase.

                { SSSSCase "Can".
                  simpl in compf1.
                  apply compute_step_compop_success_can_can in compf1; exrepnd; GC.
                  destruct bs1; allsimpl; cpx; GC.
                  destruct bs; allsimpl; cpx; GC.
                  destruct bs; allsimpl; cpx; GC.
                  destruct bs; allsimpl; cpx; GC.
                  allsimpl; cpx; boolvar.
                  destruct b as [l3 t3]; allsimpl; ginv.
                  destruct l3; allsimpl; ginv.
                  destruct b0 as [l4 t4]; allsimpl; ginv.
                  destruct l4; allsimpl; ginv.
                  cpx; fold_terms; ginv; GC.
                  apply reduces_in_atmost_k_steps_implies_reduces_to in compf0.
                  repndors; exrepnd; subst; ginv; eauto with slow.

                  { eapply reduces_to_if_split2; eauto; simpl.
                    allapply @get_int_from_cop_some; subst; allsimpl.
                    unfold compute_step_comp; simpl; auto. }

                  { eapply reduces_to_if_split2; eauto; simpl.
                    allapply @get_int_from_cop_some; subst; allsimpl.
                    unfold compute_step_comp; simpl; auto. }
                }

                { SSSSCase "NCan".
                  rw @lsubst_aux_oterm in compf1.
                  unfold_all_mk; allunfold @mk_integer.
                  rw @compute_step_ncompop_ncan2 in compf1.
                  match goal with
                    | [ H : context[compute_step ?a1 ?a2] |- _ ] =>
                      remember (compute_step a1 a2) as comp
                  end.
                  symmetry in Heqcomp; destruct comp; ginv.
*)

Abort.

Lemma reduces_to_apply_int {o} :
  forall lib z1 z2 (f arg : @NTerm o),
    reduces_to lib arg (mk_integer z1)
    -> reduces_to lib (mk_apply f arg) (mk_integer z2)
    -> reduces_to lib (mk_apply f (mk_integer z1)) (mk_integer z2).
Proof.
  introv r1 r2.
  unfold reduces_to in r2; exrepnd.
  revert dependent arg.
  revert dependent f.
  induction k; introv compa compf.

  - allrw @reduces_in_atmost_k_steps_0; ginv.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    simpl in compf1.
    destruct f as [v|op bs]; ginv.
    dopid op as [can|ncan|exc|mrk|abs] Case.

    + Case "Can".
      apply compute_step_apply_success in compf1; exrepnd; subst.
      fold_terms; ginv.

Abort.

Lemma reduces_to_force_int_bound_app_z {o} :
  forall lib v b a z (t f : @NTerm o),
    !LIn v (free_vars f)
    -> Z.abs_nat z < b
    -> reduces_to lib t (mk_integer z)
    -> reduces_to lib (force_int_bound_app v b t f (uexc a))
                  (mk_apply f (mk_integer z)).
Proof.
  introv ni l r.
  pose proof (reduces_to_prinarg
                lib NCbv
                (force_int_bound v b t (uexc a))
                (mk_integer z)
                [bterm [v] (mk_apply f (mk_var v))]) as h.
  fold_terms.
  autodimp h hyp.

  - pose proof (reduces_to_prinarg
                  lib NCbv
                  t
                  (mk_integer z)
                  [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
    fold_terms.
    autodimp h hyp.

    + eapply reduces_to_trans; eauto.
      apply (reduces_to_if_split2
               _ _ (less_bound b (mk_integer z) (uexc a))).

      * simpl; unfold apply_bterm, lsubst; simpl; boolvar; auto.

      * destruct (Z_lt_le_dec z 0).

        { apply (reduces_to_if_split2
                   _ _ (mk_less (mk_minus (mk_integer z))
                                (mk_nat b)
                                (mk_integer z)
                                (uexc a))); auto;
          [simpl; boolvar; tcsp; try lia|].

          apply (reduces_to_if_split2
                   _ _ (mk_less (mk_integer (- z))
                                (mk_nat b)
                                (mk_integer z)
                                (uexc a))); auto.
          apply reduces_to_if_step; simpl.
          unfold compute_step_comp; simpl; boolvar; tcsp.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (- z)) as k.
          autodimp k hyp; try lia.
          allrw Znat.Zabs2Nat.id.
          destruct z; allsimpl; try lia. }

        { apply (reduces_to_if_split2
                   _ _ (mk_less (mk_integer z)
                                (mk_nat b)
                                (mk_integer z)
                                (uexc a))); auto;
          [simpl; boolvar; tcsp; try lia|].
          apply reduces_to_if_step; simpl.
          unfold compute_step_comp; simpl; boolvar; tcsp.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as k.
          autodimp k hyp; try lia.
          allrw Znat.Zabs2Nat.id.
          destruct z; allsimpl; try lia. }

  - eapply reduces_to_trans; eauto.
    apply reduces_to_if_step; simpl.
    unfold apply_bterm, lsubst; simpl; boolvar; tcsp;
    try (complete (provefalse; sp)).

    rw @lsubst_aux_trivial_cl_term; auto; simpl.
    rw disjoint_singleton_r; auto.
Qed.

Lemma differ3_alpha_integer {o} :
  forall b a f g z (t : @NTerm o),
    differ3_alpha b a f g (mk_integer z) t
    -> t = mk_integer z.
Proof.
  introv d.
  unfold differ3_alpha in d; exrepnd.
  inversion d0; subst; allsimpl; cpx; fold_terms.
  inversion d1; subst; allsimpl; cpx.
  inversion d2; allsimpl; cpx.
Qed.

Lemma differ3_alpha_exc {o} :
  forall x b a f g (e t : @NTerm o),
    differ3_alpha b a f g e t
    -> isnexc x e
    -> isnexc x t.
Proof.
  introv d i.
  unfold differ3_alpha in d; exrepnd.
  apply isnexc_implies in i; exrepnd; subst.
  inversion d0; subst; allsimpl; cpx; fold_terms.
  inversion d1; subst; allsimpl; cpx.
  inversion d2; allsimpl; subst; boolvar; subst; tcsp.
Qed.

Lemma isvalue_like_except_can {o} :
  forall a c (bs : list (@BTerm o)), @isvalue_like_except o a (oterm (Can c) bs).
Proof.
  introv; unfold isvalue_like_except; simpl; sp; eauto with slow.
Qed.
Hint Resolve isvalue_like_except_can : slow.

Lemma isvalue_like_except_exc {o} :
  forall a e (bs : list (@BTerm o)),
    !LIn a (get_utokens_en e)
    -> isvalue_like_except a (oterm (Exc e) bs).
Proof.
  introv; unfold isvalue_like_except; simpl; sp; eauto with slow.
  boolvar; tcsp.
  destruct e; ginv; allsimpl; tcsp.
Qed.
Hint Resolve isvalue_like_except_exc : slow.

Lemma if_has_value_like_except_k_ncan_primarg {o} :
  forall lib a ncan k (t : @NTerm o) bs,
    !LIn a (get_utokens_nc ncan)
    -> has_value_like_except_k lib a k (oterm (NCan ncan) (bterm [] t :: bs))
    -> {j : nat & j < k # has_value_like_except_k lib a j t}.
Proof.
  induction k; introv ni r.

  - allrw @has_value_like_except_0.
    unfold isvalue_like_except in r; repnd.
    inversion r0; tcsp.

  - allrw @has_value_like_except_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|mrk1|abs1] Case.

    + Case "Can".
      exists 0; dands; try lia.
      rw @has_value_like_except_0; eauto with slow.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd; auto.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; sp.

    + Case "Exc".
      allsimpl.
      apply compute_step_catch_success in r1.
      dorn r1; exrepnd; subst; allsimpl.

      * exists 0; dands; try lia.
        rw @has_value_like_except_0; eauto with slow.

      * exists 0; dands; try lia.
        unfold has_value_like_except_k in r0; exrepnd.
        apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; subst.
        unfold isvalue_like_except in r1; repnd; allsimpl; boolvar; tcsp;
        try (complete (destruct r1; sp)); GC.
        rw @has_value_like_except_0; eauto with slow.
        apply isvalue_like_except_exc; simpl.
        destruct exc1; allsimpl; tcsp.
        intro j; dorn j; tcsp; subst; sp.

    + Case "Mrk".
      allsimpl; ginv.
      unfold has_value_like_except_k in r0; exrepnd.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      unfold isvalue_like_except in r1; repnd.
      inversion r0; sp.

    + Case "Abs".
      allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd; auto.
      exists (S j); dands; try lia.
      rw @has_value_like_except_S.
      exists n; sp.
Qed.

Lemma comp_force_int_step3 {o} :
  forall lib b a f g (t1 t2 : @NTerm o) kk u,
    !LIn a (get_utokens f)
    -> !LIn a (get_utokens g)
    -> agree_upto_b lib b f g
    -> differ3 b a f g t1 t2
    -> compute_step lib t1 = csuccess u
    -> has_value_like_except_k lib a kk u
    -> (forall t1 t2 v m, (* induction hypothesis *)
          m < S kk
          -> isvalue_like_except a v
          -> reduces_in_atmost_k_steps lib t1 v m
          -> differ3 b a f g t1 t2
          -> {v' : NTerm & reduces_to lib t2 v' # differ3_alpha b a f g v v'})
    -> {t : NTerm
        & {u' : NTerm
           & reduces_to lib t2 t
           # reduces_to lib u u'
           # differ3_alpha b a f g u' t}}.
Proof.
  nterm_ind1s t1 as [v|op bs ind] Case;
  introv nif nig agree d comp hv compind.

  - Case "vterm".
    simpl.
    inversion d; subst; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|mrk|abs] SCase; ginv.

    + SCase "Can".
      inversion d; subst.
      allsimpl; ginv.
      exists (oterm (Can can) bs2) (oterm (Can can) bs); dands; eauto with slow.

    + SCase "NCan".
      destruct bs as [|b1 bs];
        try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (simpl in comp; ginv)).

      destruct t1 as [v1|op1 bs1].

      * destruct t2 as [v2|op2 bs2]; try (complete (inversion d));[].

        inversion d as [? ? ? ? d1|?|? ? ? len imp]; subst; simphyps; cpx; ginv.

      * (* Now destruct op2 *)
        dopid op1 as [can1|ncan1|exc1|mrk1|abs1] SSCase; ginv.

        { SSCase "Can".

          (* Because the principal argument is canonical we can destruct ncan *)
          dopid_noncan ncan SSSCase.

          - SSSCase "NApply".
            allsimpl.
            apply compute_step_apply_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can NLambda) [bterm [v] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] arg) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.
            destruct bs2; allsimpl; cpx.
            cpx.

            pose proof (imp1 (bterm [v] b0) b1) as d1.
            autodimp d1 hyp.
            clear imp1.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            exists (subst t2 v t0) (subst b0 v arg); dands; eauto with slow.

            apply differ3_subst; simpl; eauto with slow.

          - SSSCase "NFix".
            allsimpl.
            apply compute_step_fix_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.

            exists (mk_apply (oterm (Can can1) bs2)
                             (mk_fix (oterm (Can can1) bs2)))
                   (mk_apply (oterm (Can can1) bs1)
                             (mk_fix (oterm (Can can1) bs1))).
            dands; eauto with slow.

            apply differ3_implies_differ3_alpha.
            apply differ3_oterm; simpl; tcsp.
            introv j; repndors; cpx; tcsp.

            { constructor; auto ; constructor; allsimpl; auto. }

            { constructor; auto; constructor; simpl; tcsp.
              introv j; repndors; cpx; tcsp. }

          - SSSCase "NSpread".
            allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can NPair) [bterm [] a0, bterm [] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] a0) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (bterm [] b0) x) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? df5 dg5 d5]; subst; clear d1.
            inversion d2 as [? ? ? df6 dg6 d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)]) (lsubst arg [(va,a0),(vb,b0)]); dands; eauto with slow.
            apply differ3_subst; simpl; eauto with slow.

          - SSSCase "NDsup".
            allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can NSup) [bterm [] a0, bterm [] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] a0) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (bterm [] b0) x) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? df5 dg5 d5]; subst; clear d1.
            inversion d2 as [? ? ? df6 dg6 d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)]) (lsubst arg [(va,a0),(vb,b0)]); dands; eauto with slow.
            apply differ3_subst; simpl; eauto with slow.

          - SSSCase "NDecide".
            allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) [bterm [] d0])) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v1] t1) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v2] t0) x) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? df4 dg4 d4]; subst; clear d1.
            inversion d2 as [? ? ? df5 dg5 d5]; subst; clear d2.
            inversion d3 as [? ? ? df6 dg6 d6]; subst; clear d3.

            inversion d4 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d4.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] d0) x) as d1.
            autodimp d1 hyp.
            clear imp1.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            dorn comp0; repnd; subst.

            + exists (subst t4 v1 t3) (subst t1 v1 d0); dands; eauto with slow.
              apply differ3_subst; simpl; eauto with slow.

            + exists (subst t5 v2 t3) (subst t0 v2 d0); dands; eauto with slow.
              apply differ3_subst; simpl; eauto with slow.

          - SSSCase "NCbv".
            allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] x) x0) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.

            exists (subst t0 v (oterm (Can can1) bs2))
                   (subst x v (oterm (Can can1) bs1)); dands; eauto with slow.
            apply differ3_subst; simpl; eauto with slow.

          - SSSCase "NSleep".
            allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 sg2 d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_axiom o)
                   (@mk_axiom o).
            dands; eauto with slow.
            apply differ3_implies_differ3_alpha; auto.
            apply differ3_refl; simpl; tcsp.

          - SSSCase "NTUni".
            allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint (Z.of_nat n))) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_uni o n)
                   (@mk_uni o n).
            dands; eauto with slow.
            { apply reduces_to_if_step; simpl.
              unfold compute_step_tuni; simpl; boolvar; try lia.
              rw Znat.Nat2Z.id; auto. }

            apply differ3_implies_differ3_alpha; auto.
            apply differ3_refl; simpl; tcsp.

          - SSSCase "NMinus".
            allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_integer o (- z))
                   (@mk_integer o (- z)).
            dands; eauto with slow.

            apply differ3_implies_differ3_alpha; auto.
            apply differ3_refl; simpl; tcsp.

          - SSSCase "NTryCatch".
            allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] x) x0) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.

            exists (oterm (Can can1) bs2)
                   (oterm (Can can1) bs1).
            dands; eauto with slow.

          - SSSCase "NCompOp".
            destruct bs; try (complete (allsimpl; ginv)).
            destruct b0 as [l t].
            destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; ginv)).

            inversion d as [?|?|? ? ? ni len imp]; subst; clear d.
            simpl in len, ni; GC.

            destruct bs3; simpl in len; cpx.
            destruct bs3; simpl in len; cpx.
            simpl in imp.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [|?|? ? ? ni1 len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|mrk3|abs3] SSSSCase.

            + SSSSCase "Can".
              simpl in comp.

              inversion d4 as [|?|? ? ? ni2 len2 imp2]; subst; clear d4; cpx.

              apply compute_step_compop_success_can_can in comp.
              exrepnd; subst.

              allsimpl; cpx.
              destruct bs3; allsimpl; cpx.
              destruct bs3; allsimpl; cpx.
              destruct bs3; allsimpl; cpx.
              GC.
              clear imp2.

              pose proof (imp (nobnd t1) b0) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd t2) b1) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? df33 dg33 d3]; subst; clear d1.
              inversion d2 as [? ? ? df44 dg44 d4]; subst; clear d2.

              dorn comp1;[|dorn comp1]; exrepnd; subst.

              * allapply @get_int_from_cop_some; subst; allsimpl.
                exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                       (if Z_lt_le_dec n1 n2 then t1 else t2);
                  dands; eauto with slow.
                boolvar; eauto with slow.

              * allapply @get_int_from_cop_some; subst; allsimpl.
                exists (if Z.eq_dec n1 n2 then t3 else t4)
                       (if Z.eq_dec n1 n2 then t1 else t2);
                  dands; eauto with slow.
                boolvar; eauto with slow.

              * allapply @get_str_from_cop_some; subst; allsimpl.
                exists (if String.string_dec s1 s2 then t3 else t4)
                       (if String.string_dec s1 s2 then t1 else t2);
                  dands; eauto with slow.
                boolvar; eauto with slow.

            + SSSSCase "NCan".
              rw @compute_step_ncompop_ncan2 in comp.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp); tcsp.

              pose proof (h t0 kk n) as k; clear h.
              repeat (autodimp k hyp).

              { apply if_has_value_like_except_k_ncompop_can1 in hv; exrepnd.
                apply (has_value_like_except_k_lt lib a j kk) in hv0; auto. }

              exrepnd.

              exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] t
                                   :: bs3))
                     (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: bterm [] u'
                                   :: bs)).
              dands; eauto with slow.

              * apply reduce_to_prinargs_comp2; eauto with slow; sp.

              * apply reduce_to_prinargs_comp2; eauto with slow; sp.

              * unfold differ3_alpha in k1; exrepnd.
                exists (oterm (NCan (NCompOp c))
                              (bterm [] (oterm (Can can1) bs1)
                                     :: bterm [] u1
                                     :: bs))
                       (oterm (NCan (NCompOp c))
                              (bterm [] (oterm (Can can1) bs4)
                                     :: bterm [] u2
                                     :: bs3)).
                dands.

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try lia; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try lia; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { apply differ3_oterm; simpl; tcsp.
                  introv j; repndors; cpx. }

            + SSSSCase "Exc".
              allsimpl; ginv.
              inversion d4 as [|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm (Exc exc3) bs5) (oterm (Exc exc3) bs2); dands; eauto with slow.

            + SSSSCase "Mrk".
              allsimpl; ginv.

            + SSSSCase "Abs".
              allsimpl.
              unfold on_success in comp.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|? ? ? ni2 len2 imp2]; subst; simphyps; clear d4.

              assert (differ3_bterms b a f g bs2 bs5) as dbs.
              { unfold differ3_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

              exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] (mk_instance vars bs5 rhs)
                                   :: bs3))
              (oterm (NCan (NCompOp c))
                     (bterm [] (oterm (Can can1) bs1)
                            :: bterm [] (mk_instance vars bs2 rhs)
                            :: bs)).

             dands; eauto with slow.

             * apply reduces_to_if_step.
               simpl; unfold on_success.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ3_mk_instance b a f g rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp); tcsp; GC.
               { unfold correct_abs in correct; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ3_alpha in h.
               exrepnd.

               exists
                 (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can can1) bs1)
                               :: bterm [] u1
                               :: bs))
                 (oterm (NCan (NCompOp c))
                        (bterm [] (oterm (Can can1) bs4)
                               :: bterm [] u2
                               :: bs3)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ3_oterm; allsimpl; tcsp.
                 introv j; repndors; cpx. }

          - SSSCase "NArithOp".
            destruct bs; try (complete (allsimpl; ginv)).
            destruct b0 as [l t].
            destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; ginv)).

            inversion d as [?|?|? ? ? ni len imp]; subst; clear d.
            simpl in len, ni; GC.

            destruct bs3; simpl in len; cpx.
            destruct bs3; simpl in len; cpx.
            simpl in imp.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [|?|? ? ? ni1 len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|mrk3|abs3] SSSSCase.

            + SSSSCase "Can".
              simpl in comp.

              inversion d4 as [|?|? ? ? ni2 len2 imp2]; subst; clear d4; cpx.

              apply compute_step_arithop_success_can_can in comp.
              exrepnd; subst.

              allsimpl; cpx.

              allapply @get_int_from_cop_some; subst; allsimpl; GC.
              exists (@oterm o (Can (Nint (get_arith_op a0 n1 n2))) [])
                     (@oterm o (Can (Nint (get_arith_op a0 n1 n2))) []);
                dands; eauto with slow.

              apply differ3_implies_differ3_alpha.
              apply differ3_refl; simpl; tcsp.

            + SSSSCase "NCan".
              rw @compute_step_narithop_ncan2 in comp.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp); tcsp.

              pose proof (h t0 kk n) as k; clear h.
              repeat (autodimp k hyp).

              { apply if_has_value_like_except_k_narithop_can1 in hv; exrepnd.
                apply (has_value_like_except_k_lt lib a j kk) in hv0; auto. }

              exrepnd.

              exists (oterm (NCan (NArithOp a0))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] t
                                   :: bs3))
                     (oterm (NCan (NArithOp a0))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: bterm [] u'
                                   :: bs)).
              dands; eauto with slow.

              * apply reduce_to_prinargs_arith2; eauto with slow; sp.

              * apply reduce_to_prinargs_arith2; eauto with slow; sp.

              * unfold differ3_alpha in k1; exrepnd.
                exists (oterm (NCan (NArithOp a0))
                              (bterm [] (oterm (Can can1) bs1)
                                     :: bterm [] u1
                                     :: bs))
                       (oterm (NCan (NArithOp a0))
                              (bterm [] (oterm (Can can1) bs4)
                                     :: bterm [] u2
                                     :: bs3)).
                dands.

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try lia; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try lia; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { apply differ3_oterm; simpl; tcsp.
                  introv j; repndors; cpx. }

            + SSSSCase "Exc".
              allsimpl; ginv.
              inversion d4 as [|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm (Exc exc3) bs5) (oterm (Exc exc3) bs2); dands; eauto with slow.

            + SSSSCase "Mrk".
              allsimpl; ginv.

            + SSSSCase "Abs".
              allsimpl.
              unfold on_success in comp.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|? ? ? ni2 len2 imp2]; subst; simphyps; clear d4.

              assert (differ3_bterms b a f g bs2 bs5) as dbs.
              { unfold differ3_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

              exists (oterm (NCan (NArithOp a0))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] (mk_instance vars bs5 rhs)
                                   :: bs3))
              (oterm (NCan (NArithOp a0))
                     (bterm [] (oterm (Can can1) bs1)
                            :: bterm [] (mk_instance vars bs2 rhs)
                            :: bs)).

             dands; eauto with slow.

             * apply reduces_to_if_step.
               simpl; unfold on_success.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ3_mk_instance b a f g rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp); tcsp; GC.
               { unfold correct_abs in correct; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ3_alpha in h.
               exrepnd.

               exists
                 (oterm (NCan (NArithOp a0))
                        (bterm [] (oterm (Can can1) bs1)
                               :: bterm [] u1
                               :: bs))
                 (oterm (NCan (NArithOp a0))
                        (bterm [] (oterm (Can can1) bs4)
                               :: bterm [] u2
                               :: bs3)).
               dands.

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try lia; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ3_oterm; allsimpl; tcsp.
                 introv j; repndors; cpx. }

          - SSSCase "NCanTest".
            allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] arg2nt) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [] arg3nt) x) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? df4 dg4 d4]; subst; clear d1.
            inversion d2 as [? ? ? df5 dg5 d5]; subst; clear d2.
            inversion d3 as [? ? ? df6 dg6 d6]; subst; clear d3.

            inversion d4 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; clear d4.

            exists (if canonical_form_test_for c can1 then t0 else t3)
                   (if canonical_form_test_for c can1 then arg2nt else arg3nt).
            dands; eauto with slow.
            destruct (canonical_form_test_for c can1); eauto with slow.
        }

        { SSCase "NCan".
          rw @compute_step_ncan_ncan in comp.
          remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [? ? ? ? ? ni1 ni2 d1 aeq1 aeq2|?|? ? ? ni len imp];
            subst; clear d.

          - (* let's prove that t1 computes to an integer in less than kk steps *)
            fold_terms; fold (force_int_bound v b t1 (uexc a)) in Heqcomp1.
            applydup @if_has_value_like_except_k_cbv_primarg in hv; simpl; tcsp; exrepnd.
            assert (has_value_like_except_k lib a (S j) (force_int_bound v b t1 (uexc a))) as hvf.
            { rw @has_value_like_except_S; eexists; eauto. }
            apply if_has_value_like_except_k_force_int_bound in hvf; exrepnd.

            pose proof (compind t1 t0 u j0) as r.
            repeat (autodimp r hyp); try lia; exrepnd.

            dorn hvf1; exrepnd; subst.

            { apply differ3_alpha_integer in r0; subst.
              pose proof (agree z) as ag.
              repeat (autodimp ag hyp); eauto with slow.
              exrepnd.

              pose proof (compute_step_force_int_bound lib v b a z j0 t1 n) as rz.
              repeat (autodimp rz hyp).

              exists (@mk_integer o z0) (@mk_integer o z0); dands.

              + pose proof (reduces_to_force_int_bound_app_z
                              lib v b a z t0 ga) as h.
                repeat (autodimp h hyp); tcsp.
                { apply alphaeq_preserves_free_vars in aeq2; rw <- aeq2; auto. }
                eapply reduces_to_trans;[exact h|].

                pose proof (reduces_to_alpha
                              lib
                              (mk_apply g (mk_integer z))
                              (mk_apply ga (mk_integer z))
                              (mk_integer z0)) as k.
                repeat (autodimp k hyp).

                { prove_alpha_eq4.
                  introv q; destruct n0;[|destruct n0]; cpx.
                  apply alphaeqbt_nilv2; auto. }

                exrepnd.
                inversion k0; subst; allsimpl; cpx.

              + pose proof (reduces_to_prinarg
                              lib NCbv
                              n
                              (mk_integer z)
                              [bterm [v] (mk_apply fa (mk_var v))]) as h.
                fold_terms.
                autodimp h hyp.
                eapply reduces_to_trans;[exact h|].
                apply (reduces_to_if_split2
                         _ _ (mk_apply fa (mk_integer z))).

                { simpl; unfold apply_bterm, lsubst; simpl; boolvar;
                  try (complete (provefalse; sp)).
                  rw @lsubst_aux_trivial_cl_term; auto; simpl.
                  rw disjoint_singleton_r; auto.
                  apply alphaeq_preserves_free_vars in aeq1; rw <- aeq1; auto. }

                pose proof (reduces_to_alpha
                              lib
                              (mk_apply f (mk_integer z))
                              (mk_apply fa (mk_integer z))
                              (mk_integer z0)) as k.
                repeat (autodimp k hyp).

                { prove_alpha_eq4.
                  introv q; destruct n0;[|destruct n0]; cpx.
                  apply alphaeqbt_nilv2; auto. }

                exrepnd.
                inversion k0; subst; allsimpl; cpx.

              + apply differ3_implies_differ3_alpha.
                apply differ3_refl; simpl; tcsp.
            }

            { apply isexc_implies2 in hvf1; exrepnd; subst.
              applydup (@differ3_alpha_exc o a0) in r0; eauto with slow;
              try (complete (simpl; boolvar; tcsp)).
              apply isnexc_implies in r2; exrepnd; subst.

              pose proof (compute_step_force_int_bound_exc
                            lib v b a t1 n (oterm (Exc a0) l)) as r.
              repeat (autodimp r hyp); eauto with slow.

              exists (oterm (Exc a0) l0) (oterm (Exc a0) l); dands; auto.

              - pose proof (reduces_to_prinarg
                              lib NCbv
                              (force_int_bound v b t0 (uexc a))
                              (oterm (Exc a0) l0)
                              [bterm [v] (mk_apply ga (mk_var v))]) as h.
                fold_terms.
                autodimp h hyp.
                { pose proof (reduces_to_prinarg
                              lib NCbv
                              t0
                              (oterm (Exc a0) l0)
                              [bterm [v] (less_bound b (mk_var v) (uexc a))]) as h.
                  fold_terms.
                  autodimp h hyp.
                  eapply reduces_to_trans; eauto with slow. }
                eapply reduces_to_trans; eauto with slow.

              - pose proof (reduces_to_prinarg
                              lib NCbv
                              n
                              (oterm (Exc a0) l)
                              [bterm [v] (mk_apply fa (mk_var v))]) as h.
                fold_terms.
                autodimp h hyp.
                eapply reduces_to_trans; eauto with slow.
            }

          - simpl in len, ni.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (NCan ncan1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            pose proof (ind (oterm (NCan ncan1) bs1) (oterm (NCan ncan1) bs1) []) as h; clear ind.
            repeat (autodimp h hyp); tcsp.

            pose proof (h t2 kk n) as k; clear h.
            repeat (autodimp k hyp); tcsp.

            { apply if_has_value_like_except_k_ncan_primarg in hv; auto.
              exrepnd.
              apply (has_value_like_except_k_lt lib a j kk); auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto with slow.

            + apply reduces_to_prinarg; auto.
            + apply reduces_to_prinarg; auto.

            + unfold differ3_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              * prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              * prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              * apply differ3_oterm; simpl; auto.
                introv j; dorn j; cpx.
        }

        { SSCase "Exc".
          allsimpl.
          apply compute_step_catch_success in comp.

          inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; cpx; clear d.
          destruct bs2; allsimpl; cpx.
          pose proof (imp (bterm [] (oterm (Exc exc1) bs1)) b0) as d1.
          autodimp d1 hyp.
          inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.
          inversion d2 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; cpx; clear d2.

          dorn comp; exrepnd; subst; allsimpl; cpx; allsimpl.

          - pose proof (imp (bterm [v] b0) x) as d1; clear imp.
            autodimp d1 hyp.
            inversion d1 as [? ? ? df22 dg22 d2]; subst; clear d1.
            pose proof (imp1 (bterm [] e) x0) as d1; clear imp1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.

            exists (subst t2 v t0) (subst b0 v e); dands; eauto with slow.

            + apply reduces_to_if_step.
              simpl; boolvar; tcsp.

            + apply differ3_subst; simpl; eauto with slow.

          - exists (oterm (Exc exc1) bs3) (oterm (Exc exc1) bs1); dands; eauto with slow.

            apply reduces_to_if_step; simpl.
            unfold compute_step_catch; destruct ncan; tcsp.
            boolvar; subst; tcsp.
        }

        { SSCase "Mrk".
          allsimpl; ginv.
          provefalse.
          unfold has_value_like_except_k in hv; exrepnd.
          apply reduces_in_atmost_k_steps_primarg_marker in hv1; subst.
          unfold isvalue_like_except in hv0; repnd.
          inversion hv1; tcsp.
        }

        { SSCase "Abs".
          allsimpl.
          unfold on_success in comp.
          remember (compute_step_lib lib abs1 bs1) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [?|?|? ? ? ni len imp]; subst; clear d.
          destruct bs2; allsimpl; cpx.
          pose proof (imp (bterm [] (oterm (Abs abs1) bs1)) b0) as d1.
          autodimp d1 hyp.
          inversion d1 as [? ? ? df2 sg2 d2]; subst; clear d1.
          inversion d2 as [?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; cpx; clear d2.

          apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

          assert (differ3_bterms b a f g bs1 bs3) as dbs.
          { unfold differ3_bterms, br_bterms, br_list; auto. }

          pose proof (found_entry_change_bs abs1 oa2 vars rhs lib bs1 correct bs3) as fe2.
          repeat (autodimp fe2 hyp).

          { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

          exists
          (oterm (NCan ncan)
                 (bterm [] (mk_instance vars bs3 rhs)
                        :: bs2))
          (oterm (NCan ncan)
                 (bterm [] (mk_instance vars bs1 rhs)
                        :: bs)).

          dands; eauto with slow.

          * apply reduces_to_prinarg.
            apply reduces_to_if_step.
            simpl; unfold on_success.
            applydup @compute_step_lib_if_found_entry in fe2.
            rw fe0; auto.

          * pose proof (differ3_mk_instance b a f g rhs vars bs1 bs3) as h.
            repeat (autodimp h hyp); tcsp; GC.
            { unfold correct_abs in correct; sp. }
            { allapply @found_entry_implies_matching_entry.
              allunfold @matching_entry; sp. }
            { allapply @found_entry_implies_matching_entry.
              allunfold @matching_entry; sp. }
            { allunfold @correct_abs; sp. }
            { allunfold @correct_abs; sp. }
            unfold differ3_alpha in h.
            exrepnd.

            exists
              (oterm (NCan ncan) (bterm [] u1 :: bs))
              (oterm (NCan ncan) (bterm [] u2 :: bs2)).
            dands.

            { prove_alpha_eq4.
              introv j; destruct n;[|destruct n]; try lia; cpx.
              apply alphaeqbt_nilv2; auto. }

            { prove_alpha_eq4.
              introv j; destruct n;[|destruct n]; try lia; cpx.
              apply alphaeqbt_nilv2; auto. }

            { apply differ3_oterm; allsimpl; tcsp.
              introv j; repndors; cpx. }
        }

    + SCase "Exc".
      allsimpl; ginv.

      inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; cpx; clear d.

      exists (oterm (Exc exc) bs2) (oterm (Exc exc) bs); dands; eauto with slow.

    + SCase "Mrk".
      allsimpl; ginv.

      inversion d as [?|?|? ? ? ni len imp]; subst; allsimpl; cpx; clear d.

      exists (oterm (Mrk mrk) bs2) (oterm (Mrk mrk) bs); dands; eauto with slow.

    + SCase "Abs".
      allsimpl.

      inversion d as [?|?|? ? ? ni len imp]; subst; clear d.

      apply compute_step_lib_success in comp; exrepnd; subst.

      assert (differ3_bterms b a f g bs bs2) as dbs.
      { unfold differ3_bterms, br_bterms, br_list; auto. }

      pose proof (found_entry_change_bs abs oa2 vars rhs lib bs correct bs2) as fe2.
      repeat (autodimp fe2 hyp).

      { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

      exists (mk_instance vars bs2 rhs) (mk_instance vars bs rhs).

      dands; eauto with slow.

      * apply reduces_to_if_step.
        simpl; unfold on_success.
        applydup @compute_step_lib_if_found_entry in fe2.
        rw fe0; auto.

      * pose proof (differ3_mk_instance b a f g rhs vars bs bs2) as h.
        repeat (autodimp h hyp); tcsp; GC.
        { unfold correct_abs in correct; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allunfold @correct_abs; sp. }
        { allunfold @correct_abs; sp. }
Qed.

Lemma isvalue_like_except_implies_isvalue_like {o} :
  forall a (t : @NTerm o),
    isvalue_like_except a t
    -> isvalue_like t.
Proof.
  introv isv.
  unfold isvalue_like_except in isv; sp.
Qed.
Hint Resolve isvalue_like_except_implies_isvalue_like : slow.

Lemma alpha_eq_preserves_isvalue_like_except {o} :
  forall a (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> isvalue_like_except a t1
    -> isvalue_like_except a t2.
Proof.
  introv aeq isv.
  allunfold @isvalue_like_except; repnd.
  applydup @alpha_eq_preserves_isvalue_like in aeq; auto.
  dands; auto.
  intro k.
  apply isnexc_implies in k; exrepnd; subst.
  inversion aeq; subst; allsimpl; boolvar; ginv; tcsp.
Qed.

Lemma comp_force_int3_aux {o} :
  forall lib a f g (t1 t2 : @NTerm o) b u,
    !LIn a (get_utokens f)
    -> !LIn a (get_utokens g)
    -> agree_upto_b lib b f g
    -> differ3 b a f g t1 t2
    -> isvalue_like_except a u
    -> reduces_to lib t1 u
    -> {v : NTerm & reduces_to lib t2 v # differ3_alpha b a f g u v}.
Proof.
  introv nif nig agree d isv comp.
  unfold reduces_to in comp; exrepnd.
  revert dependent u.
  revert dependent t2.
  revert dependent t1.
  induction k as [n ind] using comp_ind_type; introv r isv d.
  destruct n as [|k]; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t2; dands; eauto with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    pose proof (comp_force_int_step3 lib b a f g t1 t2 k u0) as h.
    repeat (autodimp h hyp).

    { unfold has_value_like_except_k.
      exists u; dands; auto. }

    { introv l' i' r' d'.
      eapply ind; eauto. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to
                  lib k u0 u' u) as h'.
    repeat (autodimp h' hyp); eauto with slow.
    exrepnd.

    unfold differ3_alpha in h1; exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u' u1) as h''.
    autodimp h'' hyp.

    pose proof (h'' k' u) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.

    pose proof (ind k') as h.
    autodimp h hyp;[lia|].
    pose proof (h u1 u2) as r'; clear h.
    autodimp r' hyp.

    pose proof (r' t2') as h; clear r'; repeat (autodimp h hyp).

    { eapply alpha_eq_preserves_isvalue_like_except in h'''0; eauto. }

    exrepnd.

    pose proof (reduces_to_steps_alpha lib u2 t v) as r'.
    repeat (autodimp r' hyp); eauto with slow.
    exrepnd.
    exists u3; dands; eauto with slow.

    { eapply reduces_to_trans; eauto. }

    { unfold differ3_alpha in h5; exrepnd.
      exists u4 u5; dands; eauto with slow. }
Qed.

Lemma comp_force_int3 {o} :
  forall lib a f g (t1 t2 : @NTerm o) b z,
    !LIn a (get_utokens f)
    -> !LIn a (get_utokens g)
    -> agree_upto_b lib b f g
    -> differ3 b a f g t1 t2
    -> reduces_to lib t1 (mk_integer z)
    -> reduces_to lib t2 (mk_integer z).
Proof.
  introv nif nig agree d comp.
  pose proof (comp_force_int3_aux lib a f g t1 t2 b (mk_integer z)) as h.
  repeat (autodimp h hyp); eauto with slow.

  exrepnd.
  apply differ3_alpha_integer in h0; subst; auto.
Qed.

Lemma differ_app_F3 {o} :
  forall b a (F : @NTerm o) x f g,
    !LIn a (get_utokens F)
    -> !LIn x (free_vars f)
    -> !LIn x (free_vars g)
    -> disjoint (bound_vars F) (free_vars f)
    -> disjoint (bound_vars F) (free_vars g)
    -> differ3
         b a
         f g
         (force_int_bound_F x b F f (uexc a))
         (force_int_bound_F x b F g (uexc a)).
Proof.
  introv ni1 ni2 ni3 df dg.
  constructor; simpl; tcsp.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto with slow.
  - constructor; auto; constructor; simpl; tcsp.
    introv i; dorn i; cpx.
    constructor; allrw disjoint_singleton_l; auto; constructor; simpl; auto.
Qed.

Lemma comp_force_int_app_F3 {o} :
  forall lib a (F f g : @NTerm o) x z b,
    !LIn a (get_utokens F)
    -> !LIn a (get_utokens f)
    -> !LIn a (get_utokens g)
    -> !LIn x (free_vars f)
    -> !LIn x (free_vars g)
    -> disjoint (bound_vars F) (free_vars f)
    -> disjoint (bound_vars F) (free_vars g)
    -> agree_upto_b lib b f g
    -> reduces_to
         lib
         (force_int_bound_F x b F f (uexc a))
         (mk_integer z)
    -> reduces_to
         lib
         (force_int_bound_F x b F g (uexc a))
         (mk_integer z).
Proof.
  introv ni1 ni2 ni3 ni4 ni5 df dg agree r.

  apply (comp_force_int3 _ a f g (force_int_bound_F x b F f (uexc a)) _ b); auto.

  apply differ_app_F3; auto; allrw; tcsp.
Qed.
