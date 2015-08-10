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



Inductive differ2 {o} (b : nat) (a : get_patom_set o) : @NTerm o -> @NTerm o -> Type :=
| differ2_force_int :
    forall t1 t2 v,
      differ2 b a t1 t2
      -> differ2 b a (force_int_bound v b t1 (uexc a)) (force_int t2)
| differ2_var :
    forall v, differ2 b a (mk_var v) (mk_var v)
| differ2_oterm :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> differ2_b b a b1 b2)
      -> differ2 b a (oterm op bs1) (oterm op bs2)
with differ2_b {o} (b : nat) (a : get_patom_set o) : @BTerm o -> @BTerm o -> Type :=
     | differ2_bterm :
         forall vs t1 t2,
           differ2 b a t1 t2
           -> differ2_b b a (bterm vs t1) (bterm vs t2).
Hint Constructors differ2 differ2_b.

Definition differ2_alpha {o} b a (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
      & alpha_eq t1 u1
      # alpha_eq t2 u2
      # differ2 b a u1 u2}}.

Definition differ2_implies_differ2_alpha {o} :
  forall b a (t1 t2 : @NTerm o),
    differ2 b a t1 t2 -> differ2_alpha b a t1 t2.
Proof.
  introv d.
  exists t1 t2; auto.
Qed.
Hint Resolve differ2_implies_differ2_alpha : slow.

Inductive differ2_subs {o} b a : @Sub o -> @Sub o -> Type :=
| dsub_nil : differ2_subs b a [] []
| dsub_cons :
    forall v t1 t2 sub1 sub2,
      differ2 b a t1 t2
      -> differ2_subs b a sub1 sub2
      -> differ2_subs b a ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors differ2_subs.

Definition differ2_bterms {o} b a (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ2_b b a) bs1 bs2.

Lemma differ2_subs_sub_find_some {o} :
  forall b a (sub1 sub2 : @Sub o) v t,
    differ2_subs b a sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # differ2 b a t u}.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma differ2_subs_sub_find_none {o} :
  forall b a (sub1 sub2 : @Sub o) v,
    differ2_subs b a sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma differ2_subs_filter {o} :
  forall b a (sub1 sub2 : @Sub o) l,
    differ2_subs b a sub1 sub2
    -> differ2_subs b a (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.

Lemma differ2_lsubst_aux {o} :
  forall b a (t1 t2 : @NTerm o) sub1 sub2,
    differ2 b a t1 t2
    -> differ2_subs b a sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> differ2 b a (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind t1 as [v|op bs ind] Case;
  introv dt ds disj1 disj2; allsimpl.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ2_subs_sub_find_some b a sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ2_subs_sub_find_none b a sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "oterm".
    inversion dt as [|?|? ? ? len imp]; subst; allsimpl.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      rw @sub_find_sub_filter; tcsp.
      fold_terms.
      apply differ2_force_int.

      apply (ind t1 []); auto.

    + apply differ2_oterm; allrw map_length; auto.

      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      applydup imp in i1.
      destruct a1 as [l1 t1].
      destruct a0 as [l2 t2].
      applydup in_combine in i1; repnd.
      allsimpl.
      inversion i0 as [? ? ? d]; subst; clear i0.
      constructor.
      apply (ind t1 l2); auto.

      * apply differ2_subs_filter; auto.

      * pose proof (subvars_sub_free_vars_sub_filter sub1 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.

      * pose proof (subvars_sub_free_vars_sub_filter sub2 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.
Qed.

Lemma differ2_refl {o} :
  forall b a (t : @NTerm o),
    differ2 b a t t.
Proof.
  nterm_ind t as [v|op bs ind] Case; auto.

  Case "oterm".
  apply differ2_oterm; auto.
  introv i.
  rw in_combine_same in i; repnd; subst.
  destruct b2 as [l t].
  constructor.
  eapply ind; eauto.
Qed.
Hint Resolve differ2_refl : slow.

Lemma differ2_subs_refl {o} :
  forall b a (sub : @Sub o),
    differ2_subs b a sub sub.
Proof.
  induction sub; auto.
  destruct a0.
  constructor; eauto with slow.
Qed.
Hint Resolve differ2_subs_refl : slow.

Lemma differ2_change_bound_vars {o} :
  forall b a vs (t1 t2 : @NTerm o),
    differ2 b a t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
           & differ2 b a u1 u2
           # alpha_eq t1 u1
           # alpha_eq t2 u2
           # disjoint (bound_vars u1) vs
           # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind t1 as [v|op bs ind] Case; introv d.

  - Case "vterm".
    inversion d; subst.
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto with slow.

  - Case "oterm".
    inversion d as [? ? ? d1|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.

    + pose proof (ex_fresh_var vs) as h; exrepnd.
      pose proof (ind t1 []) as h; repeat (autodimp h hyp).
      pose proof (h t0 d1) as k; clear h; exrepnd.

      fold_terms.

      exists
        (mk_cbv u1 v0 (less_bound b (mk_var v0) (uexc a)))
        (force_int u2); dands; auto.

      * apply differ2_force_int; auto.

      * apply alpha_eq_force_int_bound; simpl; tcsp.

      * apply alpha_eq_force_int; auto.

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; rw disjoint_cons_l; dands; eauto with slow.

      * simpl; allrw app_nil_r; eauto with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
                  & alpha_eq_bterms bs bs'
                  # alpha_eq_bterms bs2 bs2'
                  # differ2_bterms b a bs' bs2'
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
          { apply alpha_bterm_change_aux; eauto with slow.
            allrw disjoint_app_l; dands; eauto with slow. }
          { apply alpha_bterm_change_aux; eauto with slow.
            allrw disjoint_app_l; dands; eauto with slow. }
          { apply differ2_bterm.
            apply differ2_lsubst_aux; eauto with slow;
            rw @sub_free_vars_var_ren; eauto with slow. }
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
      allunfold @differ2_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands; eauto with slow.

      * apply alpha_eq_oterm_combine; dands; auto.

      * apply alpha_eq_oterm_combine; dands; auto.
Qed.

Lemma differ2_subst {o} :
  forall b a (t1 t2 : @NTerm o) sub1 sub2,
    differ2 b a t1 t2
    -> differ2_subs b a sub1 sub2
    -> differ2_alpha b a (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  rw h0; rw k0.

  pose proof (differ2_change_bound_vars
                b a (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2 dt) as d; exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply differ2_lsubst_aux; auto.
Qed.
Hint Resolve differ2_subst : slow.

Definition differ2_sk {o} b a (sk1 sk2 : @sosub_kind o) :=
  differ2_b b a (sk2bterm sk1) (sk2bterm sk2).

Inductive differ2_sosubs {o} b a : @SOSub o -> @SOSub o -> Type :=
| dsosub2_nil : differ2_sosubs b a [] []
| dsosub2_cons :
    forall v sk1 sk2 sub1 sub2,
      differ2_sk b a sk1 sk2
      -> differ2_sosubs b a sub1 sub2
      -> differ2_sosubs b a ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors differ2_sosubs.

Lemma differ2_bterms_implies_eq_map_num_bvars {o} :
  forall b a (bs1 bs2 : list (@BTerm o)),
    differ2_bterms b a bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv d; allsimpl; auto;
  allunfold @differ2_bterms; allunfold @br_bterms; allunfold @br_list;
  allsimpl; repnd; cpx.
  pose proof (d a0 b0) as h; autodimp h hyp.
  inversion h; subst.
  f_equal.
  unfold num_bvars; simpl; auto.
Qed.

Lemma differ2_bterms_cons {o} :
  forall b a (b1 b2 : @BTerm o) bs1 bs2,
    differ2_bterms b a (b1 :: bs1) (b2 :: bs2)
    <=> (differ2_b b a b1 b2 # differ2_bterms b a bs1 bs2).
Proof.
  unfold differ2_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma differ2_mk_abs_substs {o} :
  forall b a (bs1 bs2 : list (@BTerm o)) vars,
    differ2_bterms b a bs1 bs2
    -> length vars = length bs1
    -> differ2_sosubs b a (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv d m; allsimpl; cpx; tcsp.
  - provefalse.
    apply differ2_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx.
  - apply differ2_bterms_cons in d; repnd.
    destruct s, a0, b0.
    inversion d0; subst.
    boolvar; auto.
Qed.

Lemma differ2_b_change_bound_vars {o} :
  forall b a vs (b1 b2 : @BTerm o),
    differ2_b b a b1 b2
    -> {u1 : BTerm
        & {u2 : BTerm
           & differ2_b b a u1 u2
           # alpha_eq_bterm b1 u1
           # alpha_eq_bterm b2 u2
           # disjoint (bound_vars_bterm u1) vs
           # disjoint (bound_vars_bterm u2) vs}}.
Proof.
  introv d.
  pose proof (differ2_change_bound_vars
                b a vs (oterm (Exc None) [b1]) (oterm (Exc None) [b2])) as h.
  autodimp h hyp.
  - apply differ2_oterm; simpl; auto.
    introv i; dorn i; tcsp; cpx.
  - exrepnd.
    inversion h2 as [|? ? ? len1 imp1]; subst; allsimpl; cpx.
    inversion h3 as [|? ? ? len2 imp2]; subst; allsimpl; cpx.
    pose proof (imp1 0) as k1; autodimp k1 hyp; allsimpl; clear imp1.
    pose proof (imp2 0) as k2; autodimp k2 hyp; allsimpl; clear imp2.
    allunfold @selectbt; allsimpl.
    allrw app_nil_r.
    exists x x0; dands; auto.
    inversion h0 as [|?|? ? ? ? i]; subst; allsimpl; GC.
    apply i; sp.
Qed.

Lemma differ2_sk_change_bound_vars {o} :
  forall b a vs (sk1 sk2 : @sosub_kind o),
    differ2_sk b a sk1 sk2
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
           & differ2_sk b a u1 u2
           # alphaeq_sk sk1 u1
           # alphaeq_sk sk2 u2
           # disjoint (bound_vars_sk u1) vs
           # disjoint (bound_vars_sk u2) vs}}.
Proof.
  introv d.
  unfold differ2_sk in d.
  apply (differ2_b_change_bound_vars b a vs) in d; exrepnd; allsimpl.
  exists (bterm2sk u1) (bterm2sk u2).
  destruct u1, u2, sk1, sk2; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ2_sosubs_change_bound_vars {o} :
  forall b a vs (sub1 sub2 : @SOSub o),
    differ2_sosubs b a sub1 sub2
    -> {sub1' : SOSub
        & {sub2' : SOSub
           & differ2_sosubs b a sub1' sub2'
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
    apply (differ2_sk_change_bound_vars b a vs) in dsk; exrepnd.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto with slow.
Qed.

Lemma sosub_find_some_if_differ2_sosubs {o} :
  forall b a (sub1 sub2 : @SOSub o) v sk,
    differ2_sosubs b a sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind & differ2_sk b a sk sk' # sosub_find sub2 v = Some sk'}.
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

Lemma sosub_find_none_if_differ2_sosubs {o} :
  forall b a (sub1 sub2 : @SOSub o) v,
    differ2_sosubs b a sub1 sub2
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

Lemma differ2_subs_combine {o} :
  forall b a (ts1 ts2 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> (forall t1 t2,
          LIn (t1,t2) (combine ts1 ts2)
          -> differ2 b a t1 t2)
    -> differ2_subs b a (combine vs ts1) (combine vs ts2).
Proof.
  induction ts1; destruct ts2; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma differ2_apply_list {o} :
  forall b a (ts1 ts2 : list (@NTerm o)) t1 t2,
    differ2 b a t1 t2
    -> length ts1 = length ts2
    -> (forall x y, LIn (x,y) (combine ts1 ts2) -> differ2 b a x y)
    -> differ2 b a (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; destruct ts2; introv d l i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ2_oterm; simpl; auto.
  introv k.
  dorn k;[|dorn k]; cpx; constructor; auto.
Qed.

Lemma differ2_sosub_filter {o} :
  forall b a (sub1 sub2 : @SOSub o) vs,
    differ2_sosubs b a sub1 sub2
    -> differ2_sosubs b a (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ2_sosub_filter : slow.

Lemma differ2_sosub_aux {o} :
  forall b a (t : @SOTerm o) sub1 sub2,
    differ2_sosubs b a sub1 sub2
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ2 b a (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case;
  introv ds disj1 disj2 disj3 disj4 disj5 disj6 cov1 cov2; allsimpl.

  - Case "sovar".
    allrw @cover_so_vars_sovar; repnd.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ2_sosubs b a sub1 sub2) in Heqf1; auto.
      exrepnd.
      rw Heqf2.
      destruct s as [l1 t1].
      destruct sk' as [l2 t2].
      inversion Heqf0; subst.
      apply differ2_lsubst_aux; auto.

      * apply differ2_subs_combine; allrw map_length; auto.
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

    + applydup (sosub_find_none_if_differ2_sosubs b a sub1 sub2) in Heqf1; auto.
      rw Heqf0.
      apply differ2_apply_list; allrw map_length; auto.
      introv i.
      rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
      apply in_combine_same in i1; repnd; subst; allsimpl.
      disj_flat_map.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm.
    apply differ2_oterm; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
    apply in_combine_same in i1; repnd; subst; allsimpl.
    destruct a0 as [l t].
    disj_flat_map.
    allsimpl; allrw disjoint_app_l; repnd.
    constructor.
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

Lemma differ2_sosub {o} :
  forall b a (t : @SOTerm o) (sub1 sub2 : SOSub),
    differ2_sosubs b a sub1 sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ2_alpha b a (sosub sub1 t) (sosub sub2 t).
Proof.
  introv d c1 c2.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.

  pose proof (differ2_sosubs_change_bound_vars
                b a
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

  apply differ2_sosub_aux; auto.

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub1 sub1''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub1); auto. }

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub2 sub2''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub2); auto. }
Qed.

Lemma differ2_mk_instance {o} :
  forall b a (t : @SOTerm o) vars bs1 bs2,
    matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered t vars
    -> socovered t vars
    -> differ2_bterms b a bs1 bs2
    -> differ2_alpha b a (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv m1 m2 sc1 sc2 dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ2_mk_abs_substs o b a bs1 bs2 vars) in dbs; auto.

  apply differ2_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Lemma implies_differ2_alpha_force_int {o} :
  forall v b a (t1 t2 : @NTerm o),
    differ2_alpha b a t1 t2
    -> differ2_alpha b a (force_int_bound v b t1 (uexc a)) (force_int t2).
Proof.
  introv d.
  unfold differ2_alpha in d; exrepnd.
  exists (force_int_bound v b u1 (uexc a)) (force_int u2); dands.
  - apply alpha_eq_force_int_bound; allsimpl; tcsp.
  - apply alpha_eq_force_int; auto.
  - apply differ2_force_int; auto.
Qed.

Lemma differ2_oterm_not_in_utokens {o} :
  forall b a ncan bs (t : @NTerm o),
    differ2 b a (oterm (NCan ncan) bs) t
    -> !LIn a (get_utokens t)
    -> !LIn a (get_utokens_nc ncan).
Proof.
  introv d ni i.
  inversion d as [? ? ? d1|?|? ? ? len imp]; subst; allsimpl; tcsp.
  allrw in_app_iff; allrw not_over_or; repnd; tcsp.
Qed.

Lemma comp_force_int_step2 {o} :
  forall lib a (t1 t2 : @NTerm o) b u,
    !LIn a (get_utokens t2)
    -> differ2 b a t1 t2
    -> compute_step lib t1 = csuccess u
    -> has_value_like_except lib a u
    -> {t : NTerm
        & {u' : NTerm
           & reduces_to lib t2 t
           # reduces_to lib u u'
           # differ2_alpha b a u' t}}.
Proof.
  nterm_ind t1 as [v|op bs ind] Case; introv ni d comp hv.

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
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can NLambda) [bterm [v] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] arg) b2) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (bterm [v] b0) b1) as d1.
            autodimp d1 hyp.
            clear imp1.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            exists (subst t2 v t0) (subst b0 v arg); dands; eauto with slow.

            apply differ2_subst; auto.

          - SSSCase "NFix".
            allsimpl.
            apply compute_step_fix_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2.

            exists (mk_apply
                      (oterm (Can can1) bs2)
                      (oterm (NCan NFix) [bterm [] (oterm (Can can1) bs2)]))
                   (mk_apply (oterm (Can can1) bs1)
                             (oterm (NCan NFix) [bterm [] (oterm (Can can1) bs1)])).
            dands; eauto with slow.

            apply differ2_implies_differ2_alpha.
            apply differ2_oterm; simpl; auto.
            introv j.

            dorn j; cpx.

            { constructor.
              apply differ2_oterm; simpl; auto. }

            { dorn j; cpx.
              constructor.
              apply differ2_oterm; allsimpl; auto.
              introv j.
              dorn j; cpx. }

          - SSSCase "NSpread".
            allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can NPair) [nobnd a0, nobnd b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) b2) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (nobnd a0) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b0) b2) as d2.
            autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? d5]; subst; clear d1.
            inversion d2 as [? ? ? d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)])
                   (lsubst arg [(va,a0),(vb,b0)]); dands; eauto with slow.

          - SSSCase "NDsup".
            allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can NSup) [nobnd a0, nobnd b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) b2) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (nobnd a0) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b0) b2) as d2.
            autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? d5]; subst; clear d1.
            inversion d2 as [? ? ? d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)])
                   (lsubst arg [(va,a0),(vb,b0)]); dands; eauto with slow.

          - SSSCase "NDecide".
            allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can can1) [nobnd d0])) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v1] t1) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v2] t0) b2) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (nobnd d0) b0) as d1.
            autodimp d1 hyp.
            clear imp1.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            dorn comp0; repnd; subst.

            + exists (subst t4 v1 t3)
                     (subst t1 v1 d0);
                dands; eauto with slow.

              apply differ2_subst; auto.

            + exists (subst t5 v2 t3)
                     (subst t0 v2 d0);
                dands; eauto with slow.

              apply differ2_subst; auto.

          - SSSCase "NCbv".
            allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? d1|?|? ? ? len imp]; subst; allsimpl; clear d.

            + inversion d1 as [?|?|? ? ? len imp]; subst; allsimpl; clear d1.

              apply has_value_like_except_subst_less_bound in hv; exrepnd; subst.

              allsimpl; cpx; GC.
              exists (@mk_integer o z) (@mk_integer o z); dands; eauto with slow.

              * apply reduces_to_if_step; simpl.
                unfold compute_step_arith; simpl.
                allrw <- Zplus_0_r_reverse; auto.

              * unfold subst, lsubst; simpl; boolvar; GC.
                destruct (Z_lt_le_dec z 0) as [h|h].

                { apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_minus (mk_integer z)) (mk_nat b) (mk_integer z) (uexc a)));
                  [ simpl; boolvar; tcsp; omega|].

                  apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_integer (- z)) (mk_nat b) (mk_integer z) (uexc a)));
                    auto.
                  apply reduces_to_if_step; simpl.
                  unfold compute_step_comp; simpl; boolvar; tcsp; try omega.
                  provefalse.
                  pose proof (abs_of_neg2 z b); sp; try omega.
                }

                { apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_integer z) (mk_nat b) (mk_integer z) (uexc a)));
                  [ simpl; boolvar; tcsp; omega|].

                  apply reduces_to_if_step; simpl.
                  unfold compute_step_comp; simpl; boolvar; tcsp; try omega.
                  provefalse.
                  pose proof (abs_of_pos2 z b); sp; try omega.
                }

            + destruct bs2; allsimpl; cpx.
              destruct bs2; allsimpl; cpx.
              destruct bs2; allsimpl; cpx.
              GC.

              pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v] x) b1) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.

              exists (subst t0 v (oterm (Can can1) bs2))
                     (subst x v (oterm (Can can1) bs1));
                dands; eauto with slow.

              apply differ2_subst; auto.

          - SSSCase "NSleep".
            allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_axiom o) (@mk_axiom o); dands; eauto with slow.

          - SSSCase "NTUni".
            allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint (Z.of_nat n))) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_uni o n) (@mk_uni o n); dands; eauto with slow.

            apply reduces_to_if_step; simpl.
            unfold compute_step_tuni; simpl; boolvar; tcsp; try omega.
            rw Znat.Nat2Z.id; auto.

          - SSSCase "NMinus".
            allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl; GC.

            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_integer o (- z)) (@mk_integer o (- z)); dands; eauto with slow.

          - SSSCase "NTryCatch".
            allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl; GC.

            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            destruct bs2; allsimpl; repeat cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] x) x0) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3; cpx.

            exists (oterm (Can can1) bs2) (oterm (Can can1) bs1); dands; eauto with slow.

          - SSSCase "NCompOp".
            destruct bs; try (complete (allsimpl; ginv)).
            destruct b0 as [l t].
            destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; ginv)).

            inversion d as [? ? ? ? d1|?|? ? ? len imp]; subst; clear d.
            simpl in len.

            destruct bs3; simpl in len; cpx.
            destruct bs3; simpl in len; cpx.
            simpl in imp.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|mrk3|abs3] SSSSCase.

            + SSSSCase "Can".
              simpl in comp.

              inversion d4 as [|?|? ? ? len2 imp2]; subst; clear d4; cpx.

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

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

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

              pose proof (ind (oterm (NCan ncan3) bs2) []) as h; clear ind.
              autodimp h hyp; tcsp.

              pose proof (h t0 b n) as k; clear h.
              repeat (autodimp k hyp).

              { simpl in ni; introv j; simpl in j.
                allrw in_app_iff.
                allrw not_over_or; sp. }

              { apply if_has_value_like_except_ncompop_can1 in hv; auto. }

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

              * unfold differ2_alpha in k1; exrepnd.
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
                  introv j; destruct n0;[|destruct n0]; try omega; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try omega; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { apply differ2_oterm; simpl; auto.
                  introv j; dorn j; cpx.
                  dorn j; cpx. }

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

              inversion d4 as [|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

              assert (differ2_bterms b a bs2 bs5) as dbs.
              { unfold differ2_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ2_bterms_implies_eq_map_num_bvars in dbs; auto. }

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

             * pose proof (differ2_mk_instance b a rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp).
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ2_alpha in h.
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
                 introv j; destruct n;[|destruct n]; try omega; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try omega; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ2_oterm; allsimpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

          - SSSCase "NArithOp".
            destruct bs; try (complete (allsimpl; ginv)).
            destruct b0 as [l t].
            destruct l; destruct t as [v|op bs2]; try (complete (allsimpl; ginv)).

            inversion d as [? ? ? ? d1|?|? ? ? len imp]; subst; clear d.
            simpl in len.

            destruct bs3; simpl in len; cpx.
            destruct bs3; simpl in len; cpx.
            simpl in imp.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|mrk3|abs3] SSSSCase.

            + SSSSCase "Can".
              simpl in comp.

              inversion d4 as [|?|? ? ? len2 imp2]; subst; clear d4; cpx.

              apply compute_step_arithop_success_can_can in comp.
              exrepnd; subst.
              allsimpl; cpx.
              clear imp1 imp2 imp.

              allapply @get_int_from_cop_some; subst; allsimpl; GC.

              exists (@oterm o (Can (Nint (get_arith_op a0 n1 n2))) [])
                     (@oterm o (Can (Nint (get_arith_op a0 n1 n2))) []);
                dands; eauto with slow.

            + SSSSCase "NCan".
              rw @compute_step_narithop_ncan2 in comp.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) []) as h; clear ind.
              autodimp h hyp; tcsp.

              pose proof (h t0 b n) as k; clear h.
              repeat (autodimp k hyp).

              { simpl in ni; introv j; simpl in j.
                allrw in_app_iff.
                allrw not_over_or; sp. }

              { apply if_has_value_like_except_arithop_can1 in hv; auto. }

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

              * unfold differ2_alpha in k1; exrepnd.
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
                  introv j; destruct n0;[|destruct n0]; try omega; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { prove_alpha_eq4.
                  introv j; destruct n0;[|destruct n0]; try omega; cpx.
                  apply alphaeqbt_nilv2; auto. }

                { apply differ2_oterm; simpl; auto.
                  introv j; dorn j; cpx.
                  dorn j; cpx. }

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

              inversion d4 as [|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

              assert (differ2_bterms b a bs2 bs5) as dbs.
              { unfold differ2_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ2_bterms_implies_eq_map_num_bvars in dbs; auto. }

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

             * pose proof (differ2_mk_instance b a rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp).
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ2_alpha in h.
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
                 introv j; destruct n;[|destruct n]; try omega; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { prove_alpha_eq4.
                 introv j; destruct n;[|destruct n]; try omega; cpx.
                 apply alphaeqbt_nilv2; auto. }

               { apply differ2_oterm; allsimpl; auto.
                 introv j; dorn j; cpx.
                 dorn j; cpx. }

          - SSSCase "NCanTest".
            allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl.
            inversion d as [?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] arg2nt) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [] arg3nt) b2) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.

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

          inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.

          - pose proof (ind (oterm (NCan ncan1) bs1) []) as h.
            autodimp h hyp; tcsp.

            simpl in ni; allrw app_nil_r.

            pose proof (h t0 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_has_value_like_except_force_int_bound in hv; exrepnd.
              unfold has_value_like_except.
              exists u; dands; eauto with slow.
              dorn hv0; exrepnd; subst; simpl; tcsp.
              intro k.
              allapply @isnexc_implies; exrepnd; subst; ginv; tcsp. }

            exrepnd.

            exists (force_int t) (force_int_bound v b u' (uexc a)); dands; eauto with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { apply implies_differ2_alpha_force_int; auto. }

          - simpl in len.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (NCan ncan1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.

            simpl in ni; allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (ind (oterm (NCan ncan1) bs1) []) as h.
            autodimp h hyp; tcsp.
            pose proof (h t2 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_has_value_like_except_ncan_primarg in hv; auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { unfold differ2_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              - apply differ2_oterm; simpl; auto.
                introv j; dorn j; cpx.
            }
        }

        { SSCase "Exc".
          simpl in comp.
          apply compute_step_catch_success in comp.
          dorn comp; exrepnd; subst.

          - inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.
            allsimpl.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.
            allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (imp (bterm [] (oterm (Exc exc1) [bterm [] e])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] b0) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [? ? ? d1|?|? ? ? len1 imp1]; subst; clear d3.
            allsimpl; cpx.
            allsimpl.
            allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (imp1 (bterm [] e) x) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            clear imp1.
            allsimpl.

            exists (subst t0 v t2) (subst b0 v e); dands; eauto with slow.

            { apply reduces_to_if_step; simpl.
              boolvar; tcsp. }

            { apply differ2_subst; auto. }

          - inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.
            allsimpl.

            + inversion d1 as [?|?|? ? ? len imp]; subst; clear d1.
              allsimpl.
              allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
              apply if_has_value_like_except_exc in hv.
              exists (oterm (Exc exc1) bs2) (oterm (Exc exc1) bs1).
              dands; eauto with slow.

            + allsimpl.
              destruct bs2; allsimpl; cpx.

              pose proof (imp (bterm [] (oterm (Exc exc1) bs1)) b0) as d1.
              autodimp d1 hyp.
              inversion d1 as [? ? ? d2]; subst; clear d1.
              inversion d2 as [?|?|? ? ? len1 imp1]; subst; clear d2.

              allsimpl.
              allrw in_app_iff; allrw not_over_or; repnd.
              exists (oterm (Exc exc1) bs3) (oterm (Exc exc1) bs1).
              dands; eauto with slow.

              apply reduces_to_if_step; simpl.
              unfold compute_step_catch; destruct ncan; tcsp.
              boolvar; subst; tcsp.
        }

        { SSCase "Mrk".
          allsimpl; ginv.
          unfold has_value_like_except in hv; exrepnd.
          unfold reduces_to in hv1; exrepnd.
          apply reduces_in_atmost_k_steps_primarg_marker in hv3; subst.
          unfold isvalue_like in hv2; allsimpl; sp.
        }

        { SSCase "Abs".
          allsimpl.
          unfold on_success in comp.
          remember (compute_step_lib lib abs1 bs1) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.

          - pose proof (ind (oterm (Abs abs1) bs1) []) as h.
            autodimp h hyp; tcsp.

            simpl in ni; allrw app_nil_r.

            pose proof (h t0 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_has_value_like_except_force_int_bound in hv; exrepnd.
              unfold has_value_like_except.
              exists u; dands; eauto with slow.
              dorn hv0; exrepnd; subst; simpl; tcsp.
              intro k.
              allapply @isnexc_implies; exrepnd; subst; ginv; tcsp. }

            exrepnd.

            exists (force_int t) (force_int_bound v b u' (uexc a)); dands; eauto with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { apply implies_differ2_alpha_force_int; auto. }

          - simpl in len.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (Abs abs1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.

            simpl in ni; allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (ind (oterm (Abs abs1) bs1) []) as h.
            autodimp h hyp; tcsp.
            pose proof (h t2 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_has_value_like_except_ncan_primarg in hv; auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { unfold differ2_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              - apply differ2_oterm; simpl; auto.
                introv j; dorn j; cpx.
            }
        }

    + SCase "Exc".
      allsimpl; ginv.
      inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.
      exists (oterm (Exc exc) bs2) (oterm (Exc exc) bs).
      dands; eauto with slow.

    + SCase "Mrk".
      allsimpl; ginv.
      inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.
      exists (oterm (Mrk mrk) bs2) (oterm (Mrk mrk) bs).
      dands; eauto with slow.

    + SCase "Abs".
      inversion d as [? ? ? d1|?|? ? ? len imp]; subst; clear d.
      allsimpl.
      apply compute_step_lib_success in comp; exrepnd; subst.

      assert (differ2_bterms b a bs bs2) as dbs.
      { unfold differ2_bterms, br_bterms, br_list; auto. }

      pose proof (found_entry_change_bs abs oa2 vars rhs lib bs correct bs2) as fe2.
      repeat (autodimp fe2 hyp).

      { apply differ2_bterms_implies_eq_map_num_bvars in dbs; auto. }

      exists (mk_instance vars bs2 rhs) (mk_instance vars bs rhs).

      dands; eauto with slow.

      * apply reduces_to_if_step.
        simpl; unfold on_success.
        applydup @compute_step_lib_if_found_entry in fe2.
        rw fe0; auto.

      * pose proof (differ2_mk_instance b a rhs vars bs bs2) as h.
        repeat (autodimp h hyp).
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allunfold @correct_abs; sp. }
        { allunfold @correct_abs; sp. }
Qed.

Lemma comp_force_int2 {o} :
  forall lib a (t1 t2 : @NTerm o) b z,
    !LIn a (get_utokens t2)
    -> differ2 b a t1 t2
    -> reduces_to lib t1 (mk_integer z)
    -> reduces_to lib t2 (mk_integer z).
Proof.
  introv ni d comp.
  unfold reduces_to in comp; exrepnd.
  revert dependent t2.
  revert dependent t1.
  induction k as [n ind] using comp_ind_type; introv r ni d.
  destruct n as [|k]; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion d as [?|?|? ? ? len imp]; subst; clear d.
    allsimpl; cpx; eauto with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    pose proof (comp_force_int_step2 lib a t1 t2 b u) as h.
    repeat (autodimp h hyp).

    { unfold has_value_like_except.
      exists (@mk_integer o z); dands; eauto with slow; tcsp.
      - exists k; auto.
      - unfold isvalue_like; simpl; tcsp. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to
                  lib k u u' (mk_integer z)) as h'.
    repeat (autodimp h' hyp).
    { left; sp. }
    exrepnd.

    unfold differ2_alpha in h1; exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u' u1) as h''.
    autodimp h'' hyp.

    pose proof (h'' k' (mk_integer z)) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.
    inversion h'''0 as [|? ? ? ? x]; subst; allsimpl; cpx;
    clear x h'''0.
    fold_terms.

    pose proof (ind k') as h.
    autodimp h hyp;[omega|].
    pose proof (h u1) as r; clear h.
    autodimp r hyp.

    pose proof (r u2) as h; clear r; repeat (autodimp h hyp).

    { introv i.
      allapply @get_utokens_alpha_eq.
      rw <- h4 in i.
      apply reduces_to_preserves_utokens in h0.
      apply h0 in i; sp. }

    pose proof (reduces_to_steps_alpha lib u2 t (mk_integer z)) as r.
    repeat (autodimp r hyp); eauto with slow.
    exrepnd.
    inversion r2; subst; allsimpl; cpx; fold_terms.
    eapply reduces_to_trans; eauto.
Qed.

Lemma old_differ_app_F2 {o} :
  forall (F g : @NTerm o) v x b a,
    differ2
      b a
      (mk_apply F (mk_lam x (mk_apply g (force_int_bound v b (mk_var x) (uexc a)))))
      (mk_apply F (mk_lam x (mk_apply g (force_int (mk_var x))))).
Proof.
  introv.
  constructor; simpl; auto.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto with slow.
  - constructor; constructor; simpl; auto.
    introv i; dorn i; cpx.
    constructor; constructor; simpl; auto.
    introv i; dorn i;[|dorn i]; cpx; auto.
    + constructor; eauto with slow.
    + constructor; constructor; auto.
Qed.

Lemma differ_app_F2 {o} :
  forall (F g : @NTerm o) x b a,
    differ2
      b a
      (force_int_bound_F x b F g (uexc a))
      (force_int_F x F g).
Proof.
  introv.
  constructor; simpl; auto.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto with slow.
  - constructor; constructor; simpl; auto.
    introv i; dorn i; cpx.
    constructor; constructor; simpl; auto.
    introv i; dorn i;[|dorn i]; cpx; auto.
    + constructor; eauto with slow.
    + constructor; constructor; simpl; auto.
      introv i; dorn i;[|dorn i]; cpx; auto.
      * constructor; eauto with slow.
      * constructor; constructor.
Qed.

(*

  F (\x.let x:=(x+0) in f(x)) -> z
  =>
  exists b.
    F (\x.let x:=(let v:=x in if |v|<b then v else e) in f(x)) -> z

*)
Lemma comp_force_int_app_F2 {o} :
  forall lib a (F g : @NTerm o) x z b,
    !LIn a (get_utokens F)
    -> !LIn a (get_utokens g)
    -> reduces_to
         lib
         (force_int_bound_F x b F g (uexc a))
         (mk_integer z)
    -> reduces_to
         lib
         (force_int_F x F g)
         (mk_integer z).
Proof.
  introv ni1 ni2 r.

  eapply (comp_force_int2 _ a _ _ b); eauto.

  - simpl; allrw app_nil_r; allrw in_app_iff; sp.

  - apply differ_app_F2.
Qed.
