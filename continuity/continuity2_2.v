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


Require Export atoms2.
Require Export computation_seq.
Require Export continuity_defs.
(*Require Export list.  (* why?? *)*)


Inductive differ2 {o} (b : nat) : @NTerm o -> @NTerm o -> Type :=
| differ2_force_int :
    forall t1 t2 v,
      differ2 b t1 t2
      -> differ2 b (force_int_bound v b t1 (mk_vbot v)) (force_int t2)
| differ2_var :
    forall v, differ2 b (mk_var v) (mk_var v)
| differ2_sterm :
    forall f, differ2 b (sterm f) (sterm f)
| differ2_oterm :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> differ2_b b b1 b2)
      -> differ2 b (oterm op bs1) (oterm op bs2)
with differ2_b {o} (b : nat) : @BTerm o -> @BTerm o -> Type :=
     | differ2_bterm :
         forall vs t1 t2,
           differ2 b t1 t2
           -> differ2_b b (bterm vs t1) (bterm vs t2).
Hint Constructors differ2 differ2_b.

Definition differ2_alpha {o} b (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
      & alpha_eq t1 u1
      # alpha_eq t2 u2
      # differ2 b u1 u2}}.

Definition differ2_implies_differ2_alpha {o} :
  forall b (t1 t2 : @NTerm o),
    differ2 b t1 t2 -> differ2_alpha b t1 t2.
Proof.
  introv d.
  exists t1 t2; auto.
Qed.
Hint Resolve differ2_implies_differ2_alpha : slow.

Inductive differ2_subs {o} b : @Sub o -> @Sub o -> Type :=
| dsub_nil : differ2_subs b [] []
| dsub_cons :
    forall v t1 t2 sub1 sub2,
      differ2 b t1 t2
      -> differ2_subs b sub1 sub2
      -> differ2_subs b ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors differ2_subs.

Definition differ2_bterms {o} b (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ2_b b) bs1 bs2.

Lemma differ2_subs_sub_find_some {o} :
  forall b (sub1 sub2 : @Sub o) v t,
    differ2_subs b sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # differ2 b t u}.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma differ2_subs_sub_find_none {o} :
  forall b (sub1 sub2 : @Sub o) v,
    differ2_subs b sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d f; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma differ2_subs_filter {o} :
  forall b (sub1 sub2 : @Sub o) l,
    differ2_subs b sub1 sub2
    -> differ2_subs b (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.

Lemma differ2_lsubst_aux {o} :
  forall b (t1 t2 : @NTerm o) sub1 sub2,
    differ2 b t1 t2
    -> differ2_subs b sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> differ2 b (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case;
  introv dt ds disj1 disj2; allsimpl; auto.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ2_subs_sub_find_some b sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ2_subs_sub_find_none b sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "sterm".
    inversion dt; subst; allsimpl; auto.

  - Case "oterm".
    inversion dt as [|?|?|? ? ? len imp]; subst; allsimpl.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      repeat (rw @sub_find_sub_filter; simpl; tcsp).
      fold_terms.
      apply differ2_force_int.

      apply (ind t1 []); auto.

    + apply differ2_oterm; allrw map_length; auto.

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
  forall b (t : @NTerm o),
    differ2 b t t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; auto.

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
  forall b (sub : @Sub o),
    differ2_subs b sub sub.
Proof.
  induction sub; auto.
  destruct a.
  constructor; eauto 3 with slow.
Qed.
Hint Resolve differ2_subs_refl : slow.

Lemma differ2_change_bound_vars {o} :
  forall b vs (t1 t2 : @NTerm o),
    differ2 b t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
           & differ2 b u1 u2
           # alpha_eq t1 u1
           # alpha_eq t2 u2
           # disjoint (bound_vars u1) vs
           # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind t1 as [v|f ind|op bs ind] Case; introv d; auto.

  - Case "vterm".
    inversion d; subst.
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto 3 with slow.

  - Case "sterm".
    inversion d; subst; clear d.
    exists (sterm f) (sterm f); simpl; dands; auto.

  - Case "oterm".
    inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.

    + pose proof (ex_fresh_var vs) as h; exrepnd.
      pose proof (ind t1 []) as h; repeat (autodimp h hyp).
      pose proof (h t0 d1) as k; clear h; exrepnd.

      fold_terms.

      exists
        (mk_cbv u1 v0 (less_bound b (mk_var v0) (mk_vbot v0)))
        (force_int u2); dands; auto.

      * apply differ2_force_int; auto.

      * apply alpha_eq_force_int_bound; simpl; tcsp;
        allrw remove_nvars_eq; allsimpl; tcsp; eauto 3 with slow.

      * apply alpha_eq_force_int; auto.

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; rw disjoint_cons_l; dands; eauto 3 with slow.
        rw disjoint_singleton_l; auto.

      * simpl; allrw app_nil_r; eauto 3 with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
                  & alpha_eq_bterms bs bs'
                  # alpha_eq_bterms bs2 bs2'
                  # differ2_bterms b bs' bs2'
                  # disjoint (flat_map bound_vars_bterm bs') vs
                  # disjoint (flat_map bound_vars_bterm bs2') vs}}) as h.

      { revert dependent bs2.
        induction bs; destruct bs2; introv len imp; allsimpl; ginv.
        - exists ([] : list (@BTerm o)) ([] : list (@BTerm o));
            dands; simpl; eauto 3 with slow; try (apply br_bterms_nil).
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
          { apply differ2_bterm.
            apply differ2_lsubst_aux; eauto 3 with slow;
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
      allunfold @differ2_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands; eauto 3 with slow.

      * apply alpha_eq_oterm_combine; dands; auto.

      * apply alpha_eq_oterm_combine; dands; auto.
Qed.

Lemma differ2_subst {o} :
  forall b (t1 t2 : @NTerm o) sub1 sub2,
    differ2 b t1 t2
    -> differ2_subs b sub1 sub2
    -> differ2_alpha b (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  rw h0; rw k0.

  pose proof (differ2_change_bound_vars
                b (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2 dt) as d; exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto 3 with slow.

  - apply lsubst_aux_alpha_congr2; eauto 3 with slow.

  - apply differ2_lsubst_aux; auto.
Qed.
Hint Resolve differ2_subst : slow.

Definition differ2_sk {o} b (sk1 sk2 : @sosub_kind o) :=
  differ2_b b (sk2bterm sk1) (sk2bterm sk2).

Inductive differ2_sosubs {o} b : @SOSub o -> @SOSub o -> Type :=
| dsosub2_nil : differ2_sosubs b [] []
| dsosub2_cons :
    forall v sk1 sk2 sub1 sub2,
      differ2_sk b sk1 sk2
      -> differ2_sosubs b sub1 sub2
      -> differ2_sosubs b ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors differ2_sosubs.

Lemma differ2_bterms_implies_eq_map_num_bvars {o} :
  forall b (bs1 bs2 : list (@BTerm o)),
    differ2_bterms b bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv d; allsimpl; auto;
  allunfold @differ2_bterms; allunfold @br_bterms; allunfold @br_list;
  allsimpl; repnd; cpx.
  pose proof (d a b0) as h; autodimp h hyp.
  inversion h; subst.
  f_equal.
  unfold num_bvars; simpl; auto.
Qed.

Lemma differ2_bterms_cons {o} :
  forall b (b1 b2 : @BTerm o) bs1 bs2,
    differ2_bterms b (b1 :: bs1) (b2 :: bs2)
    <=> (differ2_b b b1 b2 # differ2_bterms b bs1 bs2).
Proof.
  unfold differ2_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma differ2_mk_abs_substs {o} :
  forall b (bs1 bs2 : list (@BTerm o)) vars,
    differ2_bterms b bs1 bs2
    -> length vars = length bs1
    -> differ2_sosubs b (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv d m; allsimpl; cpx; tcsp.
  - provefalse.
    apply differ2_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx.
  - apply differ2_bterms_cons in d; repnd.
    destruct s, a, b0.
    inversion d0; subst.
    boolvar; auto.
Qed.

Lemma differ2_b_change_bound_vars {o} :
  forall b vs (b1 b2 : @BTerm o),
    differ2_b b b1 b2
    -> {u1 : BTerm
        & {u2 : BTerm
           & differ2_b b u1 u2
           # alpha_eq_bterm b1 u1
           # alpha_eq_bterm b2 u2
           # disjoint (bound_vars_bterm u1) vs
           # disjoint (bound_vars_bterm u2) vs}}.
Proof.
  introv d.
  pose proof (differ2_change_bound_vars
                b vs (oterm Exc [b1]) (oterm Exc [b2])) as h.
  autodimp h hyp.
  - apply differ2_oterm; simpl; auto.
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

Lemma differ2_sk_change_bound_vars {o} :
  forall b vs (sk1 sk2 : @sosub_kind o),
    differ2_sk b sk1 sk2
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
           & differ2_sk b u1 u2
           # alphaeq_sk sk1 u1
           # alphaeq_sk sk2 u2
           # disjoint (bound_vars_sk u1) vs
           # disjoint (bound_vars_sk u2) vs}}.
Proof.
  introv d.
  unfold differ2_sk in d.
  apply (differ2_b_change_bound_vars b vs) in d; exrepnd; allsimpl.
  exists (bterm2sk u1) (bterm2sk u2).
  destruct u1, u2, sk1, sk2; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ2_sosubs_change_bound_vars {o} :
  forall b vs (sub1 sub2 : @SOSub o),
    differ2_sosubs b sub1 sub2
    -> {sub1' : SOSub
        & {sub2' : SOSub
           & differ2_sosubs b sub1' sub2'
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
    apply (differ2_sk_change_bound_vars b vs) in dsk; exrepnd.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto 3 with slow.
Qed.

Lemma sosub_find_some_if_differ2_sosubs {o} :
  forall b (sub1 sub2 : @SOSub o) v sk,
    differ2_sosubs b sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind & differ2_sk b sk sk' # sosub_find sub2 v = Some sk'}.
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

Lemma sosub_find_none_if_differ2_sosubs {o} :
  forall b (sub1 sub2 : @SOSub o) v,
    differ2_sosubs b sub1 sub2
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

Lemma differ2_subs_combine {o} :
  forall b (ts1 ts2 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> (forall t1 t2,
          LIn (t1,t2) (combine ts1 ts2)
          -> differ2 b t1 t2)
    -> differ2_subs b (combine vs ts1) (combine vs ts2).
Proof.
  induction ts1; destruct ts2; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma differ2_apply_list {o} :
  forall b (ts1 ts2 : list (@NTerm o)) t1 t2,
    differ2 b t1 t2
    -> length ts1 = length ts2
    -> (forall x y, LIn (x,y) (combine ts1 ts2) -> differ2 b x y)
    -> differ2 b (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; destruct ts2; introv d l i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ2_oterm; simpl; auto.
  introv k.
  dorn k;[|dorn k]; cpx; constructor; auto.
Qed.

Lemma differ2_sosub_filter {o} :
  forall b (sub1 sub2 : @SOSub o) vs,
    differ2_sosubs b sub1 sub2
    -> differ2_sosubs b (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ2_sosub_filter : slow.

Lemma differ2_sosub_aux {o} :
  forall b (t : @SOTerm o) sub1 sub2,
    differ2_sosubs b sub1 sub2
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ2 b (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv ds disj1 disj2 disj3 disj4 disj5 disj6 cov1 cov2; allsimpl; auto.

  - Case "sovar".
    allrw @cover_so_vars_sovar; repnd.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ2_sosubs b sub1 sub2) in Heqf1; auto.
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

    + applydup (sosub_find_none_if_differ2_sosubs b sub1 sub2) in Heqf1; auto.
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

Lemma differ2_sosub {o} :
  forall b (t : @SOTerm o) (sub1 sub2 : SOSub),
    differ2_sosubs b sub1 sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ2_alpha b (sosub sub1 t) (sosub sub2 t).
Proof.
  introv d c1 c2.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.

  pose proof (differ2_sosubs_change_bound_vars
                b
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
    - rw <- ev1; eauto 3 with slow.
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

  pose proof (sosub_aux_alpha_congr2
                t1 t0 sub1' sub1'') as aeq1.
  repeat (autodimp aeq1 hyp); eauto 3 with slow.

  { rw disjoint_app_r; dands; eauto 3 with slow. }

  { rw disjoint_app_r; dands; eauto 3 with slow. }

  pose proof (sosub_aux_alpha_congr2
                t2 t0 sub2' sub2'') as aeq2.
  repeat (autodimp aeq2 hyp); eauto 3 with slow.

  { rw disjoint_app_r; dands; eauto 3 with slow. }

  { rw disjoint_app_r; dands; eauto 3 with slow. }

  exists (sosub_aux sub1'' t0) (sosub_aux sub2'' t0); dands;
  try (apply alphaeq_eq; complete auto).

  apply differ2_sosub_aux; auto.

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub1 sub1''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub1); auto. }

  { apply (cover_so_vars_if_alphaeq_sosub t0 sub2 sub2''); auto.
    apply (cover_so_vars_if_so_alphaeq t t0 sub2); auto. }
Qed.

Lemma differ2_mk_instance {o} :
  forall b (t : @SOTerm o) vars bs1 bs2,
    matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered t vars
    -> socovered t vars
    -> differ2_bterms b bs1 bs2
    -> differ2_alpha b (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv m1 m2 sc1 sc2 dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ2_mk_abs_substs o b bs1 bs2 vars) in dbs; auto.

  apply differ2_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Lemma implies_differ2_alpha_force_int {o} :
  forall v b (t1 t2 : @NTerm o),
    differ2_alpha b t1 t2
    -> differ2_alpha b (force_int_bound v b t1 (mk_vbot v)) (force_int t2).
Proof.
  introv d.
  unfold differ2_alpha in d; exrepnd.
  exists (force_int_bound v b u1 (mk_vbot v)) (force_int u2); dands.
  - apply alpha_eq_force_int_bound; allsimpl; tcsp;
    allrw remove_nvars_eq; sp.
  - apply alpha_eq_force_int; auto.
  - apply differ2_force_int; auto.
Qed.

Lemma differ2_alpha_mk_atom_eq {o} :
  forall b (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    differ2_alpha b a1 a2
    -> differ2_alpha b b1 b2
    -> differ2_alpha b c1 c2
    -> differ2_alpha b d1 d2
    -> differ2_alpha b (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv da1 da2 da3 da4.
  allunfold @differ2_alpha; exrepnd.
  exists (mk_atom_eq u6 u4 u0 u1) (mk_atom_eq u7 u5 u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ2_alpha_mk_eapply {o} :
  forall b (a1 a2 b1 b2 : @NTerm o),
    differ2_alpha b a1 a2
    -> differ2_alpha b b1 b2
    -> differ2_alpha b (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ2_alpha; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ2_alpha_mk_exception {o} :
  forall b (a1 a2 b1 b2 : @NTerm o),
    differ2_alpha b a1 a2
    -> differ2_alpha b b1 b2
    -> differ2_alpha b (mk_exception a1 b1) (mk_exception a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ2_alpha; exrepnd.
  exists (mk_exception u0 u1) (mk_exception u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - constructor; simpl; auto.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ2_preserves_isvalue_like {o} :
  forall b (t1 t2 : @NTerm o),
    differ2 b t1 t2
    -> isvalue_like t1
    -> isvalue_like t2.
Proof.
  introv d ivl.
  allunfold @isvalue_like; exrepnd.
  repndors;[left|right].
  - apply iscan_implies in ivl; repndors; exrepnd; subst;
    inversion d; subst; eauto 3 with slow.
  - apply isexc_implies2 in ivl; exrepnd; subst.
    inversion d; subst; eauto 3 with slow.
Qed.

Definition differ2_b_alpha {o} (b : nat) (b1 b2 : @BTerm o) :=
  {u1 : BTerm
   & {u2 : BTerm
      & alpha_eq_bterm b1 u1
      # alpha_eq_bterm b2 u2
      # differ2_b b u1 u2}}.

Definition differ2_bs_alpha {o} b (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ2_b_alpha b) bs1 bs2.

Lemma differ2_bterms_nil {o} :
  forall b, @differ2_bterms o b [] [].
Proof.
  unfold differ2_bterms, br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve differ2_bterms_nil : slow.

Lemma differ2_bterms_cons_if {o} :
  forall b (b1 b2 : @BTerm o) bs1 bs2,
    differ2_b b b1 b2
    -> differ2_bterms b bs1 bs2
    -> differ2_bterms b (b1 :: bs1) (b2 :: bs2).
Proof.
  introv d1 d2; apply differ2_bterms_cons; sp.
Qed.
Hint Resolve differ2_bterms_cons_if : slow.

Lemma implies_differ2_alpha_oterm {o} :
  forall b op (bs1 bs2 : list (@BTerm o)),
    differ2_bs_alpha b bs1 bs2
    -> differ2_alpha b (oterm op bs1) (oterm op bs2).
Proof.
  introv diff.
  unfold differ2_bs_alpha, br_bterms, br_list in diff; repnd.

  assert {bs1' : list BTerm
          & {bs2' : list BTerm
          & alpha_eq_bterms bs1 bs1'
          # alpha_eq_bterms bs2 bs2'
          # differ2_bterms b bs1' bs2'}} as hbs.
  { revert dependent bs2.
    induction bs1; introv len imp; destruct bs2; allsimpl; cpx; GC.
    - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)); dands; eauto 3 with slow.
    - pose proof (imp a b0) as h; autodimp h hyp.
      pose proof (IHbs1 bs2) as k; repeat (autodimp k hyp).
      exrepnd.
      unfold differ2_b_alpha in h; exrepnd.
      exists (u1 :: bs1') (u2 :: bs2'); dands; eauto 3 with slow. }

  exrepnd.
  applydup @alpha_eq_bterms_implies_same_length in hbs0.
  applydup @alpha_eq_bterms_implies_same_length in hbs2.
  exists (oterm op bs1') (oterm op bs2'); dands; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs0; auto.

  - apply alpha_eq_oterm_combine; dands; tcsp.
    introv i; apply hbs2; auto.

  - constructor; try omega.
    introv i; apply hbs1; auto.
Qed.

Lemma differ2_alpha_pushdown_fresh_isvalue_like {o} :
  forall b v (t1 t2 : @NTerm o),
    isvalue_like t1
    -> differ2 b t1 t2
    -> differ2_alpha b (pushdown_fresh v t1) (pushdown_fresh v t2).
Proof.
  introv ivl d.
  destruct t1 as [v1|f1|op1 bs1].
  - inversion d; allsimpl; subst; allsimpl; eauto 3 with slow.
  - inversion d; subst; clear d; allsimpl; eauto 3 with slow.
  - inversion d as [? ? d1 d2|?|?|? ? ? len imp d1]; subst; allsimpl; fold_terms; clear d.
    + unfold isvalue_like in ivl; repndors; inversion ivl.
    + apply implies_differ2_alpha_oterm.
      unfold differ2_bs_alpha, br_bterms, br_list.
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

Lemma differ2_preserves_isnoncan_like {o} :
  forall (b : nat) (t1 t2 : @NTerm o),
    differ2 b t1 t2
    -> isnoncan_like t1
    -> isnoncan_like t2.
Proof.
  introv d isn.
  allunfold @isnoncan_like; exrepnd.
  repndors;[left|right].
  - apply isnoncan_implies in isn; exrepnd; subst.
    inversion d; subst; eauto with slow.
    unfold force_int, mk_add; eauto with slow.
  - apply isabs_implies in isn; exrepnd; subst.
    inversion d; subst; eauto with slow.
Qed.

Lemma alphaeq_preserves_hasvalue_like {o} :
  forall lib (t1 t2 : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> hasvalue_like lib t1
    -> hasvalue_like lib t2.
Proof.
  introv wf aeq hv.
  allunfold @hasvalue_like; exrepnd.
  eapply reduces_to_alpha in hv1;[|auto|exact aeq]; exrepnd.
  exists t2'; dands; auto.
  apply alpha_eq_preserves_isvalue_like in hv2; auto.
Qed.

Lemma hasvalue_like_ren_utokens {o} :
  forall lib (t : @NTerm o) ren,
    nt_wf t
    -> no_repeats (range_utok_ren ren)
    -> disjoint (range_utok_ren ren) (diff (get_patom_deq o) (dom_utok_ren ren) (get_utokens t))
    -> hasvalue_like lib t
    -> hasvalue_like lib (ren_utokens ren t).
Proof.
  introv wf norep disj hvl.
  allunfold @hasvalue_like; exrepnd.
  apply (reduces_to_ren_utokens _ _ _ ren) in hvl1; auto.
  exists (ren_utokens ren v); dands; eauto with slow.
Qed.

Lemma differ2_alpha_l {o} :
  forall b (t1 t2 t3 : @NTerm o),
    alpha_eq t1 t2
    -> differ2_alpha b t2 t3
    -> differ2_alpha b t1 t3.
Proof.
  introv aeq d.
  allunfold @differ2_alpha; exrepnd.
  exists u1 u2; dands; eauto with slow.
Qed.

Lemma differ2_alpha_r {o} :
  forall b (t1 t2 t3 : @NTerm o),
    differ2_alpha b t1 t2
    -> alpha_eq t2 t3
    -> differ2_alpha b t1 t3.
Proof.
  introv aeq d.
  allunfold @differ2_alpha; exrepnd.
  exists u1 u2; dands; eauto with slow.
Qed.

Lemma differ2_alpha_mk_fresh {o} :
  forall b v (t1 t2 : @NTerm o),
    differ2_alpha b t1 t2
    -> differ2_alpha b (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv d.
  allunfold @differ2_alpha; exrepnd.
  exists (mk_fresh v u1) (mk_fresh v u2); dands;
  try (apply implies_alpha_eq_mk_fresh; eauto with slow).
  constructor; simpl; auto; introv i; repndors; cpx.
Qed.

Lemma differ2_alpha_mk_lam {o} :
  forall b v (t1 t2 : @NTerm o),
    differ2_alpha b t1 t2
    -> differ2_alpha b (mk_lam v t1) (mk_lam v t2).
Proof.
  introv d.
  allunfold @differ2_alpha; exrepnd.
  exists (mk_lam v u1) (mk_lam v u2); dands;
  try (apply implies_alpha_eq_mk_lam; eauto with slow).
  constructor; simpl; auto; introv i; repndors; cpx.
Qed.

Lemma differ2_subst_utokens_aux {o} :
  forall b (t1 t2 : @NTerm o) sub,
    disjoint (bound_vars t1) (free_vars_utok_sub sub)
    -> disjoint (bound_vars t2) (free_vars_utok_sub sub)
    -> differ2 b t1 t2
    -> differ2 b (subst_utokens_aux t1 sub) (subst_utokens_aux t2 sub).
Proof.
  nterm_ind t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv disj1 disj2 d; auto.

  - Case "vterm".
    inversion d; subst; allsimpl; eauto with slow.

  - Case "sterm".
    inversion d; subst; clear d; allsimpl; auto.

  - Case "oterm".
    inversion d as [? ? ? d1|?|?|? ? ? len1 imp1]; subst; clear d.

    + allsimpl; allrw app_nil_r; fold_terms.
      allrw disjoint_app_l; allrw disjoint_cons_l; repnd.
      constructor.

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

Lemma differ2_alpha_subst_utokens {o} :
  forall b (t1 t2 : @NTerm o) sub,
    differ2_alpha b t1 t2
    -> differ2_alpha b (subst_utokens t1 sub) (subst_utokens t2 sub).
Proof.
  introv d.
  unfold differ2_alpha in d; exrepnd.

  eapply differ2_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d0|].
  eapply differ2_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d2].
  clear dependent t1.
  clear dependent t2.

  pose proof (differ2_change_bound_vars
                b (free_vars_utok_sub sub)
                u1 u2 d1) as d; exrepnd.
  rename u0 into t1.
  rename u3 into t2.

  eapply differ2_alpha_l;[eapply alpha_eq_subst_utokens_same;exact d3|].
  eapply differ2_alpha_r;[|apply alpha_eq_sym;eapply alpha_eq_subst_utokens_same;exact d4].
  clear dependent u1.
  clear dependent u2.

  pose proof (unfold_subst_utokens sub t1) as h; exrepnd.
  pose proof (unfold_subst_utokens sub t2) as k; exrepnd.
  rename t' into u1.
  rename t'0 into u2.
  rw h0; rw k0.

  eapply differ2_alpha_l;[apply (alpha_eq_subst_utokens_aux u1 t1 sub sub); eauto 3 with slow|].
  eapply differ2_alpha_r;[|apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u2 t2 sub sub); eauto with slow].

  apply differ2_implies_differ2_alpha.
  apply differ2_subst_utokens_aux; auto.
Qed.

Lemma differ2_preserves_iscan {o} :
  forall b (t1 t2 : @NTerm o),
    differ2 b t1 t2
    -> iscan t1
    -> iscan t2.
Proof.
  introv diff isc.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  inversion diff; subst; simpl; auto.
Qed.

Lemma differ2_exception_implies {o} :
  forall b (a e t : @NTerm o),
    differ2 b (mk_exception a e) t
    -> {a' : NTerm
        & {e' : NTerm
        & t = mk_exception a' e'
        # differ2 b a a'
        # differ2 b e e' }}.
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

Lemma differ2_lam_implies {o} :
  forall b v a (t : @NTerm o),
    differ2 b (mk_lam v a) t
    -> {a' : NTerm
        & t = mk_lam v a'
        # differ2 b a a' }.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d; allsimpl.

  pose proof (imp (bterm [v] a) x) as d1; autodimp d1 hyp.
  clear imp.

  inversion d1 as [? ? ? d2]; subst; clear d1.
  fold_terms.

  eexists; eexists; dands; eauto.
Qed.

Lemma comp_force_int_step2 {o} :
  forall lib (t1 t2 : @NTerm o) b u,
    wf_term t1
    -> wf_term t2
    -> differ2 b t1 t2
    -> compute_step lib t1 = csuccess u
    -> hasvalue_like lib u
    -> {t : NTerm
        & {u' : NTerm
           & reduces_to lib t2 t
           # reduces_to lib u u'
           # differ2_alpha b u' t}}.
Proof.
  nterm_ind1s t1 as [v|f ind|op bs ind] Case; introv wt1 wt2 d comp hv; auto.

  - Case "vterm".
     simpl.
     inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    inversion d; subst; clear d; allsimpl.
    exists (sterm f) (sterm f); dands; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|mrk|abs] SCase; ginv.

    + SCase "Can".
      csunf comp; inversion d; subst.
      allsimpl; ginv.
      exists (oterm (Can can) bs2) (oterm (Can can) bs); dands; eauto 3 with slow.

    + SCase "NCan".
      destruct bs as [|b1 bs];
        try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (simpl in comp; ginv)).

      {
      destruct t1 as [v1|f1|op1 bs1].

      * destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d));[].

        inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv.

      * destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d));[].
        csunf comp; allsimpl.
        dopid_noncan ncan SSCase; allsimpl; ginv.

        { SSCase "NApply".
          apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          allsimpl.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd arg) y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.

          exists (mk_eapply (sterm f1) t0) (mk_eapply (sterm f1) arg); dands; eauto 3 with slow.
          apply differ2_implies_differ2_alpha.
          apply differ2_oterm; simpl; auto.
          introv j; repndors; cpx; constructor; auto.
        }

        { SSCase "NEApply".
          apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; ginv.
          simpl in len; cpx.
          simpl in imp.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? d3]; subst; clear d1.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.

          repndors; exrepnd; subst.

          - apply compute_step_eapply2_success in comp1; repnd; GC.
            repndors; exrepnd; subst; ginv; allsimpl; GC.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl;
            clear d4; cpx; clear imp1; fold_terms.

            exists (f n) (f n); dands; eauto 3 with slow.
            apply reduces_to_if_step.
            csunf; simpl.
            dcwf h; simpl; boolvar; try omega.
            rw @Znat.Nat2Z.id; auto.

          - apply isexc_implies2 in comp0; exrepnd; subst.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.
            exists (oterm Exc bs2) (oterm Exc l); dands; eauto 3 with slow.

          - pose proof (ind b0 b0 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            allrw <- @wf_eapply_iff; repnd.
            pose proof (h t0 b x) as ih; clear h.
            applydup @preserve_nt_wf_compute_step in comp1; auto.
            repeat (autodimp ih hyp); eauto 3 with slow.
            { apply hasvalue_like_eapply_sterm_implies in hv; auto. }
            exrepnd.

            exists (mk_eapply (sterm f1) t) (mk_eapply (sterm f1) u'); dands; eauto 3 with slow.
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply differ2_alpha_mk_eapply; eauto 3 with slow. }
        }

        { SSCase "NFix".
          apply compute_step_fix_success in comp; repnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          clear imp.

          inversion d1 as [? ? ? d2]; subst; clear d1.
          inversion d2; subst; clear d2.
          fold_terms.

          exists (mk_apply (sterm f1) (mk_fix (sterm f1)))
                 (mk_apply (sterm f1) (mk_fix (sterm f1))).
          dands; eauto 3 with slow.
        }

        { SSCase "NCbv".
          apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          - inversion d1; subst; clear d1.
            apply hasvalue_like_subst_less_bound_seq in hv; sp.

          - pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
            pose proof (imp (bterm [v] x) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d3; subst; clear d3.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            fold_terms.

            exists (subst t2 v (sterm f1))
                   (subst x v (sterm f1)).
            dands; eauto 3 with slow.
            apply differ2_subst; auto.
        }

        { SSCase "NTryCatch".
          apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a) y) as d2; autodimp d2 hyp.
          pose proof (imp (bterm [v] x) z) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          inversion d2 as [? ? ? d4]; subst; clear d2.
          inversion d3 as [? ? ? d5]; subst; clear d3.
          fold_terms.

          exists (mk_atom_eq t2 t2 (sterm f1) mk_bot)
                 (mk_atom_eq a a (sterm f1) mk_bot).
          dands; eauto 3 with slow.
          apply differ2_alpha_mk_atom_eq; eauto 3 with slow.
        }

        { SSCase "NCanTest".
          apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a) y) as d2; autodimp d2 hyp.
          pose proof (imp (nobnd b0) z) as d3; autodimp d3 hyp.
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
        dopid op1 as [can1|ncan1|exc1|abs1] SSCase; ginv.

        { SSCase "Can".

          (* Because the principal argument is canonical we can destruct ncan *)
          dopid_noncan ncan SSSCase.

          - SSSCase "NApply".
            csunf comp; allsimpl.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; allsimpl.

            { inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; clear d.
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

              inversion d3 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
              destruct bs2; allsimpl; cpx.
              destruct bs2; allsimpl; cpx.
              GC.

              pose proof (imp1 (bterm [v] b0) b1) as d1.
              autodimp d1 hyp.
              clear imp1.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              exists (subst t2 v t0) (subst b0 v arg); dands; eauto 3 with slow.

              apply differ2_subst; auto.
            }

            { inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx.
              allsimpl; fold_terms.

              pose proof (imp (nobnd (mk_nseq f)) x) as d1; autodimp d1 hyp.
              pose proof (imp (nobnd arg) y) as d2; autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
              cpx.
              clear imp1.
              fold_terms.

              exists (mk_eapply (mk_nseq f) t0) (mk_eapply (mk_nseq f) arg); dands; eauto 3 with slow.
              apply differ2_implies_differ2_alpha.
              apply differ2_oterm; simpl; auto.
              introv j; repndors; cpx; repeat (constructor; auto).
              simpl; tcsp.
            }

          - SSSCase "NEApply".
            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst.
            rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; ginv.

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            simpl in len; cpx; simpl in imp.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            fold_terms.
            allrw <- @wf_eapply_iff; repnd.
            apply eapply_wf_def_oterm_implies in comp2; exrepnd; ginv; fold_terms.
            destruct comp2 as [comp2|comp2]; exrepnd; ginv; fold_terms.

            { apply differ2_lam_implies in d3; exrepnd; subst; fold_terms.

              repndors; exrepnd; subst.

              + apply compute_step_eapply2_success in comp1; repnd; GC.
                repndors; exrepnd; subst; ginv; allsimpl; GC.
                allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                exists (subst a' v0 t0) (subst b1 v0 b0); dands; eauto 3 with slow.
                { apply eapply_lam_can_implies.
                  apply differ2_preserves_iscan in d4; auto.
                  unfold computes_to_can; dands; eauto 3 with slow. }
                { apply differ2_subst; auto. }

              + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ2_exception_implies in d4; exrepnd; subst.
                exists (mk_exception a'0 e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ2_alpha_mk_exception; eauto 3 with slow.

              + pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 b x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                repeat (autodimp ih hyp); eauto 3 with slow.
                { apply hasvalue_like_eapply_lam_implies in hv; auto. }
                exrepnd.

                exists (mk_eapply (mk_lam v a') t1) (mk_eapply (mk_lam v t) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ2_alpha_mk_eapply; eauto 3 with slow.
                  apply differ2_alpha_mk_lam; eauto 3 with slow. }
            }

            { inversion d3 as [|?|?|? ? ? len imp]; subst; simphyps; clear d3.
              clear imp.
              allsimpl; cpx; allsimpl; fold_terms.
              repndors; exrepnd; subst; allsimpl.

              - destruct b0 as [v|f|op bs]; ginv;[].
                dopid op as [can|ncan|exc|abs] SSSSCase; ginv;[].
                destruct can; ginv;[].
                destruct bs; allsimpl; ginv; GC.
                boolvar; ginv; try omega; fold_terms.
                inversion d4 as [|?|?|? ? ? len imp]; subst; simphyps; clear d4.
                allsimpl; cpx; fold_terms; allsimpl.
                clear imp.

                exists (@mk_nat o (s (Z.to_nat z))) (@mk_nat o (s (Z.to_nat z))); dands; eauto 3 with slow.
                apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
                boolvar; try omega; auto.

              - apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ2_exception_implies in d4; exrepnd; subst.
                exists (mk_exception a' e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ2_alpha_mk_exception; eauto 3 with slow.

              - pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 b x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                allsimpl; autorewrite with slow in *.
                repeat (autodimp ih hyp); eauto 3 with slow.
                { apply hasvalue_like_eapply_nseq_implies in hv; auto. }
                exrepnd.

                exists (mk_eapply (mk_nseq s) t) (mk_eapply (mk_nseq s) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ2_alpha_mk_eapply; eauto 3 with slow. }
            }

(*          - SSSCase "NApseq".
            csunf comp; allsimpl.
            apply compute_step_apseq_success in comp; exrepnd; subst.
            fold_terms.

            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx.
            allsimpl.
            pose proof (imp (nobnd (mk_nat n0)) x) as d1; autodimp d1 hyp; clear imp.
            inversion d1 as [? ? ? d2]; subst; clear d1.
            inversion d2 as [|?|?|? ? ? len1 imp1]; allsimpl; cpx; clear d2.
            clear imp1; fold_terms.

            exists (@mk_nat o (n n0)) (@mk_nat o (n n0)); dands; eauto 3 with slow.
            apply reduces_to_if_step; csunf; simpl.
            rw @Znat.Nat2Z.id.
            boolvar; try omega; auto. *)

          - SSSCase "NFix".
            csunf comp; allsimpl.
            apply compute_step_fix_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2.

            exists (mk_apply
                      (oterm (Can can1) bs2)
                      (oterm (NCan NFix) [bterm [] (oterm (Can can1) bs2)]))
                   (mk_apply (oterm (Can can1) bs1)
                             (oterm (NCan NFix) [bterm [] (oterm (Can can1) bs1)])).
            dands; eauto 3 with slow.

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
            csunf comp; allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can NPair) [nobnd a, nobnd b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) b2) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (nobnd a) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b0) b2) as d2.
            autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? d5]; subst; clear d1.
            inversion d2 as [? ? ? d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)])
                   (lsubst arg [(va,a),(vb,b0)]); dands; eauto 4 with slow.

          - SSSCase "NDsup".
            csunf comp; allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp (bterm [] (oterm (Can NSup) [nobnd a, nobnd b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) b2) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            GC.

            pose proof (imp1 (nobnd a) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (nobnd b0) b2) as d2.
            autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? d5]; subst; clear d1.
            inversion d2 as [? ? ? d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)])
                   (lsubst arg [(va,a),(vb,b0)]); dands; eauto 4 with slow.

          - SSSCase "NDecide".
            csunf comp; allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
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

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.
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
                dands; eauto 3 with slow.

              apply differ2_subst; auto.

            + exists (subst t5 v2 t3)
                     (subst t0 v2 d0);
                dands; eauto 3 with slow.

              apply differ2_subst; auto.

          - SSSCase "NCbv".
            csunf comp; allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
            inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; allsimpl; clear d.

            + inversion d1 as [|?|?|? ? ? len imp]; subst; allsimpl; clear d1.

              apply hasvalue_like_subst_less_bound in hv; exrepnd; subst.

              allsimpl; cpx; GC.
              exists (@mk_integer o z) (@mk_integer o z); dands; eauto 3 with slow.

              * apply reduces_to_if_step; simpl.
                csunf; simpl.
                dcwf h; allsimpl.
                unfold compute_step_arith; simpl.
                allrw <- Zplus_0_r_reverse; auto.

              * unfold subst, lsubst; simpl; boolvar; GC; allrw not_over_or; repndors; repnd; tcsp; GC.
                simpl; fold_terms.
                destruct (Z_lt_le_dec z 0) as [h|h].

                { apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_minus (mk_integer z)) (mk_nat b) (mk_integer z) (mk_vbot v)));
                  [ csunf; simpl; boolvar; tcsp; omega|].

                  apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_integer (- z)) (mk_nat b) (mk_integer z) (mk_vbot v)));
                    auto.
                  apply reduces_to_if_step; simpl.
                  csunf; simpl.
                  dcwf q; allsimpl.
                  unfold compute_step_comp; simpl; boolvar; tcsp; try omega.
                  provefalse.
                  pose proof (abs_of_neg2 z b); sp; try omega.
                }

                { apply (reduces_to_if_split2
                           _ _
                           (mk_less (mk_integer z) (mk_nat b) (mk_integer z) (mk_vbot v)));
                  [ csunf; simpl; boolvar; tcsp; omega|].

                  apply reduces_to_if_step; simpl.
                  csunf; simpl.
                  dcwf q; allsimpl.
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

              inversion d3 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d3.

              exists (subst t0 v (oterm (Can can1) bs2))
                     (subst x v (oterm (Can can1) bs1));
                dands; eauto 3 with slow.

              apply differ2_subst; auto.

          - SSSCase "NSleep".
            csunf comp; allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.

          - SSSCase "NTUni".
            csunf comp; allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint (Z.of_nat n))) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_uni o n) (@mk_uni o n); dands; eauto 3 with slow.

            apply reduces_to_if_step; simpl.
            csunf; simpl; unfold compute_step_tuni; simpl; boolvar; tcsp; try omega.
            rw Znat.Nat2Z.id; auto.

          - SSSCase "NMinus".
            csunf comp; allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl; GC.

            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d2; cpx.
            clear imp1.

            exists (@mk_integer o (- z)) (@mk_integer o (- z)); dands; eauto 3 with slow.

          - SSSCase "NFresh".
            csunf comp; ginv.

          - SSSCase "NTryCatch".
            csunf comp; allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl; GC.

            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d; cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) x0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] a) y) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v] x) z) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4; cpx.

            exists (mk_atom_eq t0 t0 (oterm (Can can1) bs2) mk_bot)
                   (mk_atom_eq a a (oterm (Can can1) bs1) mk_bot);
              dands; eauto 3 with slow.

            apply differ2_implies_differ2_alpha.
            constructor; simpl; auto.
            introv i; repndors; ginv; tcsp; constructor; eauto 3 with slow.

          - SSSCase "NParallel".
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; allsimpl; subst; clear d.
            destruct bs2; allsimpl; cpx.
            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d.
            autodimp d hyp.
            inversion d as [? ? ? d1]; subst; clear d.
            inversion d1 as [|?|?|? ? ? len' imp']; subst; clear d1.
            exists (@mk_axiom o) (@mk_axiom o); dands; eauto with slow.

          - SSSCase "NCompOp".
            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
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

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; simpl in comp.
              dcwf h.

              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.

              apply compute_step_compop_success_can_can in comp.
              exrepnd; subst.

              allsimpl; cpx; allsimpl; GC.
              clear imp1.

              pose proof (imp (nobnd t1) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd t2) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              repndors; exrepnd; subst.

              * allapply @get_param_from_cop_pki; subst; allsimpl.
                exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                       (if Z_lt_le_dec n1 n2 then t1 else t2);
                  dands; eauto 3 with slow.
                boolvar; eauto 3 with slow.

              * allrw @get_param_from_cop_some; subst; allsimpl.
                exists (if param_kind_deq pk1 pk2 then t3 else t4)
                       (if param_kind_deq pk1 pk2 then t1 else t2);
                  dands; eauto 3 with slow.
                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h; allsimpl.
                  unfold compute_step_comp; simpl; allrw @get_param_from_cop_pk2can; auto. }
                boolvar; eauto 3 with slow.

            + SSSSCase "NCan".
              rw @compute_step_ncompop_ncan2 in comp.
              dcwf h.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp; tcsp); eauto 3 with slow.

              pose proof (h t0 b n) as k; clear h.
              repeat (autodimp k hyp).

              { apply wf_oterm_iff in wt1; allsimpl; repnd.
                pose proof (wt1 (bterm [] (oterm (NCan ncan3) bs2))) as h; autodimp h hyp. }

              { apply wf_oterm_iff in wt2; allsimpl; repnd.
                pose proof (wt2 (bterm [] t0)) as h; autodimp h hyp. }

              { apply if_hasvalue_like_ncompop_can1 in hv; auto. }

              exrepnd.

              exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] t
                                   :: bs3))
                     (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: bterm [] u'
                                   :: bs)).
              dands; eauto 3 with slow.

              * apply reduce_to_prinargs_comp2; eauto 3 with slow; sp.
                apply co_wf_def_implies_iswfpk.
                eapply co_wf_def_len_implies;[|eauto]; auto.

              * apply reduce_to_prinargs_comp2; eauto 3 with slow; sp.

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
              csunf comp; allsimpl; ginv.
              dcwf h; allsimpl; ginv.
              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm Exc bs5) (oterm Exc bs2); dands; eauto 3 with slow.
              eapply reduces_to_if_step; csunf; simpl; dcwf h.

            + SSSSCase "Abs".
              csunf comp; allsimpl.
              dcwf h; allsimpl.
              unfold on_success in comp; csunf comp; allsimpl.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

              assert (differ2_bterms b bs2 bs5) as dbs.
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

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl.
               dcwf h.
               unfold on_success; csunf; simpl.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ2_mk_instance b rhs vars bs2 bs5) as h.
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
            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
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

            inversion d3 as [|?|?|? ? ? len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; simpl in comp.
              dcwf h; allsimpl.

              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.

              apply compute_step_arithop_success_can_can in comp.
              exrepnd; subst.
              allsimpl; cpx.
              clear imp1 imp2 imp.

              allapply @get_param_from_cop_pki; subst; allsimpl; GC.

              exists (@oterm o (Can (Nint (get_arith_op a n1 n2))) [])
                     (@oterm o (Can (Nint (get_arith_op a n1 n2))) []);
                dands; eauto 3 with slow.

            + SSSSCase "NCan".
              rw @compute_step_narithop_ncan2 in comp.
              dcwf h; allsimpl;[].
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp; tcsp); eauto 3 with slow.

              pose proof (h t0 b n) as k; clear h.
              repeat (autodimp k hyp).

              { apply wf_oterm_iff in wt1; allsimpl; repnd.
                pose proof (wt1 (bterm [] (oterm (NCan ncan3) bs2))) as h; autodimp h hyp. }

              { apply wf_oterm_iff in wt2; allsimpl; repnd.
                pose proof (wt2 (bterm [] t0)) as h; autodimp h hyp. }

              { apply if_hasvalue_like_arithop_can1 in hv; auto. }

              exrepnd.

              exists (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] t
                                   :: bs3))
                     (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: bterm [] u'
                                   :: bs)).
              dands; eauto 3 with slow.

              * apply reduce_to_prinargs_arith2; eauto 3 with slow; sp.
                allunfold @ca_wf_def; exrepnd; subst; allsimpl; cpx.
                fold_terms; eauto 3 with slow.

              * apply reduce_to_prinargs_arith2; eauto 3 with slow; sp.

              * unfold differ2_alpha in k1; exrepnd.
                exists (oterm (NCan (NArithOp a))
                              (bterm [] (oterm (Can can1) bs1)
                                     :: bterm [] u1
                                     :: bs))
                       (oterm (NCan (NArithOp a))
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
              csunf comp; allsimpl; ginv.
              dcwf h; allsimpl; ginv.
              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm Exc bs5) (oterm Exc bs2); dands; eauto 3 with slow;[].
              apply reduces_to_if_step; csunf; simpl; dcwf h.

            + SSSSCase "Abs".
              csunf comp; allsimpl.
              dcwf h; allsimpl.
              unfold on_success in comp; csunf comp; allsimpl.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; simphyps; clear d4.

              assert (differ2_bterms b bs2 bs5) as dbs.
              { unfold differ2_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ2_bterms_implies_eq_map_num_bvars in dbs; auto. }

              exists (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] (mk_instance vars bs5 rhs)
                                   :: bs3))
              (oterm (NCan (NArithOp a))
                     (bterm [] (oterm (Can can1) bs1)
                            :: bterm [] (mk_instance vars bs2 rhs)
                            :: bs)).

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl; unfold on_success; csunf; simpl.
               dcwf h; allsimpl.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ2_mk_instance b rhs vars bs2 bs5) as h.
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
                 (oterm (NCan (NArithOp a))
                        (bterm [] (oterm (Can can1) bs1)
                               :: bterm [] u1
                               :: bs))
                 (oterm (NCan (NArithOp a))
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
            csunf comp; allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
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

            inversion d4 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.

            exists (if canonical_form_test_for c can1 then t0 else t3)
                   (if canonical_form_test_for c can1 then arg2nt else arg3nt).
            dands; eauto 3 with slow.
            destruct (canonical_form_test_for c can1); eauto 3 with slow.
        }

        { SSCase "NCan".
          rw @compute_step_ncan_ncan in comp.
          remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.

          - pose proof (ind (oterm (NCan ncan1) bs1) (oterm (NCan ncan1) bs1) []) as h.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.

            allrw <- @wf_cbv_iff; repnd.
            allrw @wf_term_force_int.

            pose proof (h t0 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_hasvalue_like_force_int_bound in hv; exrepnd; eauto 3 with slow.
              unfold hasvalue_like.
              exists u; dands; eauto 3 with slow. }

            exrepnd.

            exists (force_int t) (force_int_bound v b u' (mk_vbot v)); dands; eauto 3 with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { apply implies_differ2_alpha_force_int; auto. }

          - simpl in len.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (NCan ncan1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind (oterm (NCan ncan1) bs1) (oterm (NCan ncan1) bs1) []) as h.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.
            pose proof (h t2 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply wf_oterm_iff in wt1; allsimpl; repnd.
              pose proof (wt1 (bterm [] (oterm (NCan ncan1) bs1))) as h; autodimp h hyp. }

            { apply wf_oterm_iff in wt2; allsimpl; repnd.
              pose proof (wt2 (bterm [] t2)) as h; autodimp h hyp. }

            { apply if_hasvalue_like_ncan_primarg in hv; auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto 3 with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { unfold differ2_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto 3 with slow.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto 3 with slow.

              - apply differ2_oterm; simpl; auto.
                introv j; dorn j; cpx.
            }
        }

        { SSCase "Exc".
          csunf comp; simpl in comp.
          apply compute_step_catch_success in comp.
          dorn comp; exrepnd; subst.

          - inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            allsimpl.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.
            allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

            pose proof (imp (bterm [] (oterm Exc [bterm [] a', bterm [] e])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] a) x) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v] b0) y) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d2 as [? ? ? d5]; subst; clear d2.
            inversion d3 as [? ? ? d6]; subst; clear d3.

            inversion d4 as [? ? ? d1|?|?|? ? ? len1 imp1]; subst; clear d4.
            allsimpl; cpx.
            allsimpl.
            pose proof (imp1 (bterm [] a') x) as d1; autodimp d1 hyp.
            pose proof (imp1 (bterm [] e) y) as d2; autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            allsimpl.

            exists (mk_atom_eq t0 t2 (subst t3 v t4) (mk_exception t2 t4))
                   (mk_atom_eq a a' (subst b0 v e) (mk_exception a' e));
              dands; eauto 3 with slow.

            apply differ2_alpha_mk_atom_eq; eauto 3 with slow.

            { apply differ2_subst; auto. }

            { apply differ2_alpha_mk_exception; eauto 3 with slow. }

          - inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            allsimpl.

            + inversion d1 as [|?|?|? ? ? len imp]; subst; clear d1.
              exists (oterm Exc bs2) (oterm Exc bs1).
              dands; eauto 3 with slow.

            + allsimpl.
              destruct bs2; allsimpl; cpx.

              pose proof (imp (bterm [] (oterm Exc bs1)) b0) as d1.
              autodimp d1 hyp.
              inversion d1 as [? ? ? d2]; subst; clear d1.
              inversion d2 as [|?|?|? ? ? len1 imp1]; subst; clear d2.

              allsimpl.
              allrw in_app_iff; allrw not_over_or; repnd.
              exists (oterm Exc bs3) (oterm Exc bs1).
              dands; eauto 3 with slow.

              apply reduces_to_if_step; simpl.
              csunf; simpl; unfold compute_step_catch; destruct ncan; tcsp.
        }

        { SSCase "Abs".
          csunf comp; allsimpl.
          unfold on_success in comp; csunf comp; allsimpl.
          remember (compute_step_lib lib abs1 bs1) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.

          - pose proof (ind (oterm (Abs abs1) bs1) (oterm (Abs abs1) bs1) []) as h.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.

            allrw <- @wf_cbv_iff; repnd.
            allrw @wf_term_force_int.
            applydup @wf_compute_step_lib in Heqcomp1; eauto 3 with slow.

            pose proof (h t0 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply if_hasvalue_like_force_int_bound in hv; exrepnd; eauto 3 with slow.
              unfold hasvalue_like.
              exists u; dands; eauto 3 with slow. }

            exrepnd.

            exists (force_int t) (force_int_bound v b u' (mk_vbot v)); dands; eauto 3 with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { apply implies_differ2_alpha_force_int; auto. }

          - simpl in len.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (Abs abs1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind (oterm (Abs abs1) bs1) (oterm (Abs abs1) bs1) []) as h.
            repeat (autodimp h hyp; tcsp); eauto 3 with slow.
            pose proof (h t2 b n) as k; clear h.
            repeat (autodimp k hyp).

            { apply wf_oterm_iff in wt1; allsimpl; repnd.
              pose proof (wt1 (bterm [] (oterm (Abs abs1) bs1))) as h; autodimp h hyp. }

            { apply wf_oterm_iff in wt2; allsimpl; repnd.
              pose proof (wt2 (bterm [] t2)) as h; autodimp h hyp. }

            { apply if_hasvalue_like_ncan_primarg in hv; auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto 3 with slow.

            { apply reduces_to_prinarg; auto. }

            { apply reduces_to_prinarg; auto. }

            { unfold differ2_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto 3 with slow.

              - prove_alpha_eq4.
                introv j; destruct n0; eauto 3 with slow.

              - apply differ2_oterm; simpl; auto.
                introv j; dorn j; cpx.
            }
        }
      }

      { (* fresh case *)
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; repnd; subst; allsimpl.

        inversion d as [|?|?|? ? ? len1 imp1]; subst; clear d.
        allsimpl; cpx; allsimpl.
        pose proof (imp1 (bterm [n] t1) x) as d1; autodimp d1 hyp.
        clear imp1.
        inversion d1 as [? ? ? d2]; subst; clear d1.

        repndors; exrepnd; subst; fold_terms.

        - inversion d2; subst.
          exists (@mk_fresh o n (mk_var n)) (@mk_fresh o n (mk_var n)).
          dands; eauto 3 with slow.

        - applydup @differ2_preserves_isvalue_like in d2; auto.
          exists (pushdown_fresh n t2) (pushdown_fresh n t1); dands; eauto 3 with slow.
          { apply reduces_to_if_step.
            apply compute_step_fresh_if_isvalue_like; auto. }
          { apply differ2_alpha_pushdown_fresh_isvalue_like; auto. }

        - applydup @differ2_preserves_isnoncan_like in d2; auto;[].
          allrw app_nil_r.

          pose proof (fresh_atom o (get_utokens t1 ++ get_utokens t2)) as fa; exrepnd.
          allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a.

          pose proof (compute_step_subst_utoken lib t1 x [(n,mk_utoken (get_fresh_atom t1))]) as comp'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          allrw @wf_fresh_iff.
          repeat (autodimp comp' hyp); try (apply get_fresh_atom_prop); eauto 3 with slow.
          { apply nr_ut_sub_cons; eauto with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          pose proof (comp'0 [(n,mk_utoken a)]) as comp''; clear comp'0.
          allsimpl.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp comp'' hyp); exrepnd.

          pose proof (differ2_subst b t1 t2 [(n, mk_utoken a)] [(n, mk_utoken a)]) as daeq.
          repeat (autodimp daeq hyp); eauto with slow.
          unfold differ2_alpha in daeq; exrepnd.

          pose proof (compute_step_alpha lib (lsubst t1 [(n, mk_utoken a)]) u1 s) as comp'''.
          repeat (autodimp comp''' hyp); exrepnd.
          { apply nt_wf_subst; eauto 3 with slow. }
          rename t2' into s'.

          assert (wf_term x) as wfx.
          { eapply compute_step_preserves_wf;[exact comp2|].
            allrw @wf_fresh_iff.
            apply wf_term_subst; eauto with slow. }

          assert (!LIn n (free_vars x)) as ninx.
          { intro i; apply compute_step_preserves in comp2; repnd;
            try (apply nt_wf_subst; eauto 3 with slow).
            rw subvars_prop in comp0; apply comp0 in i; clear comp0.
            apply eqset_free_vars_disjoint in i; allsimpl.
            allrw in_app_iff; allrw in_remove_nvars; allsimpl; boolvar; allsimpl; tcsp. }

          applydup @alphaeq_preserves_wf_term in daeq0; auto;
          [|apply lsubst_preserves_wf_term; eauto 3 with slow];[].
          applydup @alphaeq_preserves_wf_term in daeq2; auto;
          [|apply lsubst_preserves_wf_term; eauto 3 with slow];[].
          applydup @compute_step_preserves_wf in comp'''1; auto;[].
          applydup @alphaeq_preserves_wf_term_inv in comp'''0; auto;[].

          pose proof (ind t1 u1 [n]) as q; clear ind.
          repeat (autodimp q hyp).
          { apply alpha_eq_preserves_osize in daeq0; rw <- daeq0; allrw @fold_subst.
            rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (q u2 b s') as ih; clear q.
          repeat (autodimp ih hyp); fold_terms.
          { eapply alphaeq_preserves_hasvalue_like;[|exact comp'''0|]; eauto 3 with slow.
            eapply alphaeq_preserves_hasvalue_like;[|apply alpha_eq_sym;exact comp''0|]; eauto 3 with slow.
            pose proof (hasvalue_like_ren_utokens
                          lib
                          (lsubst w [(n, mk_utoken (get_fresh_atom t1))])
                          [(get_fresh_atom t1,a)]) as hvl.
            allsimpl.
            allrw disjoint_singleton_l; allrw in_remove.
            repeat (autodimp hvl hyp); eauto 3 with slow.
            { intro k; repnd.
              apply get_utokens_lsubst_subset in k; unfold get_utokens_sub in k; allsimpl.
              allrw in_app_iff; allsimpl; repndors; tcsp. }
            { eapply alphaeq_preserves_hasvalue_like;[|exact comp'1|]; eauto 3 with slow.
              apply (hasvalue_like_fresh_implies lib (get_fresh_atom t1)) in hv; auto;
              [|apply wf_subst_utokens; eauto 3 with slow
               |intro i; apply get_utokens_subst_utokens_subset in i; allsimpl;
                unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r;
                rw in_remove in i; repnd;
                apply compute_step_preserves_utokens in comp2; eauto 3 with slow; apply comp2 in i;
                apply get_utokens_subst in i; allsimpl; boolvar; tcsp].
              pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom t1) n) as h.
              repeat (autodimp h hyp).
              eapply alphaeq_preserves_hasvalue_like in h;[exact h| |]; eauto 3 with slow.
              apply nt_wf_subst; eauto 3 with slow.
              apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow.
            }
            rw @lsubst_ren_utokens in hvl; allsimpl; fold_terms.
            unfold ren_atom in hvl; allsimpl; boolvar; tcsp.
            rw @ren_utokens_trivial in hvl; simpl; auto.
            apply disjoint_singleton_l; intro i; apply comp'4 in i; apply get_fresh_atom_prop in i; sp.
          }
          exrepnd.

          pose proof (reduces_to_alpha lib u2 (lsubst t2 [(n, mk_utoken a)]) t) as r1.
          repeat (autodimp r1 hyp); eauto with slow.
          exrepnd.

          pose proof (reduces_to_change_utok_sub
                        lib t2 t2' [(n,mk_utoken a)] [(n,mk_utoken (get_fresh_atom t2))]) as r1'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp r1' hyp); try (apply get_fresh_atom_prop); eauto 3 with slow.
          { apply nr_ut_sub_cons; eauto with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          allrw disjoint_singleton_l.
          fold_terms; allrw @fold_subst.

          pose proof (reduces_to_fresh lib t2 s0 n) as q; simpl in q.
          repeat (autodimp q hyp).
          exrepnd.

          (* 1st exists *)
          exists (mk_fresh n z).

          assert (!LIn a (get_utokens w)) as niaw.
          { intro k; apply comp'4 in k; sp. }

          pose proof (alpha_eq_subst_utokens
                        x (subst w n (mk_utoken (get_fresh_atom t1)))
                        [(get_fresh_atom t1, mk_var n)]
                        [(get_fresh_atom t1, mk_var n)]) as aeqs.
          repeat (autodimp aeqs hyp); eauto 3 with slow.
          pose proof (simple_alphaeq_subst_utokens_subst
                        w n (get_fresh_atom t1)) as aeqs1.
          autodimp aeqs1 hyp.
          eapply alpha_eq_trans in aeqs1;[|exact aeqs]; clear aeqs.

          pose proof (reduces_to_alpha lib s' (subst w n (mk_utoken a)) u') as raeq.
          repeat (autodimp raeq hyp); eauto 3 with slow; exrepnd;[].
          rename t2'0 into u''.

          assert (wf_term w) as wfw.
          { allrw @wf_fresh_iff.
            apply compute_step_preserves_wf in comp2;
              [|apply wf_term_subst;eauto with slow].
            apply alphaeq_preserves_wf_term in comp'1; auto.
            apply lsubst_wf_term in comp'1; auto.
          }

          pose proof (reduces_to_fresh2 lib w u'' n a) as rf.
          repeat (autodimp rf hyp); exrepnd.

          pose proof (reduces_to_alpha
                        lib
                        (mk_fresh n w)
                        (mk_fresh n (subst_utokens x [(get_fresh_atom t1, mk_var n)]))
                        (mk_fresh n z0)) as r'.
          repeat (autodimp r' hyp); eauto 3 with slow.
          { apply nt_wf_fresh; eauto 3 with slow. }
          { apply implies_alpha_eq_mk_fresh; eauto with slow. }
          exrepnd.
          rename t2'0 into f'.

          (* 2nd exists *)
          exists f'; dands; auto.
          eapply differ2_alpha_l;[apply alpha_eq_sym; exact r'0|].
          apply differ2_alpha_mk_fresh.
          eapply differ2_alpha_l;[exact rf0|].
          eapply differ2_alpha_r;[|apply alpha_eq_sym; exact q0].
          eapply differ2_alpha_l;[apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact raeq0|].
          eapply differ2_alpha_r;[|apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact r1'1].

          pose proof (simple_alphaeq_subst_utokens_subst w0 n (get_fresh_atom t2)) as aeqsu.
          autodimp aeqsu hyp.
          { intro j; apply r1'4 in j; apply get_fresh_atom_prop in j; sp. }

          eapply differ2_alpha_r;[|apply alpha_eq_sym;exact aeqsu];clear aeqsu.

          apply (alpha_eq_subst_utokens_same _ _ [(a, mk_var n)]) in r1'0.
          pose proof (simple_alphaeq_subst_utokens_subst w0 n a) as aeqsu.
          autodimp aeqsu hyp.

          eapply differ2_alpha_r;[|exact aeqsu];clear aeqsu.
          eapply differ2_alpha_r;[|exact r1'0].
          eapply differ2_alpha_r;[|apply alpha_eq_subst_utokens_same; exact r0].
          apply differ2_alpha_subst_utokens; auto.
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.
      inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
      exists (oterm Exc bs2) (oterm Exc bs).
      dands; eauto 3 with slow.

    + SCase "Abs".
      inversion d as [? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
      csunf comp; allsimpl.
      apply compute_step_lib_success in comp; exrepnd; subst.

      assert (differ2_bterms b bs bs2) as dbs.
      { unfold differ2_bterms, br_bterms, br_list; auto. }

      pose proof (found_entry_change_bs abs oa2 vars rhs lib bs correct bs2) as fe2.
      repeat (autodimp fe2 hyp).

      { apply differ2_bterms_implies_eq_map_num_bvars in dbs; auto. }

      exists (mk_instance vars bs2 rhs) (mk_instance vars bs rhs).

      dands; eauto 3 with slow.

      * apply reduces_to_if_step.
        csunf; simpl; unfold on_success.
        applydup @compute_step_lib_if_found_entry in fe2.
        rw fe0; auto.

      * pose proof (differ2_mk_instance b rhs vars bs bs2) as h.
        repeat (autodimp h hyp).
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allunfold @correct_abs; sp. }
        { allunfold @correct_abs; sp. }
Qed.

Lemma comp_force_int2 {o} :
  forall lib (t1 t2 : @NTerm o) b z,
    wf_term t1
    -> wf_term t2
    -> differ2 b t1 t2
    -> reduces_to lib t1 (mk_integer z)
    -> reduces_to lib t2 (mk_integer z).
Proof.
  introv w1 w2 d comp.
  unfold reduces_to in comp; exrepnd.
  revert dependent t2.
  revert dependent t1.
  induction k as [n ind] using comp_ind_type; introv w1 r w2 d.
  destruct n as [|k]; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion d as [|?|?|? ? ? len imp]; subst; clear d.
    allsimpl; cpx; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    pose proof (comp_force_int_step2 lib t1 t2 b u) as h.
    repeat (autodimp h hyp).

    { unfold hasvalue_like.
      exists (@mk_integer o z); dands; eauto 3 with slow; tcsp. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to
                  lib k u u' (mk_integer z)) as h'.
    repeat (autodimp h' hyp).
    { left; sp. }
    exrepnd.

    unfold differ2_alpha in h1; exrepnd.

    applydup @preserve_nt_wf_compute_step in r1; eauto 3 with slow.
    applydup @reduces_to_preserves_wf in h2; eauto 3 with slow.
    applydup @reduces_to_preserves_wf in h0; eauto 3 with slow.
    applydup @alphaeq_preserves_wf_term in h4; eauto 3 with slow.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u' u1) as h''.
    repeat (autodimp h'' hyp); eauto 3 with slow.

    pose proof (h'' k' (mk_integer z)) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.
    inversion h'''0 as [|?|? ? ? ? x]; subst; allsimpl; cpx;
    clear x h'''0.
    fold_terms.

    pose proof (ind k') as h.
    autodimp h hyp;[omega|].
    pose proof (h u1) as r; clear h.
    repeat (autodimp r hyp); eauto 3 with slow.

    pose proof (r u2) as h; clear r; repeat (autodimp h hyp); eauto 3 with slow.

    pose proof (reduces_to_steps_alpha lib u2 t (mk_integer z)) as r.
    repeat (autodimp r hyp); eauto 3 with slow.
    exrepnd.
    inversion r3; subst; allsimpl; cpx; fold_terms.
    eapply reduces_to_trans; eauto.
Qed.

Lemma old_differ_app_F2 {o} :
  forall (F g : @NTerm o) v x b,
    differ2
      b
      (mk_apply F (mk_lam x (mk_apply g (force_int_bound v b (mk_var x) (mk_vbot v)))))
      (mk_apply F (mk_lam x (mk_apply g (force_int (mk_var x))))).
Proof.
  introv.
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

Lemma differ_app_F2 {o} :
  forall (F g : @NTerm o) x b,
    differ2
      b
      (force_int_bound_F x b F g (mk_vbot x))
      (force_int_F x F g).
Proof.
  introv.
  constructor; simpl; auto.
  introv i; dorn i;[|dorn i]; cpx.
  - constructor; eauto 3 with slow.
  - constructor; constructor; simpl; auto.
    introv i; dorn i; cpx.
    constructor; constructor; simpl; auto.
    introv i; dorn i;[|dorn i]; cpx; auto.
    + constructor; eauto 3 with slow.
    + constructor; constructor; simpl; auto.
      introv i; dorn i;[|dorn i]; cpx; auto.
      * constructor; eauto 3 with slow.
      * constructor; constructor.
Qed.

(*

  F (\x.let x:=(x+0) in f(x)) -> z
  =>
  exists b.
    F (\x.let x:=(let v:=x in if |v|<b then v else e) in f(x)) -> z

*)
Lemma comp_force_int_app_F2 {o} :
  forall lib (F g : @NTerm o) x z b,
    wf_term F
    -> wf_term g
    -> reduces_to
         lib
         (force_int_bound_F x b F g (mk_vbot x))
         (mk_integer z)
    -> reduces_to
         lib
         (force_int_F x F g)
         (mk_integer z).
Proof.
  introv wF wg r.
  eapply (comp_force_int2 _ _ _ b);[|idtac|idtac|apply r];
  try (apply differ_app_F2); eauto 4 with slow.
Qed.
 