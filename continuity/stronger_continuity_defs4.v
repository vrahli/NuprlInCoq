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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export stronger_continuity_defs4_aux.


(* we're going to assume that e is closed *)
Inductive differ_force {o} (b : nat) (a : get_patom_set o) (f : @NTerm o) : @NTerm o -> @NTerm o -> Type :=
| differ_force_nat :
    forall arg1 arg2 x z f',
      alpha_eq f f'
      -> differ_force b a f arg1 arg2
      -> differ_force b a f (sp_force_nat arg1 x z f') (bound2_cbv arg2 x z b f' a)
| differ_force_var :
    forall v, differ_force b a f (mk_var v) (mk_var v)
| differ_force_sterm :
    forall s, differ_force b a f (sterm s) (sterm s)
| differ_force_oterm :
    forall op bs1 bs2,
      length bs1 = length bs2
      -> !LIn a (get_utokens_o op)
      -> (forall b1 b2, LIn (b1,b2) (combine bs1 bs2) -> differ_force_b b a f b1 b2)
      -> differ_force b a f (oterm op bs1) (oterm op bs2)
with differ_force_b {o} (b : nat) (a : get_patom_set o) (f : @NTerm o) : @BTerm o -> @BTerm o -> Type :=
     | differ_force_bterm :
         forall vs t1 t2,
           differ_force b a f t1 t2
           -> differ_force_b b a f (bterm vs t1) (bterm vs t2).
Hint Constructors differ_force differ_force_b.

Inductive differ_force_subs {o} b a f : @Sub o -> @Sub o -> Type :=
| dfsub_nil : differ_force_subs b a f [] []
| dfsub_cons :
    forall v t1 t2 sub1 sub2,
      differ_force b a f t1 t2
      -> differ_force_subs b a f sub1 sub2
      -> differ_force_subs b a f ((v,t1) :: sub1) ((v,t2) :: sub2).
Hint Constructors differ_force_subs.

Lemma differ_force_subs_sub_find_some {o} :
  forall b a f (sub1 sub2 : @Sub o) v t,
    differ_force_subs b a f sub1 sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u # differ_force b a f t u}.
Proof.
  induction sub1; destruct sub2; introv d sf; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
  eexists; eauto.
Qed.

Lemma differ_force_subs_sub_find_none {o} :
  forall b a f (sub1 sub2 : @Sub o) v,
    differ_force_subs b a f sub1 sub2
    -> sub_find sub1 v = None
    -> sub_find sub2 v = None.
Proof.
  induction sub1; destruct sub2; introv d sf; allsimpl; tcsp;
  inversion d; subst.
  boolvar; cpx.
Qed.

Lemma differ_force_subs_filter {o} :
  forall b a f (sub1 sub2 : @Sub o) l,
    differ_force_subs b a f sub1 sub2
    -> differ_force_subs b a f (sub_filter sub1 l) (sub_filter sub2 l).
Proof.
  induction sub1; destruct sub2; introv d; allsimpl; inversion d; auto.
  boolvar; sp.
Qed.
Hint Resolve differ_force_subs_filter : slow.

Lemma differ_force_lsubst_aux {o} :
  forall b a f (t1 t2 : @NTerm o) sub1 sub2,
    isprog f
    -> differ_force b a f t1 t2
    -> differ_force_subs b a f sub1 sub2
    -> disjoint (bound_vars t1) (sub_free_vars sub1)
    -> disjoint (bound_vars t2) (sub_free_vars sub2)
    -> differ_force b a f (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  nterm_ind1s t1 as [v|s ind|op bs ind] Case;
  introv ispf dt ds disj1 disj2; allsimpl.

  - Case "vterm".
    inversion dt; subst; allsimpl.
    remember (sub_find sub1 v) as f1; symmetry in Heqf1; destruct f1.

    + applydup (differ_force_subs_sub_find_some b a f sub1 sub2) in Heqf1; auto.
      exrepnd; allrw; auto.

    + applydup (differ_force_subs_sub_find_none b a f sub1 sub2) in Heqf1; auto.
      allrw; auto.

  - Case "sterm".
    inversion dt as [? ? ? ? ? aeq dt'|?|?|? ? ? len nia imp]; subst; allsimpl; clear dt; auto.

  - Case "oterm".
    inversion dt as [? ? ? ? ? aeq dt'|?|?|? ? ? len nia imp]; subst; allsimpl; clear dt.

    + allrw @sub_filter_nil_r.
      allrw app_nil_r.
      allrw @sub_find_sub_filter_eq; allrw memvar_singleton.
      allrw <- beq_var_refl; fold_terms.
      allrw disjoint_app_l; allrw disjoint_cons_l; allrw disjoint_app_l; repnd; GC.
      applydup @alpha_eq_preserves_isprog in aeq; auto.
      repeat (rw (lsubst_aux_trivial_cl_term2 f'); eauto 3 with slow).
      try (fold (spexc a)).
      apply differ_force_nat; auto.

      apply (ind arg1 arg1 []); eauto 3 with slow.

    + apply differ_force_oterm; allrw map_length; auto.

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
      apply (ind t1 t1 l2); eauto 3 with slow.

      * pose proof (subvars_sub_free_vars_sub_filter sub1 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.

      * pose proof (subvars_sub_free_vars_sub_filter sub2 l2) as sv.
        disj_flat_map.
        allsimpl; allrw disjoint_app_l; repnd.
        eapply subvars_disjoint_r; eauto.
Qed.

Lemma differ_force_refl {o} :
  forall b a f (t : @NTerm o),
    !LIn a (get_utokens t)
    -> differ_force b a f t t.
Proof.
  nterm_ind t as [v|s ind|op bs ind] Case; introv nia; auto;[].

  Case "oterm".
  allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
  apply differ_force_oterm; auto.
  introv i.
  rw in_combine_same in i; repnd; subst.
  destruct b2 as [l t].
  constructor.
  eapply ind; eauto.
  introv i; destruct nia; rw lin_flat_map; eexists; eauto.
Qed.
Hint Resolve differ_force_refl : slow.

Lemma differ_force_subs_refl {o} :
  forall b a f (sub : @Sub o),
    !LIn a (get_utokens_sub sub)
    -> differ_force_subs b a f sub sub.
Proof.
  induction sub; introv nia; auto.
  destruct a0.
  allrw @get_utokens_sub_cons.
  allrw in_app_iff; allrw not_over_or; repnd.
  constructor; eauto with slow.
Qed.
Hint Resolve differ_force_subs_refl : slow.

Lemma differ_force_subs_refl_var_ren {o} :
  forall b a (f : @NTerm o) l1 l2,
    differ_force_subs b a f (var_ren l1 l2) (var_ren l1 l2).
Proof.
  introv.
  apply differ_force_subs_refl.
  rw @get_utokens_sub_var_ren; simpl; tcsp.
Qed.
Hint Resolve differ_force_subs_refl_var_ren : slow.

Definition differ_force_alpha {o} (b : nat) a (f : NTerm) (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
   & alpha_eq t1 u1
   # alpha_eq t2 u2
   # differ_force b a f u1 u2}}.

Definition differ_force_implies_differ_force_alpha {o} :
  forall (b : nat) a f (t1 t2 : @NTerm o),
    differ_force b a f t1 t2 -> differ_force_alpha b a f t1 t2.
Proof.
  introv d.
  exists t1 t2; auto.
Qed.
Hint Resolve differ_force_implies_differ_force_alpha : slow.

Lemma differ_force_alpha_refl {o} :
  forall b a f (t : @NTerm o),
    !LIn a (get_utokens t)
    -> differ_force_alpha b a f t t.
Proof.
  introv nia.
  unfold differ_force_alpha.
  exists t t; dands; eauto 3 with slow.
Qed.
Hint Resolve differ_force_alpha_refl : slow.

Definition differ_force_bterms {o} b a f (bs1 bs2 : list (@BTerm o)) :=
  br_bterms (differ_force_b b a f) bs1 bs2.

Lemma differ_force_change_bound_vars {o} :
  forall b a f vs (t1 t2 : @NTerm o),
    isprog f
    -> differ_force b a f t1 t2
    -> {u1 : NTerm
        & {u2 : NTerm
        & differ_force b a f u1 u2
        # alpha_eq t1 u1
        # alpha_eq t2 u2
        # disjoint (bound_vars u1) vs
        # disjoint (bound_vars u2) vs}}.
Proof.
  nterm_ind t1 as [v|s ind|op bs ind] Case; introv ispf d; auto.

  - Case "vterm".
    inversion d; subst.
    exists (@mk_var o v) (@mk_var o v); simpl; dands; eauto with slow.

  - Case "sterm".
    inversion d; subst.
    exists (sterm s) (sterm s); simpl; dands; auto.

  - Case "oterm".
    inversion d as [? ? ? ? ? aeq dt|?|?|? ? ? len nia imp]; subst; simphyps; cpx; ginv; clear d.

    + pose proof (ex_fresh_var vs) as h; exrepnd.
      pose proof (ex_fresh_var (v :: vs)) as q; exrepnd.
      pose proof (ex_fresh_var (v :: v0 :: vs)) as q; exrepnd.
      allsimpl; allrw not_over_or; repnd; GC.

      pose proof (ind arg1 []) as h; repeat (autodimp h hyp).
      pose proof (h arg2) as k; clear h.
      repeat (autodimp k hyp); exrepnd.

      fold_terms.
      try (fold (sp_force_nat arg1 x z f')).

      pose proof (change_bvars_alpha_spec f vs) as k; simpl in k; repnd.
      remember (change_bvars_alpha vs f) as f''; clear Heqf''.
      applydup @alpha_eq_preserves_isprog in k; auto.
      applydup @alpha_eq_preserves_isprog in aeq; auto.

      exists
        (sp_force_nat u1 v v0 f'')
        (bound2_cbv u2 v v0 b f'' a);
        dands; auto.

      * apply alpha_eq_sp_force_nat; eauto 3 with slow.

      * apply alpha_eq_bound2_cbv; eauto 3 with slow.

      * simpl; allrw app_nil_r.
        rw disjoint_app_l; repeat (rw disjoint_cons_l);
        dands; eauto 3 with slow.

      * simpl; allrw app_nil_r.
        allrw disjoint_app_l.
        allrw disjoint_cons_l.
        dands; eauto 3 with slow.

    + assert ({bs' : list BTerm
               & {bs2' : list BTerm
               & alpha_eq_bterms bs bs'
               # alpha_eq_bterms bs2 bs2'
               # differ_force_bterms b a f bs' bs2'
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
          pose proof (h t2) as k; clear h.
          repeat (autodimp k hyp);[]; exrepnd.

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
          { apply differ_force_bterm.
            apply differ_force_lsubst_aux; eauto 3 with slow;
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
      allunfold @differ_force_bterms.
      allunfold @br_bterms.
      allunfold @br_list; repnd.
      exists (oterm op bs') (oterm op bs2'); dands; eauto 3 with slow.

      * apply alpha_eq_oterm_combine; dands; auto.

      * apply alpha_eq_oterm_combine; dands; auto.
Qed.

Lemma differ_force_subst {o} :
  forall b a f (t1 t2 : @NTerm o) sub1 sub2,
    isprog f
    -> differ_force b a f t1 t2
    -> differ_force_subs b a f sub1 sub2
    -> differ_force_alpha b a f (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv dt ds.

  pose proof (unfold_lsubst sub1 t1) as h; exrepnd.
  pose proof (unfold_lsubst sub2 t2) as k; exrepnd.
  rw h0; rw k0.

  pose proof (differ_force_change_bound_vars
                b a f (sub_free_vars sub1 ++ sub_free_vars sub2)
                t1 t2) as d.
  repeat (autodimp d hyp); exrepnd.
  allrw disjoint_app_r; repnd.

  exists (lsubst_aux u1 sub1) (lsubst_aux u2 sub2); dands; auto.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply lsubst_aux_alpha_congr2; eauto with slow.

  - apply differ_force_lsubst_aux; auto.
Qed.
Hint Resolve differ_force_subst : slow.

Lemma differ_force_bterms_implies_eq_map_num_bvars {o} :
  forall b a f (bs1 bs2 : list (@BTerm o)),
    differ_force_bterms b a f bs1 bs2
    -> map num_bvars bs1 = map num_bvars bs2.
Proof.
  induction bs1; destruct bs2; introv d; allsimpl; auto;
  allunfold @differ_force_bterms; allunfold @br_bterms; allunfold @br_list;
  allsimpl; repnd; cpx.
  pose proof (d a0 b0) as h; autodimp h hyp.
  inversion h; subst.
  f_equal.
  unfold num_bvars; simpl; auto.
Qed.

Definition differ_force_sk {o} b a f (sk1 sk2 : @sosub_kind o) :=
  differ_force_b b a f (sk2bterm sk1) (sk2bterm sk2).

Inductive differ_force_sosubs {o} b a f : @SOSub o -> @SOSub o -> Type :=
| dfsosub_nil : differ_force_sosubs b a f [] []
| dfsosub_cons :
    forall v sk1 sk2 sub1 sub2,
      differ_force_sk b a f sk1 sk2
      -> differ_force_sosubs b a f sub1 sub2
      -> differ_force_sosubs b a f ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors differ_force_sosubs.

Lemma differ_force_bterms_cons {o} :
  forall b a f (b1 b2 : @BTerm o) bs1 bs2,
    differ_force_bterms b a f (b1 :: bs1) (b2 :: bs2)
    <=> (differ_force_b b a f b1 b2 # differ_force_bterms b a f bs1 bs2).
Proof.
  unfold differ_force_bterms; introv.
  rw @br_bterms_cons_iff; sp.
Qed.

Lemma differ_force_mk_abs_substs {o} :
  forall b a f (bs1 bs2 : list (@BTerm o)) vars,
    differ_force_bterms b a f bs1 bs2
    -> length vars = length bs1
    -> differ_force_sosubs b a f (mk_abs_subst vars bs1) (mk_abs_subst vars bs2).
Proof.
  induction bs1; destruct bs2; destruct vars; introv d m; allsimpl; cpx; tcsp.
  - provefalse.
    apply differ_force_bterms_implies_eq_map_num_bvars in d; allsimpl; cpx.
  - apply differ_force_bterms_cons in d; repnd.
    destruct s, a0, b0.
    inversion d0; subst.
    boolvar; auto.
Qed.

Lemma differ_force_sosubs_implies_eq_length {o} :
  forall b a f (sub1 sub2 : @SOSub o),
    differ_force_sosubs b a f sub1 sub2
    -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv d; inversion d; subst; allsimpl; tcsp.
Qed.

Lemma differ_force_b_change_bound_vars {o} :
  forall b a f vs (b1 b2 : @BTerm o),
    isprog f
    -> differ_force_b b a f b1 b2
    -> {u1 : BTerm
        & {u2 : BTerm
           & differ_force_b b a f u1 u2
           # alpha_eq_bterm b1 u1
           # alpha_eq_bterm b2 u2
           # disjoint (bound_vars_bterm u1) vs
           # disjoint (bound_vars_bterm u2) vs}}.
Proof.
  introv isp d.
  pose proof (differ_force_change_bound_vars
                b a f vs (oterm Exc [b1]) (oterm Exc [b2])) as h.
  repeat (autodimp h hyp).
  - apply differ_force_oterm; simpl; tcsp.
    introv i; dorn i; tcsp; cpx.
  - exrepnd.
    inversion h2 as [|?|? ? ? len1 imp1]; subst; allsimpl; cpx.
    inversion h3 as [|?|? ? ? len2 imp2]; subst; allsimpl; cpx.
    pose proof (imp1 0) as k1; autodimp k1 hyp; allsimpl; clear imp1.
    pose proof (imp2 0) as k2; autodimp k2 hyp; allsimpl; clear imp2.
    allunfold @selectbt; allsimpl.
    allrw app_nil_r.
    exists x x0; dands; auto.
    inversion h0 as [|?|?|? ? ? ? ? i]; subst; allsimpl; GC.
    apply i; sp.
Qed.

Lemma differ_force_sk_change_bound_vars {o} :
  forall b a f vs (sk1 sk2 : @sosub_kind o),
    isprog f
    -> differ_force_sk b a f sk1 sk2
    -> {u1 : sosub_kind
        & {u2 : sosub_kind
        & differ_force_sk b a f u1 u2
        # alphaeq_sk sk1 u1
        # alphaeq_sk sk2 u2
        # disjoint (bound_vars_sk u1) vs
        # disjoint (bound_vars_sk u2) vs}}.
Proof.
  introv isp d.
  apply (differ_force_b_change_bound_vars b a f vs) in d; auto; exrepnd; allsimpl.
  exists (bterm2sk u1) (bterm2sk u2).
  destruct u1, u2, sk1, sk2; allsimpl; dands; auto;
  apply alphaeq_sk_iff_alphaeq_bterm2; simpl; auto.
Qed.

Lemma differ_force_sosubs_change_bound_vars {o} :
  forall b a f vs (sub1 sub2 : @SOSub o),
    isprog f
    -> differ_force_sosubs b a f sub1 sub2
    -> {sub1' : SOSub
        & {sub2' : SOSub
        & differ_force_sosubs b a f sub1' sub2'
        # alphaeq_sosub sub1 sub1'
        # alphaeq_sosub sub2 sub2'
        # disjoint (bound_vars_sosub sub1') vs
        # disjoint (bound_vars_sosub sub2') vs}}.
Proof.
  induction sub1; destruct sub2; introv isp d.
  - exists ([] : @SOSub o) ([] : @SOSub o); dands; simpl; tcsp.
  - inversion d.
  - inversion d.
  - inversion d as [|? ? ? ? ? dsk dso]; subst; clear d.
    apply IHsub1 in dso; exrepnd; auto.
    apply (differ_force_sk_change_bound_vars b a f vs) in dsk; exrepnd; auto.
    exists ((v,u1) :: sub1') ((v,u2) :: sub2'); dands; simpl; auto;
    allrw disjoint_app_l; dands; eauto with slow.
Qed.

Lemma sosub_find_some_if_differ_force_sosubs {o} :
  forall b a f (sub1 sub2 : @SOSub o) v sk,
    differ_force_sosubs b a f sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind & differ_force_sk b a f sk sk' # sosub_find sub2 v = Some sk'}.
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

Lemma sosub_find_none_if_differ_force_sosubs {o} :
  forall b a f (sub1 sub2 : @SOSub o) v,
    differ_force_sosubs b a f sub1 sub2
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

Lemma differ_force_subs_combine {o} :
  forall b a f (ts1 ts2 : list (@NTerm o)) vs,
    length ts1 = length ts2
    -> (forall t1 t2,
          LIn (t1,t2) (combine ts1 ts2)
          -> differ_force b a f t1 t2)
    -> differ_force_subs b a f (combine vs ts1) (combine vs ts2).
Proof.
  induction ts1; destruct ts2; destruct vs; introv len imp; allsimpl; cpx; tcsp.
Qed.

Lemma differ_force_apply_list {o} :
  forall b a f (ts1 ts2 : list (@NTerm o)) t1 t2,
    differ_force b a f t1 t2
    -> length ts1 = length ts2
    -> (forall x y, LIn (x,y) (combine ts1 ts2) -> differ_force b a f x y)
    -> differ_force b a f (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; destruct ts2; introv d l i; allsimpl; cpx.
  apply IHts1; auto.
  apply differ_force_oterm; simpl; tcsp.
  introv k.
  dorn k;[|dorn k]; cpx; constructor; auto.
Qed.

Lemma differ_force_sosub_filter {o} :
  forall b a f (sub1 sub2 : @SOSub o) vs,
    differ_force_sosubs b a f sub1 sub2
    -> differ_force_sosubs b a f (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ_sosub_filter : slow.

Lemma differ_force_sosubs_sosub_filter {o} :
  forall b a f (sub1 sub2 : @SOSub o) vs,
    differ_force_sosubs b a f sub1 sub2
    -> differ_force_sosubs b a f (sosub_filter sub1 vs) (sosub_filter sub2 vs).
Proof.
  induction sub1; destruct sub2; introv d;
  inversion d as [|? ? ? ? ? dsk dso]; subst; auto.
  destruct sk1, sk2; allsimpl.
  inversion dsk; subst.
  boolvar; tcsp.
Qed.
Hint Resolve differ_force_sosubs_sosub_filter : slow.

Lemma differ_force_sosub_aux {o} :
  forall b a f (t : @SOTerm o) sub1 sub2,
    no_utokens t
    -> isprog f
    -> differ_force_sosubs b a f sub1 sub2
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub1)
    -> disjoint (free_vars_sosub sub1) (bound_vars_sosub sub1)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub1)
    -> disjoint (fo_bound_vars t) (free_vars_sosub sub2)
    -> disjoint (free_vars_sosub sub2) (bound_vars_sosub sub2)
    -> disjoint (all_fo_vars t) (bound_vars_sosub sub2)
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ_force b a f (sosub_aux sub1 t) (sosub_aux sub2 t).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case;
  introv nout ispf ds disj1 disj2 disj3 disj4 disj5 disj6;
  introv cov1 cov2; allsimpl; tcsp.

  - Case "sovar".
    allrw @no_utokens_sovar.
    allrw @cover_so_vars_sovar; repnd.
    allrw disjoint_cons_l; repnd.
    remember (sosub_find sub1 (v, length ts)) as f1; symmetry in Heqf1.
    destruct f1.

    + applydup (sosub_find_some_if_differ_force_sosubs b a f sub1 sub2) in Heqf1; auto.
      exrepnd.
      rw Heqf2.
      destruct s as [l1 t1].
      destruct sk' as [l2 t2].
      inversion Heqf0; subst.
      apply differ_force_lsubst_aux; auto.

      * apply differ_force_subs_combine; allrw map_length; auto.
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

    + applydup (sosub_find_none_if_differ_force_sosubs b a f sub1 sub2) in Heqf1; auto.
      rw Heqf0.
      apply differ_force_apply_list; allrw map_length; auto.
      introv i.
      rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
      apply in_combine_same in i1; repnd; subst; allsimpl.
      disj_flat_map.
      apply ind; auto.

  - Case "soterm".
    allrw @no_utokens_soterm; repnd.
    assert (forall x, !LIn x (get_utokens_o op)) as niop.
    { rw nout0; simpl; tcsp. }
    allrw @cover_so_vars_soterm.
    apply differ_force_oterm; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx.
    apply in_combine_same in i1; repnd; subst; allsimpl.
    destruct a0 as [l t].
    disj_flat_map.
    allsimpl; allrw disjoint_app_l; repnd.
    applydup nout in i0; allsimpl.
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

Lemma differ_force_sosub {o} :
  forall b a f (t : @SOTerm o) (sub1 sub2 : SOSub),
    no_utokens t
    -> isprog f
    -> differ_force_sosubs b a f sub1 sub2
    -> cover_so_vars t sub1
    -> cover_so_vars t sub2
    -> differ_force_alpha b a f (sosub sub1 t) (sosub sub2 t).
Proof.
  introv nout ispf d c1 c2.
  pose proof (unfold_sosub sub1 t) as h.
  destruct h as [sub1' h]; destruct h as [t1 h]; repnd; rw h.
  pose proof (unfold_sosub sub2 t) as k.
  destruct k as [sub2' k]; destruct k as [t2 k]; repnd; rw k.

  pose proof (differ_force_sosubs_change_bound_vars
                b a f (all_fo_vars t1
                                 ++ all_fo_vars t2
                                 ++ free_vars_sosub sub1
                                 ++ free_vars_sosub sub2
                    )
                sub1 sub2) as e.
  repeat (autodimp e hyp).
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

  { dands; eauto 3 with slow.
    - rw <- ev1; eauto 3with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto 3 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto with slow.
    - rw <- ev2; eauto with slow.
    - eapply eqvars_disjoint;[apply eqvars_sym; exact ev3|].
      apply disjoint_app_l; dands; eauto 3 with slow.
      rw <- efv1.
      eapply subvars_disjoint_l;[exact ev6|]; eauto with slow. }

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

  apply differ_force_sosub_aux; eauto 3 with slow.
Qed.

Lemma differ_force_mk_instance {o} :
  forall b a f (t : @SOTerm o) vars bs1 bs2,
    no_utokens t
    -> isprog f
    -> matching_bterms vars bs1
    -> matching_bterms vars bs2
    -> socovered t vars
    -> socovered t vars
    -> differ_force_bterms b a f bs1 bs2
    -> differ_force_alpha b a f (mk_instance vars bs1 t) (mk_instance vars bs2 t).
Proof.
  introv nout ispf m1 m2 sc1 sc2 dbs.
  unfold mk_instance.
  applydup @matching_bterms_implies_eq_length in m1.
  applydup (@differ_force_mk_abs_substs o b a f bs1 bs2 vars) in dbs; auto.

  apply differ_force_sosub; auto;
  apply socovered_implies_cover_so_vars; auto.
Qed.

Definition differ_force_bterms_alpha {o} b a f (bs1 bs2 : list (@BTerm o)) :=
  {bs1' : list BTerm
   & {bs2' : list BTerm
   & alpha_eq_bterms bs1 bs1'
   # alpha_eq_bterms bs2 bs2'
   # differ_force_bterms b a f bs1' bs2' }}.

Definition differ_force_b_alpha {o} b a f (b1 b2 : @BTerm o) :=
  {u1 : BTerm
   & {u2 : BTerm
   & alpha_eq_bterm b1 u1
   # alpha_eq_bterm b2 u2
   # differ_force_b b a f u1 u2 }}.

Lemma differ_force_alpha_oterm {o} :
  forall b a f op (bs1 bs2 : list (@BTerm o)),
    !LIn a (get_utokens_o op)
    -> differ_force_bterms_alpha b a f bs1 bs2
    -> differ_force_alpha
         b a f
         (oterm op bs1)
         (oterm op bs2).
Proof.
  introv nia d.
  unfold differ_force_bterms_alpha in d; exrepnd.
  exists (oterm op bs1') (oterm op bs2').
  dands; eauto 3 with slow; try (apply alpha_eq_oterm_combine; complete auto).
  allunfold @alpha_eq_bterms; repnd.
  unfold differ_force_bterms, br_bterms, br_list in d1; repnd.
  eauto 3 with slow.
Qed.

Lemma differ_force_bterms_nil {o} :
  forall b a f, @differ_force_bterms o b a f [] [].
Proof.
  unfold differ_force_bterms, br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve differ_force_bterms_nil : slow.

Lemma differ_force_bterms_cons_if {o} :
  forall b a f (b1 b2 : @BTerm o) bs1 bs2,
    differ_force_b b a f b1 b2
    -> differ_force_bterms b a f bs1 bs2
    -> differ_force_bterms b a f (b1 :: bs1) (b2 :: bs2).
Proof.
  introv d1 d2; apply differ_force_bterms_cons; sp.
Qed.
Hint Resolve differ_force_bterms_cons_if : slow.

Lemma implies_differ_force_bterms_alpha {o} :
  forall b a f (bs1 bs2 : list (@BTerm o)),
    length bs1 = length bs2
    -> (forall b1 b2,
          LIn (b1,b2) (combine bs1 bs2)
          -> differ_force_b_alpha b a f b1 b2)
    -> differ_force_bterms_alpha b a f bs1 bs2.
Proof.
  induction bs1; destruct bs2; introv len1 imp; allsimpl; ginv; auto.
  - exists ([] : list (@BTerm o)) ([] : list (@BTerm o)); dands; eauto 3 with slow.
  - cpx.
    pose proof (imp a0 b0) as d; autodimp d hyp.
    unfold differ_force_b_alpha in d; exrepnd.
    pose proof (IHbs1 bs2) as h; repeat (autodimp h hyp).
    unfold differ_force_bterms_alpha in h; exrepnd.
    exists (u1 :: bs1') (u2 :: bs2').
    dands; eauto 3 with slow.
Qed.

Lemma implies_differ_force_b_alpha {o} :
  forall b a f vs (t1 t2 : @NTerm o),
    differ_force_alpha b a f t1 t2
    -> differ_force_b_alpha b a f (bterm vs t1) (bterm vs t2).
Proof.
  introv d.
  unfold differ_force_alpha in d; exrepnd.
  exists (bterm vs u1) (bterm vs u2).
  dands; eauto 3 with slow.
Qed.

Lemma differ_force_b_implies_alpha {o} :
  forall b a f (b1 b2 : @BTerm o),
    differ_force_b b a f b1 b2
    -> differ_force_b_alpha b a f b1 b2.
Proof.
  introv d.
  exists b1 b2; dands; auto.
Qed.
Hint Resolve differ_force_b_implies_alpha : slow.

Lemma differ_forces_alpha_nat {o} :
  forall b a f (t1 t2 : @NTerm o) x z f',
    isprog f
    -> alpha_eq f f'
    -> differ_force_alpha b a f t1 t2
    -> differ_force_alpha
         b a f
         (sp_force_nat t1 x z f')
         (bound2_cbv t2 x z b f' a).
Proof.
  introv ispf aeq d.
  applydup @alpha_eq_preserves_isprog in aeq; auto.
  allunfold @differ_force_alpha; exrepnd.
  exists (sp_force_nat u1 x z f') (bound2_cbv u2 x z b f' a).
  dands; eauto 3 with slow.
  - apply alpha_eq_sp_force_nat; eauto 3 with slow.
  - apply alpha_eq_bound2_cbv; eauto 3 with slow.
Qed.

Lemma differ_force_isvalue_like {o} :
  forall b a f (t1 t2 : @NTerm o),
    isvalue_like t1
    -> differ_force b a f t1 t2
    -> (isvalue_like t2
        # forall v,
            differ_force_alpha
              b a f
              (pushdown_fresh v t1)
              (pushdown_fresh v t2)).
Proof.
  introv isv d.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst.

    { inversion d as [? ? ? ? ? ? aeq d'|?|?|? ? ? len nia imp];
      subst; allsimpl; clear d; tcsp; GC;[].
      dands; eauto 3 with slow.
      introv.

      apply differ_force_alpha_oterm; auto.
      apply implies_differ_force_bterms_alpha; allrw @length_mk_fresh_bterms; auto.
      introv i.
      allunfold @mk_fresh_bterms.
      allrw <- @map_combine.
      allrw in_map_iff; exrepnd; allsimpl; ginv.
      applydup imp in i1.
      inversion i0 as [? ? ? ? d]; subst; clear i0.
      unfold mk_fresh_bterm.
      apply implies_differ_force_b_alpha.
      unfold maybe_new_var; boolvar;
      [|apply differ_force_implies_differ_force_alpha;
         apply differ_force_oterm; simpl; tcsp;
         introv i; repndors; tcsp; complete ginv].

      pose proof (ex_fresh_var (all_vars t1 ++ all_vars t2)) as fv; exrepnd.
      exists (mk_fresh v0 t1) (mk_fresh v0 t2).
      allrw in_app_iff; allrw not_over_or; repnd.
      dands; eauto 3 with slow;
      try (complete (apply differ_force_oterm; simpl; tcsp; introv i; repndors; ginv; tcsp));
      apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp;
      try (rw @lsubst_trivial4; simpl;
           [|apply disjoint_singleton_l; apply newvar_prop
            |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]);
      try (rw @lsubst_trivial4; simpl;
           [auto
           |apply disjoint_singleton_l; auto
           |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]).
    }

    { inversion d; subst; clear d.
      dands; eauto 3 with slow.
      introv; simpl; auto.
      apply differ_force_implies_differ_force_alpha; auto.
    }

  - apply isexc_implies2 in isv; exrepnd; subst.
    inversion d as [? ? ? ? ? ? aeq d'|?|?|? ? ? len nia imp];
      subst; allsimpl; clear d; tcsp; GC;[].
    dands; eauto 3 with slow.
    introv.

    apply differ_force_alpha_oterm; simpl; tcsp.
    apply implies_differ_force_bterms_alpha; allrw @length_mk_fresh_bterms; auto.
    introv i.
    allunfold @mk_fresh_bterms.
    allrw <- @map_combine.
    allrw in_map_iff; exrepnd; allsimpl; ginv.
    applydup imp in i1.
    inversion i0 as [? ? ? ? d]; subst; clear i0.
    unfold mk_fresh_bterm.
    apply implies_differ_force_b_alpha.
    unfold maybe_new_var; boolvar;
    [|apply differ_force_implies_differ_force_alpha;
       apply differ_force_oterm; simpl; tcsp;
       introv i; repndors; tcsp; complete ginv].

    pose proof (ex_fresh_var (all_vars t1 ++ all_vars t2)) as fv; exrepnd.
    exists (mk_fresh v0 t1) (mk_fresh v0 t2).
    allrw in_app_iff; allrw not_over_or; repnd.
    dands; eauto 3 with slow;
    try (complete (apply differ_force_oterm; simpl; tcsp; introv i; repndors; ginv; tcsp));
    apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; tcsp;
    try (rw @lsubst_trivial4; simpl;
         [|apply disjoint_singleton_l; apply newvar_prop
          |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]);
    try (rw @lsubst_trivial4; simpl;
         [auto
         |apply disjoint_singleton_l; auto
         |introv i; repndors; tcsp; ginv; simpl; apply disjoint_singleton_l; auto]).
Qed.

Lemma differ_force_alpha_alpha_eq1 {o} :
  forall b a f (t1 t2 : @NTerm o) t,
    alpha_eq t1 t
    -> differ_force_alpha b a f t1 t2
    -> differ_force_alpha b a f t t2.
Proof.
  introv aeq d.
  allunfold @differ_force_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Lemma differ_force_alpha_alpha_eq2 {o} :
  forall b a f (t1 t2 : @NTerm o) t,
    alpha_eq t2 t
    -> differ_force_alpha b a f t1 t2
    -> differ_force_alpha b a f t1 t.
Proof.
  introv aeq d.
  allunfold @differ_force_alpha; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.

Lemma differ_force_alpha_mk_fresh {o} :
  forall b a f v (t1 t2 : @NTerm o),
    differ_force_alpha b a f t1 t2
    -> differ_force_alpha b a f (mk_fresh v t1) (mk_fresh v t2).
Proof.
  introv d.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_fresh v u1) (mk_fresh v u2).
  dands; eauto 3 with slow; try (apply implies_alpha_eq_mk_fresh); auto.
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; cpx.
Qed.

Lemma differ_force_subst_utokens_aux {o} :
  forall b a f (t1 t2 : @NTerm o) sub,
    isprog f
    -> !LIn a (utok_sub_dom sub)
    -> !LIn a (get_utokens_utok_sub sub)
    -> disjoint (bound_vars t1) (free_vars_utok_sub sub)
    -> disjoint (bound_vars t2) (free_vars_utok_sub sub)
    -> disjoint (get_utokens f) (utok_sub_dom sub)
    -> differ_force b a f t1 t2
    -> differ_force
         b a f
         (subst_utokens_aux t1 sub)
         (subst_utokens_aux t2 sub).
Proof.
  nterm_ind t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv ispf nia1 nia2 disj1 disj2 duf d.

  - Case "vterm".
    inversion d as [|?|?|]; subst; allsimpl; eauto 3 with slow.

  - Case "sterm".
    inversion d as [|?|?|]; subst; allsimpl; eauto 3 with slow.

  - Case "oterm".
    inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp];
      subst; clear d; GC; fold_terms;[|].

    + allsimpl; allrw app_nil_r; fold_terms.
      repeat (allrw disjoint_app_l; allrw disjoint_cons_l; repnd).
      rw @subst_utok_if_not_in; auto;[]; fold_terms.
      rw (trivial_subst_utokens_aux f'); eauto 3 with slow;
      [|apply alphaeq_preserves_utokens in aeq; rw <- aeq; auto].

      apply differ_force_nat; auto.

      pose proof (ind1 arg1 []) as h; repeat (autodimp h hyp).

    + allrw @subst_utokens_aux_oterm; allsimpl.
      remember (get_utok op1) as guo1; symmetry in Heqguo1; destruct guo1.

      * unfold subst_utok.
        remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf; eauto 3 with slow.
        { applydup @utok_sub_find_some in Heqsf.
          unfold get_utokens_utok_sub in nia2.
          apply in_utok_sub_eta in Heqsf0; repnd.
          disj_flat_map.
          apply differ_force_refl.
          intro k; destruct nia2; rw lin_flat_map; eexists; eauto. }
        apply get_utok_some in Heqguo1; subst; allsimpl; allrw not_over_or; repnd; GC.
        apply differ_force_oterm; allrw map_length; simpl; tcsp;[].
        introv i; rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
        applydup imp in i1; applydup in_combine in i1; repnd.
        disj_flat_map.
        destruct a1 as [l1 u1].
        destruct a0 as [l2 u2].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? d1]; subst; clear i0.
        constructor; auto.

        pose proof (ind1 u1 l2) as q; autodimp q hyp.

      * apply differ_force_oterm; allrw map_length; auto.
        introv i; rw <- @map_combine in i; rw in_map_iff in i; exrepnd; cpx; allsimpl.
        applydup imp in i1; applydup in_combine in i1; repnd.
        disj_flat_map.
        destruct a1 as [l1 u1].
        destruct a0 as [l2 u2].
        allsimpl; allrw disjoint_app_l; repnd.
        inversion i0 as [? ? ? d1]; subst; clear i0.
        constructor; auto.

        pose proof (ind1 u1 l2) as q; autodimp q hyp.
Qed.

Lemma differ_force_alpha_subst_utokens {o} :
  forall b a f (t1 t2 : @NTerm o) sub,
    isprog f
    -> !LIn a (utok_sub_dom sub)
    -> !LIn a (get_utokens_utok_sub sub)
    -> disjoint (get_utokens f) (utok_sub_dom sub)
    -> differ_force_alpha b a f t1 t2
    -> differ_force_alpha
         b a f
         (subst_utokens t1 sub)
         (subst_utokens t2 sub).
Proof.
  introv ispf nia1 nia2 disj1 d.
  unfold differ_force_alpha in d; exrepnd.

  eapply differ_force_alpha_alpha_eq1;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d0|].
  eapply differ_force_alpha_alpha_eq2;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d2|].
  clear dependent t1.
  clear dependent t2.

  pose proof (differ_force_change_bound_vars
                b a f (free_vars_utok_sub sub)
                u1 u2 ispf d1) as d; exrepnd.
  rename u0 into t1.
  rename u3 into t2.

  eapply differ_force_alpha_alpha_eq1;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d3|].
  eapply differ_force_alpha_alpha_eq2;[eapply alpha_eq_subst_utokens_same;apply alpha_eq_sym;exact d4|].
  clear dependent u1.
  clear dependent u2.

  pose proof (unfold_subst_utokens sub t1) as h; exrepnd.
  pose proof (unfold_subst_utokens sub t2) as k; exrepnd.
  rename t' into u1.
  rename t'0 into u2.
  rw h0; rw k0.

  eapply differ_force_alpha_alpha_eq1;[apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u1 t1 sub sub); eauto 3 with slow|].
  eapply differ_force_alpha_alpha_eq2;[apply alpha_eq_sym;apply (alpha_eq_subst_utokens_aux u2 t2 sub sub); eauto 3 with slow|].

  apply differ_force_implies_differ_force_alpha.
  apply differ_force_subst_utokens_aux; auto.
Qed.

Lemma implies_differ_force_alpha_eapply {o} :
  forall b a f (n1 n2 e1 e2 : @NTerm o),
    differ_force_alpha b a f n1 n2
    -> differ_force_alpha b a f e1 e2
    -> differ_force_alpha
         b a f
         (mk_eapply n1 e1)
         (mk_eapply n2 e2).
Proof.
  introv d1 d2.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u3 u2).
  dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply differ_force_oterm; simpl; tcsp.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma differ_force_preserves_iscan {o} :
  forall b a f (t1 t2 : @NTerm o),
    differ_force b a f t1 t2
    -> iscan t1
    -> iscan t2.
Proof.
  introv diff isc.
  apply iscan_implies in isc; repndors; exrepnd; subst;
  inversion diff; subst; simpl; auto.
Qed.

Lemma differ_force_lam_implies {o} :
  forall b a f v u (t1 : @NTerm o),
    differ_force b a f (mk_lam v u) t1
    -> {u1 : NTerm
        & t1 = mk_lam v u1
        # differ_force b a f u u1 }.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.

  pose proof (imp (bterm [v] u) x) as d1; autodimp d1 hyp.
  clear imp.

  inversion d1 as [? ? ? d2]; subst; clear d1.
  fold_terms.

  eexists; dands; eauto.
Qed.

Lemma differ_force_nseq_implies {o} :
  forall b a f s (t1 : @NTerm o),
    differ_force b a f (mk_nseq s) t1
    -> t1 = mk_nseq s.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.
Qed.

Lemma differ_force_nat_implies {o} :
  forall b a f n (t1 : @NTerm o),
    differ_force b a f (mk_nat n) t1
    -> t1 = mk_nat n.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? ? ? imp]; subst; allsimpl; cpx; clear d; allsimpl; GC.
Qed.

Lemma differ_force_alpha_mk_lam {o} :
  forall b a f v (t1 t2 : @NTerm o),
    differ_force_alpha b a f t1 t2
    -> differ_force_alpha b a f (mk_lam v t1) (mk_lam v t2).
Proof.
  introv d.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_lam v u1) (mk_lam v u2); dands;
  try (apply implies_alpha_eq_mk_lam; eauto with slow).
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; cpx.
Qed.

Lemma differ_force_exception {o} :
  forall b a f (n e t : @NTerm o),
    differ_force b a f (mk_exception n e) t
    -> {n1 : NTerm
        & {e1 : NTerm
        & t = mk_exception n1 e1
        # differ_force b a f n n1
        # differ_force b a f e e1 }}.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len1 nia imp]; subst; tcsp.
  allsimpl; cpx; GC; allsimpl.
  pose proof (imp (nobnd n) x) as h1; autodimp h1 hyp.
  pose proof (imp (nobnd e) y) as h2; autodimp h2 hyp.
  clear imp.
  inversion h1 as [? ? ? d1]; subst; clear h1.
  inversion h2 as [? ? ? d2]; subst; clear h2.
  fold_terms.
  eexists; eexists; dands; eauto.
Qed.

Lemma differ_force_alpha_exception {o} :
  forall b a f (n e t : @NTerm o),
    differ_force_alpha b a f (mk_exception n e) t
    -> {n1 : NTerm
        & {e1 : NTerm
        & t = mk_exception n1 e1
        # differ_force_alpha b a f n n1 }}.
Proof.
  introv d.
  unfold differ_force_alpha in d; exrepnd.
  allapply @alpha_eq_exception; exrepnd; subst.
  allapply @differ_force_exception; exrepnd.
  subst; tcsp.

  apply alpha_eq_sym in d2; apply alpha_eq_exception in d2.
  exrepnd; subst.
  eexists; eexists; dands; auto.
  exists a' n1; dands; eauto 3 with slow.
Qed.

Lemma implies_differ_force_alpha_exception {o} :
  forall b a f (n1 n2 e1 e2 : @NTerm o),
    differ_force_alpha b a f n1 n2
    -> differ_force_alpha b a f e1 e2
    -> differ_force_alpha
         b a f
         (mk_exception n1 e1)
         (mk_exception n2 e2).
Proof.
  introv d1 d2.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_exception u0 u1) (mk_exception u3 u2).
  dands; eauto 3 with slow; try (apply implies_alphaeq_exception; auto).
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; auto.
Qed.

Lemma differ_force_alpha_mk_eapply {o} :
  forall b a f (a1 a2 b1 b2 : @NTerm o),
    differ_force_alpha b a f a1 a2
    -> differ_force_alpha b a f b1 b2
    -> differ_force_alpha b a f (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u3 u2); dands; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply alpha_eq_oterm_combine; simpl; dands; auto.
    introv i; repndors; cpx; auto; apply alphaeqbt_nilv2; auto.
  - apply differ_force_oterm; simpl; tcsp.
    introv i; repndors; cpx; constructor; auto.
Qed.

Lemma computation_step_differ_force {o} :
  forall lib (t1 t2 : @NTerm o) b a u f,
    isprog f
    -> wf_term t1
    -> wf_term t2
    -> !LIn a (get_utokens f)
    -> differ_force b a f t1 t2
    -> compute_step lib t1 = csuccess u
    -> hasvalue_like lib u
    -> (forall z, LIn z (get_ints t1) -> Z.abs_nat z < b)
    -> {t1' : NTerm
        & {t2' : NTerm
        & reduces_to lib u t1'
        # reduces_to lib t2 t2'
        # differ_force_alpha b a f t1' t2'}}.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv ispf wft1 wft2 niaf d comp hv i.

  - Case "vterm".
    simpl.
    inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    inversion d as [|?|?|]; subst; clear d.
    exists (sterm f1) (sterm f1); dands; eauto 3 with slow.

  - Case "oterm".
    dopid op1 as [can|ncan|exc|abs] SCase; ginv.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      inversion d; subst.
      exists (oterm (Can can) bs1) (oterm (Can can) bs2); dands; eauto with slow.

    + SCase "NCan".
      destruct bs1 as [|b1 bs1]; try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (simpl in comp; ginv)).

      { (* Non fresh case *)

        destruct t1 as [v1|f1|op1 bs1'].

        - destruct t2 as [v2|f2c|op2 bs2]; try (complete (inversion d)).
          inversion d as [|?|?|]; subst; simphyps; cpx; ginv.

        - (* sequences *)
          destruct t2 as [v2|f2|op2 bs2];
          try (complete (inversion d));[].

          csunf comp; allsimpl.

          dopid_noncan ncan SSCase; allsimpl; ginv.

          { SSCase "NApply".
            clear ind1.
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl;[].

            inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
            cpx; ginv; allsimpl.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd arg) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3; subst; clear d3.

            fold_terms.

            exists (mk_eapply (sterm f1) arg)
                   (mk_eapply (sterm f1) t0).
            dands; eauto 3 with slow.
            apply implies_differ_force_alpha_eapply; eauto 3 with slow.
          }

          { SSCase "NEApply".
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl;[].

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].

            rw @wf_term_eq in wft1; rw @nt_wf_eapply_iff in wft1; exrepnd; allunfold @nobnd; ginv.
            simpl in len1; cpx.
            simpl in imp.
            fold_terms.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [|?|?|]; subst; clear d3;[].
            fold_terms.

            repndors; exrepnd; subst.

            - apply compute_step_eapply2_success in comp1; repnd; GC.
              repndors; exrepnd; subst; ginv; allsimpl; GC.
              inversion d4 as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d4; GC;[].
              cpx; clear imp; fold_terms.

              exists (f0 n) (f0 n); dands; eauto 3 with slow.

              { apply reduces_to_if_step.
                csunf; simpl.
                dcwf h; simpl; boolvar; try omega.
                rw @Znat.Nat2Z.id; auto. }

              { apply differ_force_alpha_refl; auto.
                allrw @nt_wf_sterm_iff.
                pose proof (wft3 n) as h; clear wft3; repnd.
                rw h; simpl; tcsp. }

            - apply isexc_implies2 in comp0; exrepnd; subst.
              inversion d4 as [|?|?|?]; subst; allsimpl; clear d4.
              exists (oterm Exc l) (oterm Exc bs2); dands; eauto 3 with slow.

            - pose proof (ind1 b0 b0 []) as h; clear ind1.
              repeat (autodimp h hyp); eauto 3 with slow;[].
              allrw <- @wf_eapply_iff; repnd.
              pose proof (h t0 b a x f) as ih; clear h.
              applydup @preserve_nt_wf_compute_step in comp1; auto.
              allsimpl; autorewrite with slow in *.
              repeat (autodimp ih hyp); eauto 3 with slow.
              { apply hasvalue_like_eapply_sterm_implies in hv; exrepnd; eauto 3 with slow. }
              exrepnd.

              exists (mk_eapply (sterm f1) t1')
                     (mk_eapply (sterm f1) t2').
              dands; eauto 3 with slow.
              { apply implies_eapply_red_aux; eauto 3 with slow. }
              { apply implies_eapply_red_aux; eauto 3 with slow. }
              { apply implies_differ_force_alpha_eapply; eauto 3 with slow. }
          }

          { SSCase "NFix".
            apply compute_step_fix_success in comp; repnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.
            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.
            inversion d2 as [|?|?|]; subst; clear d2.
            fold_terms.

            exists (mk_apply (sterm f1) (mk_fix (sterm f1)))
                   (mk_apply (sterm f1) (mk_fix (sterm f1))).
            dands; eauto 3 with slow.
            apply differ_force_alpha_refl; simpl; tcsp.
          }

          { SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.

            inversion d as [? ? ? ? ? aeq1 d1|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[|].

            { inversion d1; subst; clear d1;
              allapply @hasvalue_like_subst_less_seq; tcsp. }

            { cpx; allsimpl.
              autorewrite with slow in *.

              pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
              pose proof (imp (bterm [v] x) y) as d2; autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d3; subst; clear d3.
              inversion d2 as [? ? ? d4]; subst; clear d2.
              fold_terms.

              exists (subst x v (sterm f1))
                     (subst t2 v (sterm f1)).
              dands; eauto 3 with slow.
              apply differ_force_subst; auto. }
          }

          { SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.

            pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd a0) y) as d2; autodimp d2 hyp.
            pose proof (imp (bterm [v] x) z) as d3; autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [? ? ? d5]; subst; clear d3.

            allrw <- @wf_try_iff; repnd.

            inversion d as [?|?|?|? ? ? len1 nia imp1]; subst; allsimpl; clear d; GC;[].

            exists (mk_atom_eq a0 a0 (sterm f1) mk_bot)
                   (mk_atom_eq t0 t0 (sterm f1) mk_bot);
              dands; eauto 3 with slow.
            apply differ_force_implies_differ_force_alpha.
            apply differ_force_oterm; simpl; tcsp.
            introv j; repndors; tcsp; ginv; constructor; eauto 2 with slow.
            apply differ_force_refl; simpl; tcsp.
          }

          { SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd a0) y) as d2; autodimp d2 hyp.
            pose proof (imp (nobnd b0) z) as d3; autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d4; subst; clear d4.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [? ? ? d5]; subst; clear d3.
            fold_terms.

            exists b0 t0.
            dands; eauto 3 with slow.
          }

        - (* Now destruct op1 *)
          dopid op1 as [can1|ncan1|exc1|abs1] SSCase; ginv.

          + SSCase "Can".
            allsimpl.

            (* Because the principal argument is canonical we can destruct ncan *)
            dopid_noncan ncan SSSCase.

            * SSSCase "NApply".

              clear ind1.
              csunf comp; allsimpl.
              apply compute_step_apply_success in comp; repndors; exrepnd; subst.

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (bterm [] (oterm (Can NLambda) [bterm [v] b0])) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (bterm [] arg) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                repeat (allsimpl; cpx).

                pose proof (imp1 (bterm [v] b0) x) as d1; clear imp1.
                autodimp d1 hyp.

                inversion d1 as [? ? ? d2]; subst; clear d1.

                exists (subst b0 v arg) (subst t2 v t0); dands; eauto 3 with slow.
                apply differ_force_subst; auto.
              }

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; fold_terms; GC.

                pose proof (imp (nobnd (mk_nseq f0)) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd arg) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                repeat (allsimpl; cpx; GC).
                clear imp1; fold_terms.

                exists (mk_eapply (mk_nseq f0) arg) (mk_eapply (mk_nseq f0) t0); dands; eauto 3 with slow.

                apply differ_force_implies_differ_force_alpha.
                apply differ_force_oterm; simpl; tcsp.
                introv j; repndors; tcsp; ginv; constructor; auto.
                apply differ_force_refl; simpl; tcsp.
              }

            * SSSCase "NEApply".
              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp; exrepnd; subst.
              rw @wf_term_eq in wft1; rw @nt_wf_eapply_iff in wft1; exrepnd; allunfold @nobnd; ginv.

              inversion d as [?|?|?|? ? ? len1 nia imp1]; subst; clear d; GC;[].
              simpl in len1; cpx; simpl in imp1.

              pose proof (imp1 (nobnd (oterm (Can can1) bs1')) x) as d1; autodimp d1 hyp.
              pose proof (imp1 (nobnd b0) y) as d2; autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.
              fold_terms.
              allrw <- @wf_eapply_iff; repnd.
              apply eapply_wf_def_oterm_implies in comp2; exrepnd; ginv; fold_terms.
              destruct comp2 as [comp2|comp2]; exrepnd; subst; ginv; fold_terms.

              { apply differ_force_lam_implies in d3; exrepnd; subst; fold_terms.

                { repndors; exrepnd; subst.

                  + apply compute_step_eapply2_success in comp1; repnd; GC.
                    repndors; exrepnd; subst; ginv; allsimpl; GC.
                    allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                    applydup @differ_force_preserves_iscan in d4; auto.
                    autorewrite with slow in *.

                    { exists (subst b1 v0 b0)
                             (subst u1 v0 t0).
                      dands; eauto 3 with slow.
                      { apply eapply_lam_can_implies.
                        unfold computes_to_can; dands; eauto 3 with slow. }
                      apply differ_force_subst; auto.
                    }

                  + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                    apply differ_force_exception in d4; exrepnd; subst;[].

                    exists (mk_exception a0 e)
                           (mk_exception n1 e1).
                    dands; eauto 3 with slow.
                    apply implies_differ_force_alpha_exception; eauto 3 with slow.

                  + allsimpl; autorewrite with slow in *.
                    pose proof (ind1 b0 b0 []) as h; clear ind1.
                    repeat (autodimp h hyp); eauto 3 with slow.
                    pose proof (h t0 b a x f) as ih; clear h.
                    applydup @preserve_nt_wf_compute_step in comp1; auto.
                    repeat (autodimp ih hyp); eauto 3 with slow.
                    { apply hasvalue_like_eapply_lam_implies in hv; auto. }
                    { introv j; apply i; allrw in_app_iff; tcsp. }
                    exrepnd.

                    exists (mk_eapply (mk_lam v t) t1')
                           (mk_eapply (mk_lam v u1) t2').
                    dands; eauto 3 with slow.
                    { apply implies_eapply_red_aux; eauto 3 with slow. }
                    { apply implies_eapply_red_aux; eauto 3 with slow. }
                    { apply differ_force_alpha_mk_eapply; eauto 3 with slow.
                      apply differ_force_alpha_mk_lam; eauto 3 with slow. }
                }
              }

              { apply differ_force_nseq_implies in d3; exrepnd; subst; fold_terms.

                { repndors; exrepnd; subst.

                  + apply compute_step_eapply2_success in comp1; repnd; GC.
                    repndors; exrepnd; subst; ginv; allsimpl; GC;[].
                    allapply @differ_force_nat_implies; subst.

                    { exists (@mk_nat o (f0 n))
                             (@mk_nat o (f0 n)).
                      dands; eauto 3 with slow.
                      { eapply reduces_to_if_step; csunf; simpl; dcwf xx; simpl.
                        boolvar; try omega; auto.
                        rw @Znat.Nat2Z.id; auto. }
                      apply differ_force_alpha_refl; simpl; tcsp.
                    }

                  + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                    apply differ_force_exception in d4; exrepnd; subst;[].

                    exists (mk_exception a0 e)
                           (mk_exception n1 e1).
                    dands; eauto 3 with slow.
                    apply implies_differ_force_alpha_exception; eauto 3 with slow.

                  + allsimpl; autorewrite with slow in *.
                    pose proof (ind1 b0 b0 []) as h; clear ind1.
                    repeat (autodimp h hyp); eauto 3 with slow.
                    pose proof (h t0 b a x f) as ih; clear h.
                    applydup @preserve_nt_wf_compute_step in comp1; auto.
                    repeat (autodimp ih hyp); eauto 3 with slow.
                    { apply hasvalue_like_eapply_nseq_implies in hv; auto. }
                    exrepnd.

                    exists (mk_eapply (mk_nseq s) t1')
                           (mk_eapply (mk_nseq s) t2').
                    dands; eauto 3 with slow.
                    { apply implies_eapply_red_aux; eauto 3 with slow. }
                    { apply implies_eapply_red_aux; eauto 3 with slow. }
                    { apply differ_force_alpha_mk_eapply; eauto 3 with slow. }
                }
              }

(*            * SSSCase "NApseq".

              clear ind1.
              csunf comp; allsimpl.
              apply compute_step_apseq_success in comp; repndors; exrepnd; subst.

              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC; fold_terms.

              pose proof (imp (nobnd (mk_nat n0)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx; GC).
              clear imp1.
              fold_terms.

              exists (@mk_nat o (n n0)) (@mk_nat o (n n0)); dands; eauto 3 with slow.

              { apply reduces_to_if_step; csunf; simpl.
                rw @Znat.Nat2Z.id.
                boolvar; try omega; auto. }

              { apply differ_force_implies_differ_force_alpha.
                apply differ_force_oterm; simpl; tcsp. }*)

            * SSSCase "NFix".
              csunf comp; allsimpl.
              apply compute_step_fix_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can can1) bs1')) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).

              exists (mk_apply (oterm (Can can1) bs1') (mk_fix (oterm (Can can1) bs1')))
                     (mk_apply (oterm (Can can1) bs2) (mk_fix (oterm (Can can1) bs2)));
                dands; eauto 3 with slow.

              apply differ_force_implies_differ_force_alpha.
              apply differ_force_oterm; simpl; tcsp.
              introv j; repndors; tcsp; ginv; constructor; auto.
              apply differ_force_oterm; simpl; auto.
              introv j; repndors; tcsp; ginv; constructor; auto.

            * SSSCase "NSpread".
              csunf comp; allsimpl.
              apply compute_step_spread_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can NPair) [nobnd a0, nobnd b0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [va,vb] arg) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd a0) x) as d1.
              autodimp d1 hyp.
              pose proof (imp1 (nobnd b0) y) as d2.
              autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              exists (lsubst arg [(va,a0),(vb,b0)])
                     (lsubst t0 [(va,t2),(vb,t3)]); dands; eauto 3 with slow.
              apply differ_force_subst; auto.

            * SSSCase "NDsup".
              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can NSup) [nobnd a0, nobnd b0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [va,vb] arg) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd a0) x) as d1.
              autodimp d1 hyp.
              pose proof (imp1 (nobnd b0) y) as d2.
              autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              exists (lsubst arg [(va,a0),(vb,b0)])
                     (lsubst t0 [(va,t2),(vb,t3)]); dands; eauto 3 with slow.
              apply differ_force_subst; auto.

            * SSSCase "NDecide".
              csunf comp; allsimpl.
              apply compute_step_decide_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can can1) [nobnd d0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v1] t1) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (bterm [v2] t0) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd d0) x) as d1.
              autodimp d1 hyp.
              clear imp1.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              repndors; repnd; subst.

              { exists (lsubst t1 [(v1,d0)])
                       (lsubst t4 [(v1,t3)]);
                dands; eauto 3 with slow. }

              { exists (lsubst t0 [(v2,d0)])
                       (lsubst t5 [(v2,t3)]);
                dands; eauto 3 with slow. }

            * SSSCase "NCbv".
              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp; exrepnd; subst.
              inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

              { (* force case *)
                inversion d' as [|?|?|? ? ? len nia imp]; subst.
                applydup @alpha_eq_preserves_isprog in aeq;auto;[].
                eapply continuity2_2.alphaeq_preserves_hasvalue_like in hv;
                  [| |apply alpha_eq_subst_sp_force_nat_alpha_eq;auto];
                  [|allrw <- @wf_cbv_iff; repnd;
                    apply nt_wf_subst; eauto 2 with slow];[].

                apply wf_bound2_cbv in wft2; repnd.
                fold_terms.
                fold (sp_force_nat (oterm (Can can1) bs1') v z f') in wft1.
                apply wf_sp_force_nat in wft1; repnd.

                applydup @hasvalue_like_less in hv; eauto 3 with slow;[].

                repndors; exrepnd.

                - allunfold @computes_to_can; repnd.
                  apply reduces_to_if_isvalue_like in hv5; eauto 3 with slow;
                    unfold mk_integer in hv5; ginv;[].
                  allsimpl; cpx; GC; fold_terms.
                  unfold mk_zero, mk_nat in hv4.
                  apply reduces_to_if_isvalue_like in hv4; eauto 3 with slow; ginv.
                  fold_terms.

                  boolvar; tcsp; try (complete (allapply @hasvalue_like_vbot; tcsp));[].
                  pose proof (Wf_Z.Z_of_nat_complete_inf i1) as hi1;
                    autodimp hi1 hyp; exrepnd; subst; fold_terms.
                  exists (mk_apply f' (mk_nat n)) (mk_apply f' (mk_nat n)).
                  dands; eauto 3 with slow.

                  + unfsubst; simpl; allrw memvar_singleton.
                    allrw <- @beq_var_refl; fold_terms.
                    rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.
                    apply reduces_to_if_step; csunf; simpl.
                    dcwf h; simpl;[].
                    unfold compute_step_comp; simpl.
                    boolvar; tcsp; try omega.

                  + unfold bound2_cbv.
                    eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    unfold apply_bterm; simpl; fold_terms.
                    unflsubst; simpl.
                    allrw <- @beq_var_refl; fold_terms.
                    allrw memvar_singleton.
                    rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.
                    eapply reduces_to_if_split2;
                      [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].

                    match goal with
                      | [ |- context[mk_lam ?v ?t ] ] => remember (mk_lam v t) as xx; clear Heqxx
                    end.

                    boolvar; tcsp; try omega; GC.
                    pose proof (i (Z.of_nat n)) as h; autodimp h hyp.
                    rw Znat.Zabs2Nat.id in h.

                    apply reduces_to_if_step; csunf; simpl.
                    dcwf hh; simpl;[].
                    unfold compute_step_comp; simpl.
                    boolvar; tcsp; try omega.

                  + apply differ_force_implies_differ_force_alpha.
                    apply differ_force_refl; simpl; rw app_nil_r.
                    apply alphaeq_preserves_utokens in aeq; rw <- aeq; auto.

                - apply can_doesnt_raise_an_exception in hv1; sp.

                - apply can_doesnt_raise_an_exception in hv2; sp.
              }

              (* non force case *)

              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can can1) bs1')) x0) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v] x) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              exists (lsubst x [(v,oterm (Can can1) bs1')])
                     (lsubst t0 [(v,oterm (Can can1) bs2)]);
                dands; eauto 3 with slow.
              apply differ_force_subst; auto.

            * SSSCase "NSleep".
              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms.

              pose proof (imp (nobnd (mk_integer z)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.

            * SSSCase "NTUni".
              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms.

              pose proof (imp (nobnd (mk_nat n)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_uni o n) (@mk_uni o n); dands; eauto 3 with slow.
              apply reduces_to_if_step; csunf; simpl.
              unfold compute_step_tuni; simpl; boolvar; tcsp; try omega.
              rw Znat.Nat2Z.id; auto.

            * SSSCase "NMinus".
              csunf comp; allsimpl.
              apply compute_step_minus_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms.

              pose proof (imp (nobnd (mk_integer z)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_integer o (- z)) (@mk_integer o (- z)); dands; eauto 3 with slow.

            * SSSCase "NFresh".
              csunf comp; allsimpl; ginv.

            * SSSCase "NTryCatch".
              csunf comp; allsimpl.
              apply compute_step_try_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) x0) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd a0) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (bterm [v] x) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              exists (mk_atom_eq a0 a0 (oterm (Can can1) bs1') mk_bot)
                     (mk_atom_eq t0 t0 (oterm (Can can1) bs2) mk_bot);
                dands; eauto 3 with slow.

              apply differ_force_implies_differ_force_alpha.
              apply differ_force_oterm; simpl; tcsp.
              introv j; repndors; tcsp; ginv; constructor; eauto 2 with slow.

            * SSSCase "NParallel".
              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms.
              destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) b2) as d1.
              autodimp d1 hyp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              fold_terms.

              exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.
              apply differ_force_implies_differ_force_alpha.
              apply differ_force_refl; simpl; tcsp.

            * SSSCase "NCompOp".
              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; subst; allsimpl;[|idtac|].

              { apply compute_step_compop_success_can_can in comp1;
                exrepnd; subst; allsimpl; ginv; GC.

                repndors; exrepnd; subst; allrw @get_param_from_cop_some; subst;
                allsimpl; fold_terms; allrw <- @pk2term_eq.

                - inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                  cpx; allsimpl; fold_terms.

                  pose proof (imp (nobnd (mk_integer n1)) x) as d1.
                  autodimp d1 hyp.
                  pose proof (imp (nobnd (mk_integer n2)) y) as d2.
                  autodimp d2 hyp.
                  pose proof (imp (nobnd t3) z) as d3.
                  autodimp d3 hyp.
                  pose proof (imp (nobnd t4) u) as d4.
                  autodimp d4 hyp.
                  clear imp.

                  inversion d1 as [? ? ? d5]; subst; clear d1.
                  inversion d2 as [? ? ? d6]; subst; clear d2.
                  inversion d3 as [? ? ? d7]; subst; clear d3.
                  inversion d4 as [? ? ? d8]; subst; clear d4.

                  inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].
                  inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].
                  repeat (allsimpl; cpx).
                  clear imp1 imp2.
                  fold_terms.

                  exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                         (if Z_lt_le_dec n1 n2 then t5 else t6);
                    dands; eauto 3 with slow.
                  boolvar; eauto 3 with slow.

                - inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                  cpx; allsimpl; fold_terms.

                  pose proof (imp (nobnd (pk2term pk1)) x) as d1.
                  autodimp d1 hyp.
                  pose proof (imp (nobnd (pk2term pk2)) y) as d2.
                  autodimp d2 hyp.
                  pose proof (imp (nobnd t3) z) as d3.
                  autodimp d3 hyp.
                  pose proof (imp (nobnd t4) u) as d4.
                  autodimp d4 hyp.
                  clear imp.

                  inversion d1 as [? ? ? d5]; subst; clear d1.
                  inversion d2 as [? ? ? d6]; subst; clear d2.
                  inversion d3 as [? ? ? d7]; subst; clear d3.
                  inversion d4 as [? ? ? d8]; subst; clear d4.

                  allrw @pk2term_eq.
                  inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].
                  inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].
                  repeat (allsimpl; cpx).
                  clear imp1 imp2.
                  fold_terms.
                  allrw <- @pk2term_eq.

                  exists (if param_kind_deq pk1 pk2 then t3 else t4)
                         (if param_kind_deq pk1 pk2 then t5 else t6);
                    dands; eauto 3 with slow.
                  { apply reduces_to_if_step; csunf; simpl;
                    allrw @pk2term_eq; allsimpl.
                    dcwf h; allsimpl.
                    unfold compute_step_comp; allsimpl.
                    allrw @get_param_from_cop_pk2can; auto. }

                  boolvar; eauto 3 with slow.
              }

              { apply if_hasvalue_like_ncompop_can1 in hv.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                destruct bs2 as [|b1 bs2];allsimpl;ginv;[].
                destruct bs2 as [|b2 bs2];allsimpl;ginv;[].

                pose proof (imp (nobnd (oterm (Can can1) bs1')) b1) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) b2) as d2.
                autodimp d2 hyp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                pose proof (ind1 t t []) as h; clear ind1.
                repeat (autodimp h hyp);eauto 3 with slow;[].
                pose proof (h t0 b a t' f) as q; clear h.

                allrw @wf_term_ncompop_iff; exrepnd; allsimpl; ginv.
                allsimpl.

                pose proof (imp (nobnd c0) (nobnd c1)) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd d) (nobnd d0)) as d2.
                autodimp d2 hyp.

                inversion d1 as [? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? d6]; subst; clear d2.

                repeat (autodimp q hyp).
                { introv j; apply i; simpl; repeat (rw in_app_iff); tcsp. }
                exrepnd.

                assert (co_wf_def c can1 bs0) as co2.
                { eapply co_wf_def_len_implies;[|exact comp0];auto. }

                exists (mk_compop c (oterm (Can can1) bs1') t1' c0 d)
                       (mk_compop c (oterm (Can can1) bs0) t2' c1 d0).
                dands; eauto 3 with slow.

                { eapply reduce_to_prinargs_comp2;
                  [apply reduces_to_symm
                  |apply co_wf_def_implies_iswfpk; auto
                  |auto]. }

                { eapply reduce_to_prinargs_comp2;
                  [apply reduces_to_symm
                  |apply co_wf_def_implies_iswfpk; auto
                  |auto]. }

                { apply differ_force_alpha_oterm; simpl; tcsp.
                  apply implies_differ_force_bterms_alpha; simpl; auto.
                  introv j; repndors; tcsp; ginv;
                  apply implies_differ_force_b_alpha; eauto 3 with slow. }
              }

              { allunfold @nobnd.
                allrw @wf_term_ncompop_iff; exrepnd; allsimpl; ginv.
                allsimpl.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd b0) y) as d2.
                autodimp d2 hyp.
                pose proof (imp (nobnd c0) z) as d3.
                autodimp d3 hyp.
                pose proof (imp (nobnd d0) u) as d4.
                autodimp d4 hyp.
                clear imp.

                inversion d1 as [? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? d6]; subst; clear d2.
                inversion d3 as [? ? ? d7]; subst; clear d3.
                inversion d4 as [? ? ? d8]; subst; clear d4.

                inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].

                apply isexc_implies2 in comp1; exrepnd; subst;[].
                inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].

                assert (co_wf_def c can1 bs2) as co2.
                { eapply co_wf_def_len_implies;[|exact comp0];auto. }

                exists (oterm Exc l)
                       (oterm Exc bs0).
                dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h. }
              }

            * SSSCase "NArithOp".
              apply compute_step_narithop_can1_success in comp; repnd.
              allunfold @nobnd.
              allrw @wf_term_narithop_iff; exrepnd; allsimpl; ginv.
              repndors; exrepnd; subst; allsimpl;ginv;[|idtac|].

              { apply compute_step_arithop_success_can_can in comp1;
                exrepnd; subst; allsimpl; ginv; GC.
                allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; fold_terms.

                pose proof (imp (nobnd (mk_integer n1)) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd (mk_integer n2)) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                inversion d4 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d4;[].
                repeat (allsimpl; cpx).
                clear imp1 imp2.
                fold_terms.

                exists (@mk_integer o (get_arith_op a0 n1 n2))
                       (@mk_integer o (get_arith_op a0 n1 n2));
                  dands; eauto 3 with slow.
              }

              { apply if_hasvalue_like_arithop_can1 in hv.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                pose proof (ind1 t t []) as h; clear ind1.
                repeat (autodimp h hyp);eauto 3 with slow;[].
                allrw @wf_term_narithop_iff; exrepnd; allsimpl; ginv.
                pose proof (h b0 b a t' f) as q; clear h.
                repeat (autodimp q hyp).
                { introv j; apply i; simpl; repeat (rw in_app_iff); tcsp. }
                exrepnd.

                assert (ca_wf_def can1 bs2) as co2.
                { eapply ca_wf_def_len_implies;[|exact comp0];auto. }

                exists (mk_arithop a0 (oterm (Can can1) bs1') t1')
                       (mk_arithop a0 (oterm (Can can1) bs2) t2').
                dands; eauto 3 with slow.

                { eapply reduce_to_prinargs_arith2;
                  [apply reduces_to_symm
                  |
                  |auto]; eauto 3 with slow. }

                { eapply reduce_to_prinargs_arith2;
                  [apply reduces_to_symm
                  |
                  |auto]; eauto 3 with slow. }

                { apply differ_force_alpha_oterm; simpl; tcsp.
                  apply implies_differ_force_bterms_alpha; simpl; auto.
                  introv j; repndors; tcsp; ginv;
                  apply implies_differ_force_b_alpha; eauto 3 with slow. }
              }

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                apply isexc_implies2 in comp1; exrepnd; subst;[].
                inversion d4 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d4;[].

                assert (ca_wf_def can1 bs2) as co2.
                { eapply ca_wf_def_len_implies;[|exact comp0];auto. }

                exists (oterm Exc l)
                       (oterm Exc bs0).
                dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h. }
              }

            * SSSCase "NCanTest".
              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd arg2nt) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (nobnd arg3nt) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              exists (if canonical_form_test_for c can1 then arg2nt else arg3nt)
                     (if canonical_form_test_for c can1 then t0 else t3);
                dands; eauto 3 with slow.
              remember (canonical_form_test_for c can1) as cc; destruct cc; eauto 3 with slow.

          + SSCase "NCan".
            rw @compute_step_ncan_ncan in comp.
            remember (compute_step lib (oterm (NCan ncan1) bs1')) as cs;
              symmetry in Heqcs; destruct cs; ginv;[].
            apply if_hasvalue_like_ncan_primarg in hv.
            allsimpl.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              fold (sp_force_nat (oterm (NCan ncan1) bs1') x z f') in wft1.
              fold (sp_force_nat n x z f').
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.

              pose proof (ind1 (oterm (NCan ncan1) bs1') (oterm (NCan ncan1) bs1') []) as h; clear ind1.
              repeat (autodimp h hyp);eauto 3 with slow;[].
              pose proof (h arg2 b a n f) as q; clear h.
              repeat (autodimp q hyp).
              { introv j; allsimpl; allrw app_nil_r; apply i; allrw in_app_iff; sp. }
              exrepnd.

              exists (sp_force_nat t1' x z f') (bound2_cbv t2' x z b f' a).
              dands; eauto 3 with slow.

              { eapply reduces_to_prinarg;exact q0. }
              { eapply reduces_to_prinarg;exact q2. }
              { apply differ_forces_alpha_nat; auto. }
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

            pose proof (imp (nobnd (oterm (NCan ncan1) bs1')) b2) as d1.
            repeat (autodimp d1 hyp).

            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind1 (oterm (NCan ncan1) bs1') (oterm (NCan ncan1) bs1') []) as h; clear ind1.
            repeat (autodimp h hyp);eauto 3 with slow;[].

            allrw @wf_oterm_iff; allsimpl; repnd.
            pose proof (wft1 (nobnd (oterm (NCan ncan1) bs1'))) as w1; autodimp w1 hyp.
            pose proof (wft2 (nobnd t2)) as w2; autodimp w2 hyp.
            allrw @wf_bterm_iff.

            pose proof (h t2 b a n f) as q; clear h.
            repeat (autodimp q hyp).
            { introv j; apply i; allrw in_app_iff; sp. }
            exrepnd.

            exists (oterm (NCan ncan) (nobnd t1' :: bs1))
                   (oterm (NCan ncan) (nobnd t2' :: bs2)).
            dands; eauto 3 with slow.

            { eapply reduces_to_prinarg;exact q0. }
            { eapply reduces_to_prinarg;exact q2. }
            { apply differ_force_alpha_oterm; simpl; tcsp.
              apply implies_differ_force_bterms_alpha; simpl; auto.
              introv j; repndors; tcsp; ginv; eauto 3 with slow.
              - apply implies_differ_force_b_alpha; auto.
              - pose proof (imp b1 b2) as h; autodimp h hyp; eauto 3 with slow. }

          + SSCase "Exc".
            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              repndors; repnd; ginv; subst;[].
              fold (sp_force_nat (oterm Exc bs1') x z f') in wft1.
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.
              clear ind1.

              inversion d' as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d'.
              exists (oterm Exc bs1') (oterm Exc bs2); dands; eauto 3 with slow.
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx;[].

            pose proof (imp (nobnd (oterm Exc bs1')) b2) as d1.
            autodimp d1 hyp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].

            repndors; exrepnd; subst; allsimpl; fold_terms; cpx; allsimpl; fold_terms.

            { pose proof (imp1 (nobnd a') x0) as d1.
              autodimp d1 hyp.
              pose proof (imp1 (nobnd e) y0) as d2.
              autodimp d2 hyp.
              clear imp1.
              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              pose proof (imp (nobnd a0) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v] b0) y) as d2.
              autodimp d2 hyp.
              clear imp.
              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              allrw <- @wf_try_iff; repnd.
              allrw @wf_exception_iff; repnd.

              exists (mk_atom_eq a0 a' (subst b0 v e) (mk_exception a' e))
                     (mk_atom_eq t3 t2 (subst t4 v t0) (mk_exception t2 t0)).
              dands; eauto 3 with slow;[].

              apply differ_force_alpha_oterm; simpl; tcsp.
              apply implies_differ_force_bterms_alpha; simpl; auto.
              introv j; repndors; tcsp; ginv;
              apply implies_differ_force_b_alpha; eauto 3 with slow.

              { apply differ_force_subst; auto. }
              { apply differ_force_alpha_oterm; simpl; tcsp.
                apply implies_differ_force_bterms_alpha; simpl; auto.
                introv j; repndors; tcsp; ginv;
                apply implies_differ_force_b_alpha; eauto 3 with slow. }
            }

            { exists (oterm Exc bs1') (oterm Exc bs3).
              dands; eauto 3 with slow.
              apply reduces_to_if_step.
              csunf; simpl.
              rw @compute_step_catch_if_diff; auto.
            }

          + SSCase "Abs".
            rw @compute_step_ncan_abs in comp.
            remember (compute_step_lib lib abs1 bs1') as cs;
              symmetry in Heqcs; destruct cs; ginv;[].
            apply if_hasvalue_like_ncan_primarg in hv.
            allsimpl.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              fold (sp_force_nat (oterm (Abs abs1) bs1') x z f') in wft1.
              fold (sp_force_nat n x z f').
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.

              pose proof (ind1 (oterm (Abs abs1) bs1') (oterm (Abs abs1) bs1') []) as h; clear ind1.
              repeat (autodimp h hyp);eauto 3 with slow;[].
              pose proof (h arg2 b a n f) as q; clear h.
              repeat (autodimp q hyp).
              { introv j; allsimpl; allrw app_nil_r; apply i; allrw in_app_iff; sp. }
              exrepnd.

              exists (sp_force_nat t1' x z f') (bound2_cbv t2' x z b f' a).
              dands; eauto 3 with slow.

              { eapply reduces_to_prinarg;exact q0. }
              { eapply reduces_to_prinarg;exact q2. }
              { apply differ_forces_alpha_nat; auto. }
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

            pose proof (imp (nobnd (oterm (Abs abs1) bs1')) b2) as d1.
            repeat (autodimp d1 hyp).

            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind1 (oterm (Abs abs1) bs1') (oterm (Abs abs1) bs1') []) as h; clear ind1.
            repeat (autodimp h hyp);eauto 3 with slow;[].

            allrw @wf_oterm_iff; allsimpl; repnd.
            pose proof (wft1 (nobnd (oterm (Abs abs1) bs1'))) as w1; autodimp w1 hyp.
            pose proof (wft2 (nobnd t2)) as w2; autodimp w2 hyp.
            allrw @wf_bterm_iff.

            pose proof (h t2 b a n f) as q; clear h.
            repeat (autodimp q hyp).
            { introv j; apply i; allrw in_app_iff; sp. }
            exrepnd.

            exists (oterm (NCan ncan) (nobnd t1' :: bs1))
                   (oterm (NCan ncan) (nobnd t2' :: bs2)).
            dands; eauto 3 with slow.

            { eapply reduces_to_prinarg;exact q0. }
            { eapply reduces_to_prinarg;exact q2. }
            { apply differ_force_alpha_oterm; simpl; tcsp.
              apply implies_differ_force_bterms_alpha; simpl; auto.
              introv j; repndors; tcsp; ginv; eauto 3 with slow.
              - apply implies_differ_force_b_alpha; auto.
              - pose proof (imp b1 b2) as h; autodimp h hyp; eauto 3 with slow. }
      }

      { (* fresh case *)

        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; repnd; subst; allsimpl.

        inversion d as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d;[].
        allsimpl; cpx; allsimpl.
        pose proof (imp1 (bterm [n] t1) x) as d1.
        autodimp d1 hyp.
        clear imp1.
        inversion d1 as [? ? ? d2]; subst; clear d1.
        fold_terms.

        repndors; exrepnd; subst; allsimpl.

        - apply not_hasvalue_like_fresh in hv; sp.

        - pose proof (differ_force_isvalue_like b a f t1 t2) as h.
          repeat (autodimp h hyp).
          repnd.
          exists (pushdown_fresh n t1) (pushdown_fresh n t2).
          dands; eauto 3 with slow.
          apply reduces_to_if_step.
          apply compute_step_fresh_if_isvalue_like; auto.

        - (* one reduction step under fresh *)
          pose proof (fresh_atom o (a :: get_utokens t1
                                      ++ get_utokens t2
                                      ++ get_utokens f)) as fa; exrepnd.
          allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a'.

          pose proof (ind1 t1 (subst t1 n (mk_utoken a')) [n]) as q; clear ind1.
          repeat (autodimp q hyp);[rw @simple_osize_subst;eauto 3 with slow|];[].
          allrw @wf_fresh_iff.
          applydup @compute_step_preserves_wf in comp2; auto;
          [|apply wf_term_subst; eauto 3 with slow];[].
          pose proof (hasvalue_like_fresh_implies
                        lib (get_fresh_atom t1) n
                        (subst_utokens x [(get_fresh_atom t1, mk_var n)])) as hvf.
          repeat (autodimp hvf hyp).
          { apply wf_subst_utokens; eauto 3 with slow. }
          { introv j; apply get_utokens_subst_utokens_subset in j; allsimpl.
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r.
            allrw in_remove; sp. }

          assert (!LIn n (free_vars x)) as ninx.
          { apply compute_step_preserves in comp2; repnd; eauto 4 with slow;[].
            introv j; apply subvars_eq in comp3; apply comp3 in j.
            apply eqset_free_vars_disjoint in j; allsimpl; boolvar; allsimpl;
            allrw app_nil_r; allrw in_remove_nvars; allsimpl; tcsp. }

          eapply continuity2_2.alphaeq_preserves_hasvalue_like in hvf;
            [| |apply simple_subst_subst_utokens_aeq; auto];
            [|apply nt_wf_subst; eauto 3 with slow;[];
              apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow];[].

          pose proof (compute_step_subst_utoken
                        lib t1 x
                        [(n,mk_utoken (get_fresh_atom t1))]) as comp'.
          repeat (autodimp comp' hyp); eauto 3 with slow.
          { apply nr_ut_sub_cons; auto; introv j; apply get_fresh_atom_prop. }
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; apply get_fresh_atom_prop. }
          exrepnd; allsimpl.
          pose proof (comp'0 [(n,mk_utoken a')]) as comp''; allsimpl; clear comp'0.
          repeat (autodimp comp'' hyp).
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; auto. }
          exrepnd.
          allrw @fold_subst.

          pose proof (get_fresh_atom_prop t1) as gfpat1.
          remember (get_fresh_atom t1) as at1.
          clear Heqat1.
          dup comp'1 as aeq1.
          apply (alpha_eq_subst_utokens_same _ _ [(at1,mk_var n)]) in aeq1.
          dup aeq1 as aeq'.
          apply alpha_eq_sym in aeq1.
          eapply alpha_eq_trans in aeq1;
            [|apply alpha_eq_sym; apply simple_alphaeq_subst_utokens_subst;
              introv j; apply comp'4 in j; sp].
          dup aeq1 as aeq''.
          apply (lsubst_alpha_congr2 _ _ [(n,mk_utoken a')]) in aeq1.
          allrw @fold_subst.
          dup aeq1 as aeq'''.
          apply alpha_eq_sym in aeq1; eapply alpha_eq_trans in aeq1;
          [|apply alpha_eq_sym; apply simple_subst_subst_utokens_aeq_ren; auto].
          assert (alpha_eq s (ren_utokens [(at1,a')] x)) as aeq2 by (eauto 3 with slow).

          pose proof (q (subst t2 n (mk_utoken a')) b a s f) as ih; clear q.
          repeat (autodimp ih hyp); try (apply wf_term_subst; eauto 3 with slow).
          { repeat unfsubst.
            apply differ_force_lsubst_aux; simpl; auto.
            apply dfsub_cons; auto;[].
            apply differ_force_oterm; simpl; tcsp. }
          { eapply continuity2_2.alphaeq_preserves_hasvalue_like;[|apply alpha_eq_sym;exact aeq2|];eauto 3 with slow;
            apply continuity2_2.hasvalue_like_ren_utokens; simpl; eauto 3 with slow.
            apply disjoint_singleton_l; rw in_remove; introv j; repnd.
            apply compute_step_preserves_utokens in comp2; eauto 3 with slow; apply comp2 in j.
            apply get_utokens_subst in j; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp. }
          { introv j; unfsubst in j.
            allrw app_nil_r.
            rw (get_ints_lsubst_aux_nr_ut t1 [(n, mk_utoken a')] mk_axiom) in j; simpl; eauto 3 with slow. }
          exrepnd.

          applydup @reduces_to_fresh2 in ih2; auto.
          exrepnd.

          applydup @compute_step_preserves_wf in comp''1 as wf1; eauto 4 with slow;[].

          eapply reduces_to_alpha in ih0;
            [| |eapply alpha_eq_trans;[exact comp''0|exact aeq'''] ];
            eauto 3 with slow;[].
          exrepnd.
          applydup @reduces_to_fresh2 in ih0; auto;
          [|apply wf_subst_utokens; eauto 3 with slow
           |introv j; apply get_utokens_subst_utokens_subset in j; allsimpl;
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r;
            allrw in_remove; repnd;
            apply compute_step_preserves_utokens in comp2; eauto 3 with slow; apply comp2 in j;
            apply get_utokens_subst in j; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp].
          exrepnd.

          exists (mk_fresh n z0)
                 (mk_fresh n z); dands; eauto 3 with slow.
          eapply differ_force_alpha_alpha_eq1;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih7|].
          eapply differ_force_alpha_alpha_eq1;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_subst_utokens_same;exact ih5|].
          eapply differ_force_alpha_alpha_eq2;
            [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih4|].
          apply differ_force_alpha_mk_fresh.

          apply differ_force_alpha_subst_utokens; simpl; tcsp;
          apply disjoint_singleton_r; auto.
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.

      inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].

      exists (oterm Exc bs1) (oterm Exc bs2); dands; eauto 3 with slow.

    + SCase "Abs".
      csunf comp; allsimpl.

      inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].

      pose proof (differ_force_bterms_implies_eq_map_num_bvars b a f bs1 bs2) as e.
      autodimp e hyp.
      { unfold differ_force_bterms, br_bterms, br_list; dands; auto. }
      apply compute_step_lib_success in comp; exrepnd; subst.
      exists (mk_instance vars bs1 rhs)
             (mk_instance vars bs2 rhs).
      dands; eauto 3 with slow.
      { apply reduces_to_if_step; csunf; simpl.
        eapply compute_step_lib_success_change_bs;[|exact comp0]; auto. }
      dup comp0 as fe.
      eapply found_entry_change_bs in fe;[|exact e].
      applydup @found_entry_implies_matching_entry in comp0.
      applydup @found_entry_implies_matching_entry in fe.
      apply differ_force_mk_instance; auto;
      try (complete (allunfold @matching_entry; sp));
      try (complete (allunfold @correct_abs; sp)).
      unfold differ_force_bterms, br_bterms, br_list; sp.
Qed.

Lemma reduces_to_nat_differ_force {o} :
  forall lib (t1 t2 : @NTerm o) k
         (comp : reduces_to lib t1 (mk_nat k))
         b a f,
    isprog f
    -> wf_term t1
    -> wf_term t2
    -> !LIn a (get_utokens f)
    -> differ_force b a f t1 t2
    -> (forall z,
          LIn z (get_ints_from_computation lib t1 (mk_nat k) comp)
          -> Z.abs_nat z < b)
    -> reduces_to lib t2 (mk_nat k).
Proof.
  introv ispf w1 w2 niaf d i.
  unfold reduces_to in comp; exrepnd.
  unfold get_ints_from_computation in i.
  revert dependent t1.
  revert dependent t2.
  induction k0 as [n ind] using comp_ind_type; introv w2 w1 d i.
  destruct n as [|n]; allsimpl.

  - rw @reduces_in_atmost_k_steps_0 in comp0; subst.
    inversion d as [|?|?|? ? ? len nia imp]; subst; clear d.
    allsimpl; cpx; eauto 3 with slow.

  - remember (implies_reduces_in_atmost_k_steps_S lib t1 (mk_nat k) n comp0) as s.
    exrepnd.
    clear Heqs comp0.

    pose proof (computation_step_differ_force lib t1 t2 b a u f) as h.
    repeat (autodimp h hyp).
    { unfold hasvalue_like; exists (@mk_nat o k); dands; eauto 3 with slow. }
    { introv j; apply i; rw in_app_iff; sp. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to lib n u t1' (mk_nat k)) as h'.
    repeat (autodimp h' hyp); eauto 3 with slow.
    exrepnd.

    unfold differ_force_alpha in h1; exrepnd.

    applydup @compute_step_preserves_wf in s1;auto;[].
    applydup @reduces_to_preserves_wf in h0;auto;[].
    applydup @reduces_to_preserves_wf in h2;auto;[].
    applydup @alphaeq_preserves_wf_term in h4;auto;[].
    applydup @alphaeq_preserves_wf_term in h3;auto;[].

    pose proof (reduces_in_atmost_k_steps_alpha lib t1' u1) as h''.
    repeat (autodimp h'' hyp); eauto 3 with slow;[].
    pose proof (h'' k' (mk_nat k)) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.
    inversion h'''0 as [|?|? ? ? ? x]; subst; allsimpl; cpx;
    clear x h'''0;[].
    fold_terms.

    pose proof (ind k') as h.
    autodimp h hyp;[omega|].

    pose proof (h u2) as q; autodimp q hyp.
    pose proof (q u1 h'''1) as r; clear q.
    repeat (autodimp r hyp).

    { introv j.
      apply i; rw in_app_iff; right.
      pose proof (get_ints_from_red_atmost_if_reduces_to
                    lib n k' u t1' (mk_nat k) z s0 h'0) as hh.
      repeat (autodimp hh hyp); eauto 3 with slow.
      erewrite @get_ints_from_red_atmost_alpha_eq; eauto 3 with slow. }

    pose proof (reduces_to_steps_alpha lib u2 t2' (mk_nat k)) as q.
    repeat (autodimp q hyp); eauto 2 with slow.
    exrepnd.
    allapply @alpha_eq_mk_nat; subst.
    eapply reduces_to_trans; eauto.
Qed.

Lemma reduces_toc_nat_differ_force {o} :
  forall lib (t1 t2 : @CTerm o) k
         (comp : computes_to_valc lib t1 (mkc_nat k))
         b a f,
    !LIn a (getc_utokens f)
    -> differ_force b a (get_cterm f) (get_cterm t1) (get_cterm t2)
    -> (forall z,
          LIn z (get_ints_from_computes_to_valc lib t1 (mkc_nat k) comp)
          -> Z.abs_nat z < b)
    -> computes_to_valc lib t2 (mkc_nat k).
Proof.
  introv niaf d imp.
  destruct_cterms; allsimpl.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; eauto 3 with slow.
  eapply reduces_to_nat_differ_force;
    [|idtac|idtac|idtac|exact d|]; eauto 3 with slow.
Qed.

Lemma spM_cond {o} :
  forall lib (F f : @CTerm o),
    member lib F (mkc_fun nat2nat mkc_tnat)
    -> member lib f nat2nat
    -> {n : nat
        & equality lib
                   (mkc_apply2 (spM_c F) (mkc_nat n) f)
                   (mkc_apply F f)
                   (mkc_bunion mkc_tnat mkc_unit) }.
Proof.
  introv mF mf.

  (* Do we want to constrain the f? *)

  apply equality_in_fun in mF; repnd.
  clear mF0 mF1.
  applydup mF in mf.
  dup mf0 as ma; apply equality_refl in ma.
  apply equality_in_tnat in mf0.
  apply equality_of_nat_imp_tt in mf0.
  unfold equality_of_nat_tt in mf0; exrepnd; GC.

  pose proof (equality_lam_force_nat_c_in_nat2nat lib nvarx nvarz f mf) as q.
  applydup mF in q.
  apply equality_in_tnat in q0.
  apply equality_of_nat_imp_tt in q0.
  unfold equality_of_nat_tt in q0; exrepnd; spcast.
  computes_to_eqval.
  allapply @eq_mkc_nat_implies; subst; GC.

  pose proof (exists_bigger_than_list_Z
                (get_ints_from_computes_to_valc
                   lib
                   (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                   (mkc_nat k)
                   q1)) as h; exrepnd.

  exists n.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_apply2_spM_c
    |].

  apply equality_in_disjoint_bunion; eauto 3 with slow.
  dands; eauto 3 with slow.
  left.

  rw @test_c_eq.

  destruct (fresh_atom o (getc_utokens F ++ getc_utokens f)) as [a nia].
  allrw in_app_iff; allrw not_over_or; repnd.

  assert (equality
            lib
            (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f))
            (mkc_apply F f)
            (mkc_tnat)) as comp;
    [|pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f) a) as h;
       repeat (autodimp h hyp);
       [destruct_cterms;allsimpl;
        allunfold @getcv_utokens; allunfold @getc_utokens;
        allsimpl; allrw app_nil_r;
        allrw in_app_iff; complete sp
       |exists (@mkc_nat o k); dands; spcast; tcsp;
        allrw @substc_test_try2_cv;
        apply equality_in_tnat in comp;
        apply equality_of_nat_imp_tt in comp;
        unfold equality_of_nat_tt in comp; exrepnd; auto;
        computes_to_eqval; complete ginv
       |spcast; allrw @substc_test_try2_cv;
        eapply equality_respects_cequivc_left;[apply cequivc_sym;exact h|];
        complete auto
       ]
    ];[].

  allrw @substc_test_try2_cv.

  assert (equality
            lib
            (mkc_apply F (bound2_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
            (mkc_apply F f)
            mkc_tnat) as equ;
    [|apply equality_in_tnat in equ;
       unfold equality_of_nat in equ; exrepnd; spcast;
       eapply equality_respects_cequivc_left;
       [apply cequivc_sym;
         apply computes_to_valc_implies_cequivc;
         eapply computes_to_valc_mkc_try;[exact equ1|];
         apply computes_to_pkc_refl;
         complete (apply mkc_utoken_eq_pk2termc)
       |eapply equality_respects_cequivc_right;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact equ0|];
         eauto 3 with slow
       ]
    ].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
      apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequiv_bound2_c_cbv]
    |].

  apply equality_in_tnat.
  exists k; dands; spcast; auto;[].

  pose proof (reduces_toc_nat_differ_force
                lib
                (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                k q1 n a f) as h.
  repeat (autodimp h hyp).

  allrw @get_cterm_apply; simpl.
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow.
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow.
  apply differ_force_nat; auto.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
