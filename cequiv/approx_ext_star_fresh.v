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


Require Import approx_ext_star0.


Lemma isprog_vars_iff_isprogram_bt {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t <=> isprogram_bt (bterm vs t).
Proof.
  introv.
  rw @isprog_vars_eq.
  unfold isprogram_bt; simpl.
  rw @bt_wf_iff.
  rw @closed_bt_bterm; sp.
Qed.

Lemma isprog_vars_implies_isprogram_bt {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> isprogram_bt (bterm vs t).
Proof.
  introv isp.
  apply isprog_vars_iff_isprogram_bt; auto.
Qed.
Hint Resolve isprog_vars_implies_isprogram_bt : slow.

Lemma alpha_eq_bterm_implies_eq_length {o} :
  forall vs1 vs2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm vs1 t1) (bterm vs2 t2)
    -> length vs1 = length vs2.
Proof.
  introv aeq.
  inversion aeq; subst; auto.
Qed.

Lemma isprogram_lsubst_aux_implies {o} :
  forall (t : @NTerm o) sub,
    disjoint_bv_sub t sub
    -> isprogram (lsubst_aux t sub)
    -> isprogram_bt (bterm (dom_sub sub) t).
Proof.
  introv d isp.
  apply isprog_vars_iff_isprogram_bt.
  apply isprog_vars_eq.
  destruct isp as [c w].
  apply lsubst_aux_nt_wf in w; dands; auto.
  rw subvars_prop; introv i.
  unfold closed in c.
  rw <- null_iff_nil in c.
  unfold null in c.
  destruct (in_deq _ deq_nvar x (dom_sub sub)) as [j|j]; auto.
  provefalse.
  pose proof (c x) as h; destruct h.
  pose proof (eqvars_free_vars_disjoint_aux2 t sub d) as h; auto.
  rw eqvars_prop in h; apply h; clear h.
  rw in_app_iff; rw in_remove_nvars; sp.
Qed.

Lemma isprogram_lsubst_implies {o} :
  forall (t : @NTerm o) sub,
    isprogram (lsubst t sub)
    -> isprogram_bt (bterm (dom_sub sub) t).
Proof.
  introv isp.
  pose proof (unfold_lsubst sub t) as h; exrepnd; rw h0 in isp.
  apply isprogram_lsubst_aux_implies in isp; auto.
  - allunfold @isprogram_bt.
    allunfold @closed_bt; allsimpl.
    applydup @alphaeq_preserves_free_vars in h1 as fv.
    rw fv; repnd; dands; auto.
    allrw @bt_wf_iff.
    apply alphaeq_preserves_wf in h1; apply h1; auto.
  - unfold disjoint_bv_sub, sub_range_sat; introv i j k.
    apply h2 in k; destruct k.
    apply in_sub_free_vars_iff.
    exists v t0; dands; auto.
Qed.

Lemma isprogram_subst_implies {o} :
    forall (t : @NTerm o) (v : NVar) (a : NTerm),
      isprogram (subst t v a)
      -> isprogram_bt (bterm [v] t).
Proof.
  introv isp.
  apply isprogram_lsubst_implies in isp; allsimpl; auto.
Qed.

Definition get_op {o} (t : @NTerm o) : Opid :=
  match t with
    | vterm _ => Exc
    | sterm _ => Exc
    | oterm op _ => op
  end.

Inductive same_value_like {o} lib : @NTerm o -> @NTerm o -> Type :=
| svl_c : forall c bs1 bs2, same_value_like lib (oterm (Can c) bs1) (oterm (Can c) bs2)
| svl_e : forall bs1 bs2, same_value_like lib (oterm Exc bs1) (oterm Exc bs2)
| svl_s :
    forall f1 f2,
      (*(forall n, alpha_eq (f1 n) (f2 n))*)
      (forall n, approx_ext_star lib (f1 n) (f2 n))
      -> same_value_like lib (sterm f1) (sterm f2).
Hint Constructors same_value_like.

Lemma approx_ext_starbts_nil {o} :
  forall lib (op : @Opid o), approx_ext_starbts lib op [] [].
Proof.
  introv; unfold approx_ext_starbts, lblift_sub; simpl; dands; tcsp.
Qed.
Hint Resolve approx_ext_starbts_nil : slow.

Lemma howe_lemma2_implies_same_value_like {o} :
  forall lib (t u : @NTerm o),
    isprogram t
    -> isprogram u
    -> isvalue_like t
    -> approx_ext_star lib t u
    -> {v : NTerm
        & same_value_like lib t v
        # approx_ext_starbts lib (get_op t) (get_bterms t) (get_bterms v)
        # reduces_to lib u v}.
Proof.
  introv ispt ispu isv ap.
  unfold isvalue_like in isv; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst.

    + pose proof (howe_lemma2 lib c bterms u) as h; simpl in h.
      repeat (autodimp h hyp).
      exrepnd.
      exists (oterm (Can c) lbt'); dands; eauto.
      unfold computes_to_value in h0; repnd; auto.

    + apply howe_lemma2_seq in ap; auto; exrepnd.
      exists (sterm f'); dands; simpl; eauto 3 with slow; tcsp.

  - apply isexc_implies2 in isv; exrepnd; subst.
    applydup @isprogram_exception_implies in ispt; exrepnd; subst.
    pose proof (howe_lemma2_exc lib a t u) as h; simpl in h.
    repeat (autodimp h hyp).
    exrepnd.
    exists (oterm Exc [bterm [] a', bterm [] e']); simpl; dands; auto.
    unfold approx_ext_starbts, lblift_sub; simpl; dands; auto.
    introv k; repeat (destruct n; cpx).
    + unfold selectbt; simpl; eauto with slow.
    + unfold selectbt; simpl; eauto with slow.
Qed.

Lemma same_value_like_alpha_eq_r {o} :
  forall lib (t u v : @NTerm o),
    same_value_like lib t u
    -> alpha_eq u v
    -> same_value_like lib t v.
Proof.
  introv svl aeq.
  inversion svl as [| |? ? imp1]; clear svl; subst;
  inversion aeq as [|? ? imp2|]; clear aeq; subst; auto.
  constructor; introv; eauto 3 with slow.
Qed.

Lemma same_value_like_alpha_eq_l {o} :
  forall lib (t u v : @NTerm o),
    same_value_like lib t u
    -> alpha_eq t v
    -> same_value_like lib v u.
Proof.
  introv svl aeq.
  inversion svl as [| |? ? imp1]; clear svl; subst;
  inversion aeq as [|? ? imp2|]; clear aeq; subst; auto.
  constructor; introv; eauto 3 with slow.
Qed.

Lemma approx_ext_starbts_get_bterms_alpha_eq {o} :
  forall lib op (t u v : @NTerm o),
    approx_ext_starbts lib op (get_bterms t) (get_bterms u)
    -> alpha_eq u v
    -> approx_ext_starbts lib op (get_bterms t) (get_bterms v).
Proof.
  introv ap aeq.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl; auto;
  try (complete (inversion aeq; subst; allsimpl; tcsp)).
  - unfold approx_ext_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_ext_starbts, lblift_sub; simpl; sp.
  - unfold approx_ext_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_ext_starbts, lblift_sub; simpl; sp.
  - inversion aeq as [|?|? ? ? len imp]; subst; simpl.
    allunfold @approx_ext_starbts.
    allunfold @lblift_sub; repnd; dands; auto; try omega.
    introv i.
    pose proof (ap n) as h1; autodimp h1 hyp.
    pose proof (imp n) as h2; autodimp h2 hyp; try omega.
    eapply approx_ext_star_bterm_alpha_fun_r; eauto.
Qed.

(*
Lemma approx_ext_star_congruence_same_value_like {o} :
  forall lib (t u : @NTerm o),
    isprogram t
    -> isprogram u
    -> same_value_like t u
    -> approx_ext_starbts lib (get_op t) (get_bterms t) (get_bterms u)
    -> approx_ext_star lib t u.
Proof.
  introv ispt ispu svl ap.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl;
  try (complete (apply isprogram_vterm in ispt; sp));
  try (complete (apply isprogram_vterm in ispu; sp));
  try (complete (inversion svl)).
  - apply (apss _ _ _ f2); eauto 3 with slow.
  - inversion svl; subst; apply approx_ext_star_congruence3; auto.
Qed.
*)

Lemma closed_axiom {o} :
  @closed o mk_axiom.
Proof. sp. Qed.
Hint Resolve closed_axiom : slow.

Lemma alpha_eq_subst_utoken_not_in_implies2 {o} :
  forall (t1 t2 : @NTerm o) v a,
    !LIn a (get_utokens t1)
    -> !LIn a (get_utokens t2)
    -> alpha_eq (subst t1 v (mk_utoken a)) (subst t2 v (mk_utoken a))
    -> alpha_eq t1 t2.
Proof.
  introv ni1 ni2 aeq.
  pose proof (change_bvars_alpha_wspec [v] t1) as k1.
  pose proof (change_bvars_alpha_wspec [v] t2) as k2.
  exrepnd.
  allrw disjoint_singleton_l.
  pose proof (lsubst_alpha_congr2 ntcv0 t1 [(v,mk_utoken a)]) as p1.
  pose proof (lsubst_alpha_congr2 ntcv t2 [(v,mk_utoken a)]) as p2.
  autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
  allrw @fold_subst.
  assert (alpha_eq (subst ntcv0 v (mk_utoken a)) (subst ntcv v (mk_utoken a))) as h' by eauto with slow.
  apply alpha_eq_subst_utoken_not_in_implies in h'; eauto with slow.
  { intro j; destruct ni1; apply alphaeq_preserves_utokens in k3; rw k3; auto. }
  { intro j; destruct ni2; apply alphaeq_preserves_utokens in k0; rw k0; auto. }
Qed.

Lemma isprogram_pushdown_fresh {o} :
  forall v (t : @NTerm o),
    isprogram (pushdown_fresh v t) <=> isprog_vars [v] t.
Proof.
  introv; split; intro k.
  - destruct k as [c w].
    rw @isprog_vars_eq.
    apply nt_wf_pushdown_fresh in w; dands; auto.
    unfold closed in c.
    rw @free_vars_pushdown_fresh in c.
    rw subvars_prop; introv i.
    rw <- null_iff_nil in c.
    rw null_remove_nvars in c; apply c in i; sp.
  - rw @isprog_vars_eq in k; repnd.
    split; allrw @nt_wf_pushdown_fresh; auto.
    unfold closed; rw @free_vars_pushdown_fresh.
    rw <- null_iff_nil.
    rw null_remove_nvars; introv i.
    rw subvars_prop in k0; apply k0; auto.
Qed.

Lemma same_value_like_implies_same_op {o} :
  forall lib op1 op2 (bs1 bs2 : list (@BTerm o)),
    same_value_like lib (oterm op1 bs1) (oterm op2 bs2)
    -> op1 = op2.
Proof.
  introv s; inversion s; auto.
Qed.

Lemma fresh_id_approx_ext_any {o} :
  forall lib (t : @NTerm o) x,
    isprogram t
    -> approx_ext lib (mk_fresh x (mk_var x)) t.
Proof.
  introv Hpr.
  apply approx_ext_assume_hasvalue; auto.
  { apply isprogram_fresh; apply isprog_vars_var. }

  introv Hv.
  unfold hasvalue_like in Hv; exrepnd.
  apply (not_fresh_id_reduces_to_is_value_like _ _ x) in Hv1; tcsp.
Qed.

Lemma change_bvars_alpha_norep {o} :
  forall (t : @NTerm o) (lv : list NVar),
    {u : NTerm
     $ disjoint lv (bound_vars u)
     # alpha_eq t u
     # no_repeats (bound_vars u)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv.

  - Case "vterm".
    exists (@mk_var o v); simpl; dands; auto.

  - Case "sterm".
    exists (sterm f); simpl; dands; eauto 3 with slow.

  - Case "oterm".

    assert (forall lv, {bs' : list BTerm
            $ disjoint lv (bound_vars_bterms bs')
            # alpha_eq_bterms bs bs'
            # no_repeats (bound_vars_bterms bs') }) as ibs.
    { clear lv; induction bs; introv; allsimpl.
      - exists ([] : list (@BTerm o)); simpl; dands; eauto with slow.
      - autodimp IHbs hyp.
        { introv i s; eapply ind; eauto. }
        pose proof (IHbs lv) as ibs; clear IHbs; exrepnd.
        destruct a as [l t].

        pose proof (fresh_vars (length l)
                               (lv ++ l
                                   ++ all_vars t
                                   ++ bound_vars_bterms bs'))
             as fvs; exrepnd.
        allrw disjoint_app_r; exrepnd.

        pose proof (ind t (lsubst t (var_ren l lvn)) l) as ih; clear ind; repeat (autodimp ih hyp).
        { rw @lsubst_allvars_preserves_osize2; eauto 3 with slow. }

        pose proof (ih (lv ++ lvn ++ bound_vars_bterms bs')) as ht; clear ih.
        exrepnd.
        allrw disjoint_app_l; repnd.

        exists (bterm lvn u :: bs'); simpl.
        allrw no_repeats_app.
        allrw disjoint_app_l; allrw disjoint_app_r.
        dands; eauto 3 with slow.
        apply alpha_eq_bterms_cons; dands; auto.
        eapply alpha_eq_bterm_trans;[|apply alpha_eq_bterm_congr;exact ht2].
        apply alpha_bterm_change; auto.
        allrw disjoint_app_l; dands; eauto with slow.
    }

    pose proof (ibs lv) as h; clear ibs; exrepnd.
    exists (oterm op bs'); simpl; dands; auto.
    apply alpha_eq_oterm_combine; auto.
Qed.

Lemma blift_sub_diff {o} :
  forall vs lib op (b1 b2 : @BTerm o),
    blift_sub lib op (approx_ext_star lib) b1 b2
    -> {lv : list NVar
        $ {nt1,nt2 : NTerm
        $ (
            (op <> NCan NFresh # approx_ext_star lib nt1 nt2)
            [+]
            {sub : Sub
             & op = NCan NFresh
             # approx_ext_star lib (lsubst nt1 sub) (lsubst nt2 sub)
             # nrut_sub (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2) sub
             # lv = dom_sub sub}
          )
        # alpha_eq_bterm b1 (bterm lv nt1)
        # alpha_eq_bterm b2 (bterm lv nt2)
        # disjoint vs lv
        # disjoint vs (bound_vars nt1)
        # disjoint vs (bound_vars nt2)
        # disjoint lv (bound_vars nt1)
        # disjoint lv (bound_vars nt2)
        # no_repeats lv
        # no_repeats (bound_vars nt1)
        # no_repeats (bound_vars nt2) }}.
Proof.
  introv bl.
  unfold blift_sub in bl; exrepnd.

  pose proof (alpha_bterm_pair_change b1 b2 lv nt1 nt2 vs) as h.
  repeat (autodimp h hyp); exrepnd.
  allrw disjoint_app_r; allrw disjoint_app_l; repnd.

  pose proof (change_bvars_alpha_norep nt1n (vs ++ lvn)) as ch1; exrepnd.
  assert (alpha_eq nt1 u) as h2' by eauto with slow.
  assert (alpha_eq_bterm b1 (bterm lvn (lsubst u (var_ren lv lvn)))) as h4'.
  { eapply alpha_eq_bterm_trans;[exact h4|].
    apply alpha_eq_bterm_congr.
    apply lsubst_alpha_congr2; auto. }
  allrw disjoint_app_l; repnd.
  rename ch3 into h9'.
  rename ch1 into h13'.
  clear dependent nt1n.
  rename h2' into h2; rename h4' into h4; rename h9' into h9; rename h13' into h13.
  rename u into nt1n.

  pose proof (change_bvars_alpha_norep nt2n (vs ++ lvn)) as ch'1; exrepnd.
  assert (alpha_eq nt2 u) as h3' by eauto with slow.
  assert (alpha_eq_bterm b2 (bterm lvn (lsubst u (var_ren lv lvn)))) as h5'.
  { eapply alpha_eq_bterm_trans;[exact h5|].
    apply alpha_eq_bterm_congr.
    apply lsubst_alpha_congr2; auto. }
  allrw disjoint_app_l; repnd.
  rename ch'3 into h0'.
  rename ch'1 into h7'.
  clear dependent nt2n.
  rename h3' into h3; rename h5' into h5; rename h7' into h7; rename h0' into h0.
  rename u into nt2n.

  exists lvn (lsubst nt1n (var_ren lv lvn)) (lsubst nt2n (var_ren lv lvn)).
  dands; eauto 3 with slow; try (complete (rw @boundvars_lsubst_vars; auto)).

  repndors; exrepnd.

  - left; dands; auto.
    apply approx_ext_star_lsubst_vars; eauto 3 with slow.

  - right.
    exists (combine lvn (range sub)); dands; auto.

    + pose proof (lsubst_nest_same_alpha2 nt1n lv lvn (range sub)) as nest1.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest1 hyp); try omega; eauto 3 with slow.
      { subst; allrw @length_dom; auto. }
      { apply alphaeq_preserves_free_vars in h2; rw <- h2.
        apply disjoint_remove_nvars_weak_r; auto. }
      eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact nest1].

      pose proof (lsubst_nest_same_alpha2 nt2n lv lvn (range sub)) as nest2.
      allrw @length_dom; allrw @length_range.
      repeat (autodimp nest2 hyp); try omega; eauto 3 with slow.
      { subst; allrw @length_dom; auto. }
      { apply alphaeq_preserves_free_vars in h3; rw <- h3.
        apply disjoint_remove_nvars_weak_r; auto. }
      eapply approx_ext_star_alpha_fun_r;[|apply alpha_eq_sym; exact nest2].

      subst.
      rw <- @sub_eta; auto.

      apply (lsubst_alpha_congr2 _ _ sub) in h2.
      apply (lsubst_alpha_congr2 _ _ sub) in h3.
      eauto with slow.

    + repeat (rw @get_utokens_lib_lsubst_allvars; eauto with slow).
      apply (alphaeq_preserves_get_utokens_lib lib) in h2.
      apply (alphaeq_preserves_get_utokens_lib lib) in h3.
      rw <- h2; rw <- h3.
      eapply nrut_sub_change_sub_same_range;[|exact bl5].
      rw @range_combine; auto.
      rw @length_range; auto.
      subst; allrw @length_dom; auto.

    + rw @dom_sub_combine; auto.
      rw @length_range; auto.
      subst; allrw @length_dom; auto.
Qed.

Lemma bt_wf_mk_fresh_bterm_if {o} :
  forall (b : @BTerm o) v,
    bt_wf b
    -> bt_wf (mk_fresh_bterm v b).
Proof.
  introv wf.
  destruct b as [l t]; allsimpl.
  allrw @bt_wf_iff.
  apply nt_wf_fresh; auto.
Qed.

Lemma alpha_eq_bterm_ren_1side {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (bound_vars t1)
    -> disjoint l1 (bound_vars t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l1 (lsubst t2 (var_ren l2 l1))).
Proof.
  introv disj1 disj2 aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.
  apply (lsubst_alpha_congr2 _ _ (var_ren lv l1)) in a.
  allrw disjoint_app_r; repnd.

  pose proof (lsubst_nest_vars_same t1 l1 lv l1) as h1.
  allrw disjoint_app_l.
  repeat (autodimp h1 hyp); dands; eauto 3 with slow.
  rw h1 in a.

  pose proof (lsubst_nest_vars_same t2 l2 lv l1) as h2.
  allrw disjoint_app_l.
  repeat (autodimp h2 hyp); dands; try omega; eauto 3 with slow.
  rw h2 in a.

  pose proof (lsubst_trivial_alpha t1 l1) as h.
  eauto with slow.
Qed.

Lemma alpha_eq_bterm_ren_1side2 {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (bound_vars t1)
    -> disjoint l1 (bound_vars t2)
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alpha_eq t1 (lsubst t2 (var_ren l2 l1)).
Proof.
  introv disj1 disj2 aeq.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.
  apply (lsubst_alpha_congr2 _ _ (var_ren lv l1)) in a.
  allrw disjoint_app_r; repnd.

  pose proof (lsubst_nest_vars_same t1 l1 lv l1) as h1.
  allrw disjoint_app_l.
  repeat (autodimp h1 hyp); dands; eauto 3 with slow.
  rw h1 in a.

  pose proof (lsubst_nest_vars_same t2 l2 lv l1) as h2.
  allrw disjoint_app_l.
  repeat (autodimp h2 hyp); dands; try omega; eauto 3 with slow.
  rw h2 in a.

  pose proof (lsubst_trivial_alpha t1 l1) as h.
  eauto with slow.
Qed.

Lemma alpha_eq_lsubst_aux_pull_out_token {o} :
  forall (t : @NTerm o) l sub t',
    disjoint (dom_sub sub) (bound_vars t)
    -> disjoint (dom_sub sub) (bound_vars t')
    -> disjoint (bound_vars t) (bound_vars t')
    -> no_repeats (bound_vars t)
    -> nrut_sub l sub
    -> subset (get_utokens t') l
    -> no_repeats (dom_sub sub)
    -> wf_term t
    -> alpha_eq t (lsubst_aux t' sub)
    -> {u : NTerm $ t = lsubst_aux u sub # disjoint (get_utokens u) (get_utokens_sub sub)}.
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case;
  introv disj1 disj2 disj3 norep nrut ss nrs wf aeq;
  allsimpl; GC.

  - Case "vterm".
    destruct t' as [z|f|op' bs']; allsimpl;
    try (complete (inversion aeq)).

    remember (sub_find sub z) as sf; symmetry in Heqsf; destruct sf.

    + apply sub_find_some in Heqsf.
      eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst; inversion aeq.
    + inversion aeq; subst.
      exists (@mk_var o z); simpl; boolvar; tcsp.
      rw Heqsf; auto.

  - Case "sterm".
    exists (sterm f); simpl; dands; auto.

  - Case "oterm".
    destruct t' as [z|f|op' bs']; allsimpl; try (complete (inversion aeq)).

    + remember (sub_find sub z) as sf; symmetry in Heqsf; destruct sf;
      try (complete (inversion aeq)).

      apply sub_find_some in Heqsf.
      eapply in_nrut_sub in Heqsf; eauto; exrepnd; subst; inversion aeq; subst.
      allsimpl; cpx; allsimpl; fold_terms.

      pose proof (in_nrut_sub_or l a sub) as ora.
      repeat (autodimp ora hyp); repndors; exrepnd.

      { exists (@mk_var o v); simpl; allrw; dands; auto. }

      { exists (mk_utoken a); simpl; auto.
        rw disjoint_singleton_l; dands; auto. }

    + allrw @alpha_eq_oterm_combine2; repnd; subst.
      allrw map_length.

      rw @wf_oterm_iff in wf; repnd.

      assert {bs'' : list BTerm
              & bs = lsubst_bterms_aux bs'' sub
              # disjoint (get_utokens_bs bs'') (get_utokens_sub sub)} as hbs.
      { clear wf0.
        revert dependent bs'.
        revert dependent bs.
        induction bs as [|b bs]; introv ind disj1 norep wf disj2 disj3 ss len imp; allsimpl; cpx; GC.

        - exists ([] : list (@BTerm o)); simpl; auto.

        - destruct bs' as [|b' bs']; allsimpl; cpx.
          allrw in_app_iff; allrw not_over_or; repnd.
          allrw no_repeats_app; repnd.
          allrw disjoint_app_r; allrw disjoint_app_l; repnd.
          repeat (autodimp IHbs hyp).
          { introv i j k; eapply ind; eauto. }
          pose proof (IHbs bs') as ih; clear IHbs.
          repeat (autodimp ih IHbs); exrepnd.
          { allrw subset_app; repnd; dands; auto. }
          pose proof (imp b (lsubst_bterm_aux b' sub)) as h.
          repeat (autodimp h hyp).
          destruct b as [l1 t1].
          destruct b' as [l2 t2].
          allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          allrw disjoint_app_l; repnd.
          allrw no_repeats_app; repnd.
          allrw disjoint_app_r; allrw disjoint_app_l; repnd.
          applydup @alpha_eq_bterm_lenbvars in h.

          apply alpha_eq_bterm_ren_1side2 in h; auto;
          [|introv i j; apply subset_bound_vars_lsubst_aux in j; allsimpl;
            allrw in_app_iff; repndors; tcsp;
            [apply disj8 in i; sp|];
            rw (sub_bound_vars_nrut_sub (sub_filter sub l2) l) in j; allsimpl; tcsp;
            complete (eauto with slow)].
          pose proof (ind t1 l1) as k; clear ind; autodimp k hyp.

          rw @lsubst_lsubst_aux in h;
            [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
               rw @sub_free_vars_var_ren; auto;
               introv i j; apply subset_bound_vars_lsubst_aux in i; allsimpl;
               allrw in_app_iff; applydup disj8 in j; repndors; tcsp;
               apply subset_sub_bound_vars_sub_filter in i;
               erewrite sub_bound_vars_nrut_sub in i; eauto].

          rw (sub_filter_disjoint1 sub) in h; eauto 3 with slow.

          pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                        t2 sub (var_ren l2 l1)) as e.
          allsimpl; rw @sub_free_vars_var_ren in e; auto.
          rw (sub_bound_vars_nrut_sub sub l) in e; eauto 3 with slow.
          rw (sub_free_vars_nrut_sub sub l) in e; eauto 3 with slow.
          rw @cl_lsubst_aux_sub_trivial in e; eauto 3 with slow.
          repeat (autodimp e hyp); eauto with slow.
          rw <-  e in h; clear e.

          pose proof (k l sub (lsubst_aux t2 (sub_filter (var_ren l2 l1) (dom_sub sub))))
            as ih; clear k.
          repeat (autodimp ih hyp); eauto 3 with slow.
          { introv i j; apply subset_bound_vars_lsubst_aux in j.
            rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
            allrw app_nil_r; apply disj7 in i; sp. }
          { introv i j; apply subset_bound_vars_lsubst_aux in j.
            rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
            allrw app_nil_r; apply disj5 in i; sp. }
          { allrw subset_app; repnd; rw @get_utokens_lsubst_aux_allvars; eauto 3 with slow. }
          { pose proof (wf (bterm l1 t1)) as w; autodimp w hyp. }

          exrepnd.
          exists (bterm l1 u :: bs''); simpl.
          allrw disjoint_app_l; dands; eauto 3 with slow.
          f_equal; auto.
          f_equal; auto.
          rw (sub_filter_disjoint1 sub); eauto 3 with slow.
      }

      exrepnd.

      remember (get_utok op') as guo; symmetry in Heqguo; destruct guo.

      { apply get_utok_some in Heqguo; subst; allsimpl.
        destruct bs''; allsimpl; cpx; GC; fold_terms.
        allrw subset_cons_l; repnd; allsimpl.
        exists (mk_utoken g); simpl; fold_terms; rw disjoint_singleton_l; dands; auto.
        unfold nrut_sub in nrut; repnd.
        apply nrut in ss0; sp.
      }

      { exists (oterm op' bs''); simpl; subst.
        allrw subset_app; repnd.
        allrw disjoint_app_l; dands; eauto 3 with slow.
        unfold lsubst_bterms_aux; auto.
        destruct op'; allsimpl; tcsp.
        destruct c; allsimpl; tcsp.
      }
Qed.

Lemma alpha_eq_subst_bterm_aux_pull_out_token {o} :
  forall b v a l (t : @NTerm o),
    !LIn v l
    -> !LIn v (bound_vars t)
    -> disjoint l (bound_vars t)
    -> no_repeats (bound_vars t)
    -> !LIn a (get_utokens_b b)
    -> wf_term t
    -> alpha_eq_bterm (subst_bterm_aux b v (mk_utoken a)) (bterm l t)
    -> {u : NTerm & t = subst u v (mk_utoken a) # !LIn a (get_utokens u)}.
Proof.
  introv ni1 ni2 disj1 norep niab wf aeq.

  pose proof (ex_change_bvars_bterm_alpha (v :: l ++ bound_vars t) b) as ch; exrepnd.
  allrw disjoint_cons_l; allrw disjoint_app_l; repnd.
  pose proof (lsubst_aux_alphabt_congr_cl b bt' [(v,mk_utoken a)] [(v,mk_utoken a)]) as aeqb.
  repeat (autodimp aeqb hyp); eauto with slow.
  eapply alpha_eq_bterm_trans in aeq;[|apply alpha_eq_bterm_sym; exact aeqb].
  assert (!LIn a (get_utokens_b bt')) as niabt'.
  { apply alpha_eq_bterm_preserves_utokens in ch0; rw <- ch0; auto. }
  clear dependent b; rename bt' into b.
  rename ch3 into disj2; rename ch2 into disj3; rename ch1 into ni3; rename niabt' into niab.

  destruct b as [l1 u1]; allsimpl.
  allrw disjoint_app_r; repnd.
  allunfold @subst_bterm_aux; allsimpl; boolvar.
  - allrw @lsubst_aux_nil.
    exists t.
    applydup @alpha_eq_bterm_preserves_utokens in aeq as eu; allsimpl; rw <- eu.
    apply alpha_eq_bterm_preserves_free_vars in aeq; allsimpl.
    rw @cl_subst_trivial; eauto with slow.
    introv i.
    assert (LIn v (remove_nvars l (free_vars t))) as j.
    { rw in_remove_nvars; sp. }
    rw <- aeq in j.
    rw in_remove_nvars in j; sp.
  - (* change the l1 into l when inverting aeq *)
    apply alpha_eq_bterm_sym in aeq.
    applydup @alpha_eq_bterm_lenbvars in aeq.
    apply alpha_eq_bterm_ren_1side2 in aeq; auto;
    [|introv i j; apply subset_bound_vars_lsubst_aux in j; allsimpl;
      allrw app_nil_r; apply disj2 in i; sp].
    rw @lsubst_lsubst_aux in aeq;
      [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
         rw @sub_free_vars_var_ren; auto;
         introv i j; apply subset_bound_vars_lsubst_aux in i; allsimpl;
         allrw app_nil_r; apply disj2 in j; sp].

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj u1 [(v,mk_utoken a)] (var_ren l1 l)) as h.
    allsimpl.
    rw @sub_free_vars_var_ren in h; auto.
    allrw disjoint_singleton_l; fold_terms.
    repeat (autodimp h hyp); eauto 3 with slow.
    rw <-  h in aeq; clear h.

    pose proof (alpha_eq_lsubst_aux_pull_out_token
                  t (get_utokens u1) [(v,mk_utoken a)]
                  (lsubst_aux u1 (sub_filter (var_ren l1 l) [v]))) as h.
    allsimpl; allrw disjoint_singleton_l.
    repeat (autodimp h hyp); eauto 3 with slow.

    { intro i; apply subset_bound_vars_lsubst_aux in i; allrw in_app_iff.
      rw @sub_bound_vars_allvars_sub in i; eauto 3 with slow.
      allsimpl; repndors; tcsp. }

    { introv i j; apply subset_bound_vars_lsubst_aux in j; allrw in_app_iff.
      rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
      allsimpl; repndors; tcsp.
      apply disj3 in i; sp. }

    { apply nrut_sub_cons; eexists; simpl; dands; eauto; tcsp; eauto with slow. }

    { rw @get_utokens_lsubst_aux_allvars; eauto with slow. }

    exrepnd; allsimpl.
    unfold get_utokens_sub in h0; allsimpl; allrw disjoint_singleton_r.
    exists u.
    unfsubst; dands; auto.
Qed.

Lemma alpha_eq_bterm_ren_1side3 {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    disjoint l1 (all_vars t2)
    -> length l1 = length l2
    -> no_repeats l1
    -> alpha_eq t1 (lsubst t2 (var_ren l2 l1))
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2).
Proof.
  introv disj1 len norep aeq.
  pose proof (fresh_vars (length l1) (l1 ++ l2
                                         ++ all_vars t1
                                         ++ all_vars t2))
    as fvs; exrepnd; allrw disjoint_app_r; repnd.
  apply (al_bterm _ _ lvn); allrw disjoint_app_r; auto.
  apply (lsubst_alpha_congr2 _ _ (var_ren l1 lvn)) in aeq.
  pose proof (lsubst_nest_vars_same t2 l2 l1 lvn) as h.
  repeat (autodimp h hyp); allrw disjoint_app_l; dands; auto.
  rw h in aeq; eauto with slow.
Qed.

Definition maybe_new_var_b {o} (v : NVar) (b : @BTerm o) :=
  match b with
    | bterm l t => maybe_new_var v l t
  end.

Lemma in_nrut_sub_eq {o} :
  forall (sub: @Sub o) v1 v2 t l,
    nrut_sub l sub
    -> LIn (v1, t) sub
    -> LIn (v2, t) sub
    -> v1 = v2.
Proof.
  induction sub; introv nrut ni1 ni2; allsimpl; tcsp.
  destruct a as [v u].
  allrw @nrut_sub_cons; exrepnd; subst.
  repndors; subst; tcsp; cpx.
  - destruct nrut2; rw lin_flat_map.
    apply in_sub_eta in ni1; repnd.
    eexists; dands; eauto; simpl; tcsp.
  - destruct nrut2; rw lin_flat_map.
    apply in_sub_eta in ni2; repnd.
    eexists; dands; eauto; simpl; tcsp.
  - eapply IHsub; eauto.
Qed.

Lemma eqset_preserves_null {T} :
  forall (s1 s2 : list T),
    eqset s1 s2
    -> null s1
    -> null s2.
Proof.
  introv eqs n i.
  apply eqs in i.
  apply n in i; sp.
Qed.

Lemma null_get_utokens_sub_keep_first_free_vars_eq {o} :
  forall l (t : @NTerm o) sub,
    nrut_sub l sub
    -> null (get_utokens_sub (sub_keep_first sub (free_vars t)))
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv nrut nu; allsimpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; auto.
    unfold get_utokens_sub in nu.
    allrw @null_flat_map.
    applydup @sub_find_some in Heqsf.
    pose proof (nu n) as h; clear nu.
    eapply in_nrut_sub in nrut; eauto; exrepnd; subst; allsimpl.
    autodimp h hyp.

    + apply in_range_iff; exists v.
      apply in_sub_keep_first; simpl; tcsp.

    + pose proof (h a) as q; allsimpl; destruct q; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x as [vs t]; allsimpl.
    f_equal.
    eapply ind;[eauto| |]; eauto 3 with slow.
    introv j.
    allrw @in_get_utokens_sub; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allrw @sub_find_sub_filter_eq; boolvar; ginv.
    destruct (nu x).
    apply in_get_utokens_sub.
    exists v t0; dands; auto.
    apply in_sub_keep_first; dands; auto.
    apply lin_flat_map.
    eexists; dands; eauto.
    simpl; rw in_remove_nvars; sp.
Qed.

Lemma alpha_eq_lsubst_aux_nrut_sub_implies {o} :
  forall (t1 t2 : @NTerm o) sub l,
    nrut_sub l sub
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> disjoint (dom_sub sub) (bound_vars t1)
    -> disjoint (dom_sub sub) (bound_vars t2)
    -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub)
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv nrut ss1 ss2 disj1 disj2 aeq; allsimpl.

  - Case "vterm".
    remember (sub_find sub v1) as sf; symmetry in Heqsf; destruct sf.

    + apply sub_find_some in Heqsf.
      dup Heqsf as i.
      eapply in_nrut_sub in i; eauto; exrepnd; subst.
      destruct t2 as [v2|f2|op2 bs2]; allsimpl;
      try (complete (inversion aeq)).

      * remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

        { apply sub_find_some in Heqsf'.
          dup Heqsf' as j.
          eapply in_nrut_sub in j; eauto; exrepnd; subst.
          inversion aeq; subst; allsimpl; GC.
          apply (in_nrut_sub_eq sub v1 v2 (mk_utoken a0) l) in nrut; auto; subst; auto. }

        { inversion aeq. }

      * inversion aeq; subst; allsimpl; cpx; destruct bs2; allsimpl; cpx; GC; fold_terms.
        allrw singleton_subset; tcsp.

    + apply sub_find_none2 in Heqsf.
      destruct t2 as [v2|f2|op2 bs2]; allsimpl;
      try (complete (inversion aeq)).

      remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

      { apply sub_find_some in Heqsf'.
        dup Heqsf' as j.
        eapply in_nrut_sub in j; eauto; exrepnd; subst.
        inversion aeq. }

      { inversion aeq; subst; auto. }

  - Case "sterm".
    applydup @alphaeq_preserves_utokens in aeq; allsimpl.
    symmetry in aeq0; apply null_iff_nil in aeq0.
    eapply eqset_preserves_null in aeq0;[|apply get_utokens_lsubst_aux].
    allrw @null_app; repnd.
    erewrite null_get_utokens_sub_keep_first_free_vars_eq in aeq; eauto.

  - Case "oterm".
    allrw subset_app; repnd.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion aeq)).

    + remember (sub_find sub v2) as sf'; symmetry in Heqsf'; destruct sf'.

      { apply sub_find_some in Heqsf'.
        dup Heqsf' as j.
        eapply in_nrut_sub in j; eauto; exrepnd; subst.
        inversion aeq; subst; allsimpl; destruct bs1; allsimpl; cpx; GC; fold_terms.
        allrw singleton_subset; tcsp. }

      { inversion aeq. }

    + apply alpha_eq_oterm_combine2 in aeq; allrw map_length; repnd; subst.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      pose proof (aeq (lsubst_bterm_aux b1 sub) (lsubst_bterm_aux b2 sub)) as aeqb; clear aeq.
      rw <- @map_combine in aeqb.
      rw in_map_iff in aeqb.
      autodimp aeqb hyp.
      { eexists; dands; eauto. }
      applydup in_combine in i; repnd; disj_flat_map.
      destruct b1 as [l1 t1]; destruct b2 as [l2 t2]; allsimpl.
      allrw disjoint_app_r; repnd.
      allrw subset_app; repnd.

      repeat (rw @sub_filter_disjoint1 in aeqb; eauto 3 with slow).

      pose proof (fresh_vars
                    (length l1)
                    (all_vars (lsubst_aux t1 sub)
                              ++ all_vars (lsubst_aux t2 sub)
                              ++ dom_sub sub
                              ++ bound_vars t1
                              ++ bound_vars t2
                              ++ free_vars t1
                              ++ free_vars t2))
        as fvs; exrepnd; allrw disjoint_app_r; repnd.

      pose proof (alphabt_change_var_aux
                    (lsubst_aux t1 sub) (lsubst_aux t2 sub) l1 l2) lvn
        as a.
      allrw disjoint_app_r; repeat (autodimp a hyp); dands; eauto 3 with slow.
      repnd.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t1 sub (var_ren l1 lvn)) as e1.
      rw @sub_free_vars_var_ren in e1; auto.
      rw @cl_lsubst_aux_sub_trivial in e1; eauto 3 with slow.
      erewrite sub_bound_vars_nrut_sub in e1; eauto 3 with slow.
      erewrite sub_free_vars_nrut_sub in e1; eauto 3 with slow.
      rw @sub_filter_disjoint1 in e1;[|rw @dom_sub_var_ren; eauto with slow]; auto.
      repeat (autodimp e1 hyp); eauto 3 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t2 sub (var_ren l2 lvn)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try omega.
      rw @cl_lsubst_aux_sub_trivial in e2; eauto 3 with slow.
      erewrite sub_bound_vars_nrut_sub in e2; eauto 3 with slow.
      erewrite sub_free_vars_nrut_sub in e2; eauto 3 with slow.
      rw @sub_filter_disjoint1 in e2;[|rw @dom_sub_var_ren; eauto with slow]; auto; try omega.
      repeat (autodimp e2 hyp); eauto 3 with slow.

      rw <- e1 in a0; rw <- e2 in a0; clear e1 e2.

      pose proof (ind1 t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as q; clear ind1.
      repeat (autodimp q hyp).
      { rw @lsubst_aux_allvars_preserves_osize2; eauto 2 with slow. }
      pose proof (q (lsubst_aux t2 (var_ren l2 lvn)) sub l) as ih; clear q.
      repeat (rw @get_utokens_lsubst_aux_allvars in ih; eauto 3 with slow).
      repeat (rw @boundvars_lsubst_aux_vars in ih; auto; try omega).
      repeat (autodimp ih hyp); eauto 3 with slow.
      { introv z1; apply ss1; rw lin_flat_map; eexists; dands; eauto. }
      { introv z1; apply ss2; rw lin_flat_map; eexists; dands; eauto. }
      apply (al_bterm _ _ lvn); allrw disjoint_app_r; dands; auto.

      repeat (rw @lsubst_lsubst_aux); auto;
      rw <- @sub_free_vars_is_flat_map_free_vars_range;
      rw @computation2.sub_free_vars_var_ren; eauto 3 with slow; try omega.
Qed.

Lemma alpha_eq_bterm_mk_fresh_bterm_berm {o} :
  forall (b : @BTerm o) v a l t,
    disjoint l (all_vars_bterm b)
    -> disjoint l (bound_vars t)
    -> !LIn v l
    -> !LIn (maybe_new_var_b v b) l
    -> no_repeats l
    -> !LIn a (get_utokens t)
    -> !LIn a (get_utokens_b b)
    -> alpha_eq_bterm (subst_bterm_aux b v (mk_utoken a))
                      (bterm l (subst t v (mk_utoken a)))
    -> alpha_eq_bterm (mk_fresh_bterm v b) (bterm l (mk_fresh v t)).
Proof.
  introv disj1 disj2 ni1 ni2 norep nia1 nia2 aeqb.
  destruct b as [l' t'].
  unfold mk_fresh_bterm.
  apply alpha_eq_bterm_sym.
  allsimpl; allrw disjoint_app_r; repnd.
  applydup @alphaeqbt_numbvars in aeqb as len.
  unfold num_bvars in len; allsimpl.

  apply alpha_eq_bterm_sym in aeqb.
  unfold subst_bterm_aux in aeqb; allsimpl.
  apply alpha_eq_bterm_ren_1side2 in aeqb;
    [|unfold subst; rw @cl_lsubst_lsubst_aux; eauto 3 with slow;
      rw (@bound_vars_lsubst_aux_nrut_sub o t [(v,mk_utoken a)] []);
      eauto 3 with slow;
      apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp
     |boolvar; allrw @lsubst_aux_nil; auto;
      rw (@bound_vars_lsubst_aux_nrut_sub o t' [(v,mk_utoken a)] []);
      eauto 3 with slow;
      apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp].

  apply alpha_eq_bterm_ren_1side3; auto.
  { unfold all_vars; simpl; allrw app_nil_r.
    allrw disjoint_app_r; allrw disjoint_cons_r; dands; auto.
    apply disjoint_remove_nvars_weak_r; auto. }

  rw @lsubst_lsubst_aux; simpl; fold_terms;
  [|rw app_nil_r; rw <- @sub_free_vars_is_flat_map_free_vars_range;
    rw @sub_free_vars_var_ren; auto;
    apply disjoint_cons_l; dands; complete (eauto with slow)].

  allunfold @maybe_new_var.
  boolvar.

  - allrw @lsubst_aux_nil.
    assert (!LIn v (free_vars t)) as nivt.
    { intro i; apply alphaeq_preserves_utokens in aeqb.
      rw (get_utokens_lsubst_allvars t') in aeqb; eauto 3 with slow.
      rw <- aeqb in nia2; destruct nia2.
      apply get_utokens_lsubst; rw in_app_iff; sp; simpl.
      boolvar; tcsp. }
    rw @cl_subst_trivial in aeqb; eauto 3 with slow.
    rw @lsubst_aux_sub_filter_aux; simpl;
    [|introv i j; repndors; tcsp; subst;
      rw @dom_sub_var_ren; auto;
      apply newvar_prop in i; complete sp].

    dup aeqb as aeq.
    apply (implies_alpha_eq_mk_fresh v) in aeqb.
    rw <- @lsubst_lsubst_aux;
      [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
         rw @sub_free_vars_var_ren; complete (eauto with slow)].
    eapply alpha_eq_trans;[exact aeqb|].

    pose proof (ex_fresh_var (all_vars (lsubst t' (var_ren l' l)))) as fv; exrepnd.
    apply (implies_alpha_eq_mk_fresh_sub v0); allrw in_app_iff; allrw not_over_or; repnd; tcsp.
    repeat (rw (lsubst_trivial3 (lsubst t' (var_ren l' l)))); auto.

    { introv i; apply in_var_ren in i; allsimpl; exrepnd; repndors; tcsp; subst; allsimpl.
      rw disjoint_singleton_l; dands; auto.
      intro j.
      pose proof (eqvars_free_vars_disjoint t' (var_ren l' l)) as e.
      rw eqvars_prop in e; apply e in j; clear e.
      rw @dom_sub_var_ren in j; auto.
      rw in_app_iff in j; rw in_remove_nvars in j; repndors; exrepnd; tcsp.
      - apply newvar_prop in j0; sp.
      - apply in_sub_free_vars in j; exrepnd.
        apply in_sub_keep_first in j0; repnd.
        apply sub_find_some in j2.
        apply in_var_ren in j2; exrepnd; subst; allsimpl; repndors; tcsp; subst; tcsp.
    }

    { introv i; apply in_var_ren in i; allsimpl; exrepnd; repndors; tcsp; subst; allsimpl.
      rw disjoint_singleton_l; dands; auto.
      intro j.
      pose proof (eqvars_free_vars_disjoint t' (var_ren l' l)) as e.
      rw eqvars_prop in e; apply e in j; clear e.
      rw @dom_sub_var_ren in j; auto.
      rw in_app_iff in j; rw in_remove_nvars in j; repndors; exrepnd; tcsp.
      apply in_sub_free_vars in j; exrepnd.
      apply in_sub_keep_first in j0; repnd.
      apply sub_find_some in j2.
      apply in_var_ren in j2; exrepnd; subst; allsimpl; repndors; tcsp; subst; tcsp.
    }

  - rw @lsubst_lsubst_aux in aeqb;
    [|rw <- @sub_free_vars_is_flat_map_free_vars_range;
       rw @sub_free_vars_var_ren; try (complete (eauto 3 with slow));
       rw (@bound_vars_lsubst_aux_nrut_sub o t' [(v,mk_utoken a)] []);
       eauto 3 with slow;
       apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp].

    pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                  t' [(v,mk_utoken a)] (var_ren l' l)) as e; allsimpl.
    allrw disjoint_singleton_l.
    rw @sub_free_vars_var_ren in e; try (complete (eauto 3 with slow)).
    repeat (autodimp e hyp); eauto 2 with slow; fold_terms.
    rw <- e in aeqb; clear e.
    apply implies_alpha_eq_mk_fresh.
    remember (lsubst_aux t' (sub_filter (var_ren l' l) [v])) as t''.
    unfold subst in aeqb; rw @cl_lsubst_lsubst_aux in aeqb; eauto 2 with slow.

    assert (!LIn a (get_utokens t'')) as niat''.
    { subst; intro i.
      apply get_utokens_lsubst_aux in i; allrw in_app_iff; repndors; tcsp.
      rw @get_utokens_sub_allvars_sub in i; allsimpl; eauto with slow.
    }

    clear Heqt''.

    pose proof (change_bvars_alpha_wspec [v] t) as aeqt; exrepnd.
    pose proof (change_bvars_alpha_wspec [v] t'') as aeqt'; exrepnd.
    allrw disjoint_singleton_l.

    assert (alpha_eq (lsubst_aux t [(v, mk_utoken a)])
                     (lsubst_aux ntcv [(v, mk_utoken a)])) as aeq1.
    { apply computation2.lsubst_aux_alpha_congr_same_cl_sub; eauto 3 with slow. }

    assert (alpha_eq (lsubst_aux t'' [(v, mk_utoken a)])
                     (lsubst_aux ntcv0 [(v, mk_utoken a)])) as aeq2.
    { apply computation2.lsubst_aux_alpha_congr_same_cl_sub; eauto 3 with slow. }

    assert (alpha_eq (lsubst_aux ntcv [(v, mk_utoken a)])
                     (lsubst_aux ntcv0 [(v, mk_utoken a)])) as aeq3.
    { eapply alpha_eq_trans;[apply alpha_eq_sym; exact aeq1|].
      eapply alpha_eq_trans;[exact aeqb|].
      eauto with slow. }
    clear aeq1 aeq2.

    assert (alpha_eq ntcv ntcv0) as aeq;[|eauto 4 with slow];[].

    apply (alpha_eq_lsubst_aux_nrut_sub_implies
             _ _ _ (get_utokens ntcv ++ get_utokens ntcv0)) in aeq3;
      simpl; eauto 3 with slow; allrw disjoint_singleton_l; auto.

    apply alphaeq_preserves_utokens in aeqt0.
    apply alphaeq_preserves_utokens in aeqt'0.
    rw aeqt0 in nia1.
    rw aeqt'0 in niat''.
    apply nrut_sub_cons; eexists; dands; simpl; eauto; tcsp; eauto 3 with slow.
    rw in_app_iff; tcsp.
Qed.

Lemma alpha_eq_bterm_preserves_isprog_vars {o} :
  forall l1 l2 (t1 t2 : @NTerm o),
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> isprog_vars l1 t1
    -> isprog_vars l2 t2.
Proof.
  introv aeq isp.
  allrw @isprog_vars_eq; repnd.
  applydup @alphaeqbt_preserves_nt_wf in aeq as w.
  rw w; dands; auto.
  apply alphaeqbt_preserves_fvars in aeq; allsimpl.
  rw eqvars_prop in aeq.
  allrw subvars_prop.
  introv i.
  destruct (in_deq _ deq_nvar x l2) as [d|d]; auto.
  assert (LIn x (remove_nvars l2 (free_vars t2))) as j.
  { rw in_remove_nvars; sp. }
  apply aeq in j.
  rw in_remove_nvars in j; repnd.
  apply isp0 in j0; sp.
Qed.

Lemma approx_ext_starbts_get_bterms_alpha_eq_l {o} :
  forall lib op (t u v : @NTerm o),
    approx_ext_starbts lib op (get_bterms t) (get_bterms u)
    -> alpha_eq t v
    -> approx_ext_starbts lib op (get_bterms v) (get_bterms u).
Proof.
  introv ap aeq.
  destruct t as [v1|f1|op1 bs1]; destruct u as [v2|f2|op2 bs2]; allsimpl; auto;
  try (complete (inversion aeq; subst; allsimpl; auto)).
  - unfold approx_ext_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_ext_starbts, lblift_sub; simpl; sp.
  - unfold approx_ext_starbts, lblift_sub in ap; allsimpl; repnd; cpx.
    inversion aeq; subst; allsimpl; cpx; auto.
    unfold approx_ext_starbts, lblift_sub; simpl; sp.
  - inversion aeq as [|?|? ? ? len imp]; subst; simpl.
    allunfold @approx_ext_starbts.
    allunfold @lblift_sub; repnd; dands; auto; try omega.
    introv i.
    pose proof (ap n) as h1; autodimp h1 hyp; try omega.
    pose proof (imp n) as h2; autodimp h2 hyp; try omega.
    eapply approx_ext_star_bterm_alpha_fun_l;[apply alpha_eq_bterm_sym; exact h2|]; auto.
Qed.

Lemma subst_sterm {o} :
  forall (f : @ntseq o) v t,
    subst (sterm f) v t = sterm f.
Proof.
  introv; unfold subst; autorewrite with slow; auto.
Qed.
Hint Rewrite @subst_sterm : slow.

(*
Lemma same_value_like_sterm_implies_approx_ext_star {o} :
  forall lib (f1 f2 : @ntseq o),
    nt_wf (sterm f2)
    -> same_value_like (sterm f1) (sterm f2)
    -> approx_ext_star lib (sterm f1) (sterm f2).
Proof.
  introv wf svl.
  inversion svl; subst; clear svl.
  econstructor; eauto.
  apply approx_ext_open_refl; auto.
Qed.
Hint Resolve same_value_like_sterm_implies_approx_ext_star : slow.
 *)

Lemma eq_get_utokens_implies_eq_get_utokens_lib {o} :
  forall lib (t1 t2 : @NTerm o),
    get_utokens t1 = get_utokens t2
    -> get_utokens_lib lib t1 = get_utokens_lib lib t2.
Proof.
  introv h; unfold get_utokens_lib; f_equal; auto.
Qed.

Lemma get_utokens_lib_lsubst_aux_subset {o} :
  forall lib (t : @NTerm o) sub,
    subset
      (get_utokens_lib lib (lsubst_aux t sub))
      (get_utokens_lib lib t ++ get_utokens_sub sub).
Proof.
  introv; unfold get_utokens_lib; introv i; allrw in_app_iff; repndors; tcsp.
  apply get_utokens_lsubst_aux_subset in i; allrw in_app_iff; repndors; tcsp.
Qed.

Lemma approx_ext_star_pushdown_fresh_if_subst {o} :
  forall lib (t1 t2 : @NTerm o) v1 v2 a,
    !LIn a (get_utokens_lib lib t1)
    -> !LIn a (get_utokens_lib lib t2)
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> same_value_like lib (subst t1 v1 (mk_utoken a)) (subst t2 v2 (mk_utoken a))
    -> approx_ext_starbts lib (get_op t1) (get_bterms (subst t1 v1 (mk_utoken a))) (get_bterms (subst t2 v2 (mk_utoken a)))
    -> approx_ext_star lib (pushdown_fresh v1 t1) (pushdown_fresh v2 t2).
Proof.
  introv ni1 ni2 isp1 isp2 svl ap.

  pose proof (ex_fresh_var (all_vars t1
                                     ++ all_vars t2))
    as fv; exrepnd.
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (alpha_bterm_change
                (bterm [v1] t1) [v1] t1 [v]) as aeqbt1.
  allrw disjoint_singleton_r.
  allrw in_app_iff; allrw not_over_or.
  allsimpl.
  repeat (autodimp aeqbt1 hyp).

  pose proof (alpha_bterm_change
                (bterm [v2] t2) [v2] t2 [v]) as aeqbt2.
  allrw disjoint_singleton_r.
  allrw in_app_iff; allrw not_over_or.
  allsimpl.
  repeat (autodimp aeqbt2 hyp).

  remember (lsubst t1 (var_ren [v1] [v])) as nt1.
  remember (lsubst t2 (var_ren [v2] [v])) as nt2.

  applydup @alpha_eq_bterm_preserves_utokens in aeqbt1 as ut1; allsimpl.
  rw ut1 in ni3.
  applydup @alpha_eq_bterm_preserves_utokens in aeqbt2 as ut2; allsimpl.
  rw ut2 in ni0.

  pose proof (lsubst_alpha_congr4 [v1] [v] t1 nt1 [(v1,mk_utoken a)] [(v,mk_utoken a)]) as c1.
  allsimpl.
  repeat (autodimp c1 hyp); eauto 3 with slow.

  pose proof (lsubst_alpha_congr4 [v2] [v] t2 nt2 [(v2,mk_utoken a)] [(v,mk_utoken a)]) as c2.
  allsimpl.
  repeat (autodimp c2 hyp); eauto 3 with slow.

  allrw @fold_subst.

  eapply same_value_like_alpha_eq_r in svl;[|exact c2].
  eapply same_value_like_alpha_eq_l in svl;[|exact c1].

  eapply alpha_eq_bterm_preserves_isprog_vars in isp1;[|exact aeqbt1].
  eapply alpha_eq_bterm_preserves_isprog_vars in isp2;[|exact aeqbt2].

  assert (get_op t1 = get_op nt1) as go.
  { subst; rw @lsubst_lsubst_aux; allrw <- @sub_free_vars_is_flat_map_free_vars_range;
    allsimpl; allrw disjoint_singleton_r; auto.
    destruct t1; simpl; boolvar; simpl; tcsp. }
  rw go in ap.

  eapply approx_ext_starbts_get_bterms_alpha_eq in ap;[|exact c2].
  eapply approx_ext_starbts_get_bterms_alpha_eq_l in ap;[|exact c1].

  applydup @implies_alpha_eq_pushdown_fresh in aeqbt1 as apf1.
  applydup @implies_alpha_eq_pushdown_fresh in aeqbt2 as apf2.

  eapply approx_ext_star_alpha_fun_l;[|apply alpha_eq_sym; exact apf1].
  eapply approx_ext_star_alpha_fun_r;[|apply alpha_eq_sym; exact apf2].

  clear dependent t1.
  clear dependent t2.
  rename nt1 into t1.
  rename nt2 into t2.

  repeat (unfsubst in svl); repeat (unfsubst in ap); allsimpl.
  destruct t1 as [x|f|op bs]; allsimpl; tcsp; GC.

  - boolvar.

    + apply approx_ext_open_implies_approx_ext_star.
      apply approx_ext_implies_approx_ext_open.
      apply (approx_ext_trans _ _ (mk_fresh x (mk_var x))).

      * apply reduces_to_implies_approx_ext2.
        { apply isprogram_fresh.
          apply isprog_vars_var. }
        apply reduces_to_if_step.
        csunf; simpl; boolvar; auto.

      * apply fresh_id_approx_ext_any.
        apply isprogram_pushdown_fresh; auto.

    + inversion svl.

  - autorewrite with slow in *.
    destruct t2 as [v2|f2|op bs]; allsimpl; boolvar; allsimpl;
    try (complete (inversion svl)); eauto 4 with slow.
    inversion svl; subst; clear svl.
    allrw @isprog_vars_eq; repnd.
    econstructor;[| |eauto|]; eauto 3 with slow.

  - allsimpl.
    destruct t2 as [x|f|op' bs']; allsimpl; GC; try (complete (inversion svl)).

    + boolvar; try (complete (inversion svl)).
      inversion svl; subst; allsimpl.
      allrw not_over_or; sp.

    + applydup @same_value_like_implies_same_op in svl; subst.

      assert (length bs = length bs') as e.
      {  unfold approx_ext_starbts, lblift_sub in ap; repnd; allrw map_length.
         unfold mk_fresh_bterms; allrw map_length; auto. }

      apply (apso _ _ _ _ (mk_fresh_bterms v bs')); auto;
      try (apply approx_ext_open_refl);
      [unfold mk_fresh_bterms; allrw map_length; auto
       |idtac
       |apply isprog_vars_eq in isp2; repnd;
       allrw @nt_wf_oterm_iff; repnd;
       rw <- isp3;
       unfold mk_fresh_bterms; allrw map_map; unfold compose; dands;
       [ apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto|];
       introv i; allrw in_map_iff; exrepnd; subst;
       apply isp2 in i1; apply bt_wf_mk_fresh_bterm_if; complete auto].

      unfold lblift_sub, mk_fresh_bterms; dands; allrw map_length; auto.
      introv i.
      repeat (rw @selectbt_map; auto; try omega).
      unfold approx_ext_starbts, lblift_sub in ap; repnd; allrw map_length; GC.
      pose proof (ap n i) as k; clear ap.
      repeat (rw @selectbt_map in k; auto; try omega).
      allunfold @selectbt.

      pose proof (in_nth_combine _ _ bs bs' n default_bt default_bt) as h.
      repeat (autodimp h hyp).
      remember (nth n bs default_bt)  as b1; clear Heqb1.
      remember (nth n bs' default_bt) as b2; clear Heqb2.
      allrw in_app_iff; allrw not_over_or; repnd.
      applydup in_combine in h; repnd.
      assert (!LIn a (get_utokens_b b1)) as niab1.
      { introv q; destruct ni3; rw lin_flat_map; eexists; dands; eauto. }
      assert (!LIn a (get_utokens_b b2)) as niab2.
      { introv q; destruct ni0; rw lin_flat_map; eexists; dands; eauto. }

(* new stuff *)

      apply (blift_sub_diff (v :: maybe_new_var_b v b1
                               :: maybe_new_var_b v b2
                               :: all_vars_bterm b1
                               ++ all_vars_bterm b2)) in k; exrepnd.
      allrw disjoint_cons_r; allrw disjoint_cons_l; allrw disjoint_app_r; allrw disjoint_app_l; repnd.

      assert (wf_term nt1) as wfnt1.
      { repndors; exrepnd.
        - allapply @approx_ext_star_relates_only_wf; repnd; eauto 2 with slow.
        - allapply @approx_ext_star_relates_only_wf; repnd.
          allapply @lsubst_nt_wf; eauto with slow. }

      assert (wf_term nt2) as wfnt2.
      { repndors; exrepnd.
        - allapply @approx_ext_star_relates_only_wf; repnd; eauto 2 with slow.
        - allapply @approx_ext_star_relates_only_wf; repnd.
          allapply @lsubst_nt_wf; eauto with slow. }

      pose proof (alpha_eq_subst_bterm_aux_pull_out_token b1 v a lv nt1) as exs1.
      repeat (autodimp exs1 hyp); exrepnd.
      subst nt1.
      rename u into nt1.

      pose proof (alpha_eq_subst_bterm_aux_pull_out_token b2 v a lv nt2) as exs2.
      repeat (autodimp exs2 hyp); exrepnd.
      subst nt2.
      rename u into nt2.

      assert (disjoint lv (bound_vars nt1)) as disjlvnt1.
      { introv i1 i2; apply k7 in i1; destruct i1.
        unfsubst.
        rw (bound_vars_lsubst_aux_nrut_sub nt1 [(v,mk_utoken a)] []); auto.
        apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp. }

      assert (disjoint lv (bound_vars nt2)) as disjlvnt2.
      { introv i1 i2; apply k8 in i1; destruct i1.
        unfsubst.
        rw (bound_vars_lsubst_aux_nrut_sub nt2 [(v,mk_utoken a)] []); auto.
        apply nrut_sub_cons; eexists; dands; simpl; eauto with slow; tcsp. }

      unfold blift_sub.

      pose proof (alpha_eq_bterm_mk_fresh_bterm_berm b1 v a lv nt1) as e1.
      repeat (autodimp e1 hyp); eauto 3 with slow.

      pose proof (alpha_eq_bterm_mk_fresh_bterm_berm b2 v a lv nt2) as e2.
      repeat (autodimp e2 hyp); eauto 3 with slow.

      exists lv (mk_fresh v nt1) (mk_fresh v nt2); dands; auto.

      (* here comes trouble! *)

      repndors;[left|right].

      * repnd; dands; auto.
        apply (apso _ _ _ _ [bterm [v] nt2]); allsimpl; auto; fold_terms;
        [|apply approx_ext_open_refl; allrw <- @nt_wf_eq;
          allapply @lsubst_nt_wf; apply nt_wf_fresh; auto].
        unfold lblift_sub; simpl; dands; auto; introv q; destruct n0; cpx.
        unfold selectbt; simpl.
        unfold blift_sub.

        exists [v] nt1 nt2; dands; auto.
        right.
        exists [(v,mk_utoken a)]; simpl; dands; auto.
        apply nrut_sub_cons; simpl; eexists; dands; eauto 3 with slow; tcsp.
        repeat (rw in_app_iff); sp.

      * exrepnd.

        pose proof (exists_nrut_sub
                      (dom_sub sub)
                      (a :: get_utokens_lib lib (subst nt1 v (mk_utoken a))
                         ++ get_utokens_lib lib (subst nt2 v (mk_utoken a))))
          as ens; exrepnd.

        pose proof (approx_ext_star_change_nrut_sub
                      lib
                      (subst nt1 v (mk_utoken a))
                      (subst nt2 v (mk_utoken a))
                      sub
                      (get_utokens_lib lib (subst nt1 v (mk_utoken a)) ++ get_utokens_lib lib (subst nt2 v (mk_utoken a)))
                      sub0
                      (a :: get_utokens_lib lib (subst nt1 v (mk_utoken a)) ++ get_utokens_lib lib (subst nt2 v (mk_utoken a))))
          as aps; repeat (autodimp aps hyp); eauto 5 with slow;[].

        exists sub0; dands; auto; simpl; allrw app_nil_r;
        try (complete (subst; auto));
        [|eapply nrut_sub_subset;[|exact ens1]; apply subset_cons1;
          apply subset_app_lr; introv z;
          apply get_utokens_lib_subst; boolvar; simpl;
          autorewrite with slow in *;
          repeat (rw app_nil_r); repeat (rw in_app_iff); tcsp;
          try (complete (unfold get_utokens_lib in *; allrw in_app_iff; tcsp))];[].

        repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow); simpl; fold_terms.
        apply (apso _ _ _ _ [bterm [v] (lsubst_aux nt2 (sub_filter sub0 [v]))]); allsimpl; auto; fold_terms;
        [|apply approx_ext_open_refl; allrw <- @nt_wf_eq;
          allapply @lsubst_nt_wf; apply nt_wf_fresh; auto;
          apply implies_wf_lsubst_aux; eauto 3 with slow];[].
        unfold lblift_sub; simpl; dands; auto; introv q; destruct n0; cpx.
        unfold selectbt; simpl.
        unfold blift_sub.

        allunfold @subst.
        rw (cl_lsubst_swap_sub_filter nt1) in aps; eauto 3 with slow.
        rw (cl_lsubst_swap_sub_filter nt2) in aps; eauto 3 with slow.
        allsimpl.

        assert (!LIn a (get_utokens_sub sub0)) as niasub.
        { intro z; unfold nrut_sub in ens1; repnd; allrw disjoint_cons_l; sp. }

        exists [v] (lsubst_aux nt1 (sub_filter sub0 [v])) (lsubst_aux nt2 (sub_filter sub0 [v])); dands; auto.
        right.
        exists [(v,mk_utoken a)]; simpl; dands; auto.
        { repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow). }
        apply nrut_sub_cons; simpl; eexists; dands; eauto 2 with slow; tcsp.

        rw in_app_iff; rw not_over_or; dands; intro z;
          apply get_utokens_lib_lsubst_aux_subset in z; rw in_app_iff in z; repndors; tcsp;
            try (apply get_utokens_sub_filter_subset in z; tcsp);
            try (complete (apply in_app_iff in z; repndors; tcsp)).
Qed.

Lemma alpha_eq_lsubst_nrut_sub_implies {o} :
  forall (t1 t2 : @NTerm o) sub l,
    nrut_sub l sub
    -> subset (get_utokens t1) l
    -> subset (get_utokens t2) l
    -> alpha_eq (lsubst t1 sub) (lsubst t2 sub)
    -> alpha_eq t1 t2.
Proof.
  introv nrut ss1 ss2 aeq.

  pose proof (unfold_lsubst sub t1) as p; destruct p as [t1']; repnd.
  pose proof (unfold_lsubst sub t2) as q; destruct q as [t2']; repnd.
  rw p in aeq; rw p2 in aeq.

  pose proof (change_bvars_alpha_wspec (dom_sub sub) t1') as h; destruct h as [t1'']; repnd.
  pose proof (change_bvars_alpha_wspec (dom_sub sub) t2') as k; destruct k as [t2'']; repnd.
  dup p5 as a1.
  apply (computation2.lsubst_aux_alpha_congr_same_cl_sub _ _ sub) in a1; eauto 2 with slow.
  dup p7 as a2.
  apply (computation2.lsubst_aux_alpha_congr_same_cl_sub _ _ sub) in a2; eauto 2 with slow.

  assert (alpha_eq (lsubst_aux t1'' sub) (lsubst_aux t2'' sub)) as aeq2 by eauto 4 with slow.

  pose proof (alpha_eq_lsubst_aux_nrut_sub_implies t1'' t2'' sub l) as a.
  repeat (autodimp a hyp).
  - apply alphaeq_preserves_utokens in p5; rw <- p5.
    apply alphaeq_preserves_utokens in p0; rw <- p0; auto.
  - apply alphaeq_preserves_utokens in p7; rw <- p7.
    apply alphaeq_preserves_utokens in p3; rw <- p3; auto.
  - assert (alpha_eq t1 t1'') as aeq11 by eauto 3 with slow.
    assert (alpha_eq t2 t2'') as aeq22 by eauto 3 with slow.
    eauto 4 with slow.
Qed.

Lemma reduces_in_atmost_k_steps_mk_fresh_id {o} :
  forall (lib : @library o) v k u,
    reduces_in_atmost_k_steps lib (mk_fresh v (vterm v)) u k
    -> u = mk_fresh v (vterm v).
Proof.
  induction k; introv r.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; allsimpl; boolvar; ginv.
    apply IHk in r0; auto.
Qed.

Lemma reduces_in_atmost_k_steps_mk_fresh_id2 {o} :
  forall (lib : @library o) v k,
    reduces_in_atmost_k_steps lib (mk_fresh v (vterm v)) (mk_fresh v (vterm v)) k.
Proof.
  induction k; introv.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    exists (@mk_fresh o v (vterm v)); dands; auto.
    csunf; simpl; boolvar; auto.
Qed.

Lemma isprog_vars_implies_nt_wf {o} :
  forall (t : @NTerm o) l, isprog_vars l t -> nt_wf t.
Proof.
  introv isp.
  rw @isprog_vars_eq in isp; sp.
Qed.
Hint Resolve isprog_vars_implies_nt_wf : slow.
