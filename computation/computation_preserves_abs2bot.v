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



Require Export computation8.
Require Export computation_preserves_lib.
Require Export atom_ren.
Require Export alphaeq5.


Definition abs2bot_op {o}
           (op : @Opid o)
           (bs : list BTerm) : NTerm :=
  match op with
  | Abs abs => mk_bot
  | _ => oterm op bs
  end.

Fixpoint abs2bot {o} (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => abs2bot (f n))
  | oterm op bs => abs2bot_op op (map abs2bot_bterm bs)
  end
with abs2bot_bterm {o} (b : @BTerm o) : BTerm :=
       match b with
       | bterm vs t => bterm vs (abs2bot t)
       end.

Lemma subset_nil_implies_nil :
  forall T (l : list T), subset l [] -> l = [].
Proof.
  introv ss.
  destruct l as [|x l]; allsimpl; auto.
  pose proof (ss x); allsimpl; tcsp.
Qed.
Hint Resolve subset_nil_implies_nil : slow.

Lemma implies_props_abs2bot {o} :
  forall (t : @NTerm o),
    (nt_wf t -> nt_wf (abs2bot t))
      # (subset (free_vars (abs2bot t)) (free_vars t))
      # (subset (get_utokens (abs2bot t)) (get_utokens t)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; dands; introv h; allsimpl; auto.

  - Case "sterm".
    inversion h as [|? imp|]; subst.
    constructor; introv.
    pose proof (imp n) as q; clear imp; repnd.
    pose proof (ind n) as z; clear ind; repnd.
    apply z0 in q0.
    rw q1 in z1.
    rw q in z.
    dands; auto.

    + unfold closed; eauto 3 with slow.

    + unfold noutokens; eauto 3 with slow.

  - Case "oterm".
    unfold abs2bot_op.
    inversion  h as [| |? ? imp e]; subst; clear h.

    destruct op; allsimpl; eauto 2 with slow;
    constructor; simpl; allrw map_map; allunfold @compose.

    + introv i; allrw in_map_iff; exrepnd; subst.
      destruct a as [l t]; simpl.
      applydup ind in i1; repnd.
      constructor.
      apply i2.
      apply imp in i1.
      allrw @bt_wf_iff. auto.

    + rw <- e.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl; auto.

    + introv i; allrw in_map_iff; exrepnd; subst.
      destruct a as [l t]; simpl.
      applydup ind in i1; repnd.
      constructor.
      apply i2.
      apply imp in i1.
      allrw @bt_wf_iff. auto.

    + rw <- e.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl; auto.

    + introv i; allrw in_map_iff; exrepnd; subst.
      destruct a as [l t]; simpl.
      applydup ind in i1; repnd.
      constructor.
      apply i2.
      apply imp in i1.
      allrw @bt_wf_iff. auto.

    + rw <- e.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl; auto.

  - Case "oterm".
    destruct op; allsimpl; tcsp; allrw lin_flat_map; exrepnd;
    allrw in_map_iff; exrepnd; subst;
    destruct a as [l t]; allsimpl;
    eexists; dands; eauto; allsimpl;
    allrw in_remove_nvars; repnd; dands; auto;
    apply ind in h1; repnd;
    apply h4 in h2; auto.

  - Case "oterm".
    destruct op; allsimpl; tcsp; allrw in_app_iff; repndors; tcsp;
    allrw lin_flat_map; exrepnd; try right;
    destruct x0 as [l t]; allsimpl;
    allrw in_map_iff; exrepnd;
    destruct a as [l1 t1]; allsimpl; ginv;
    applydup ind in h1; repnd;
    eexists; dands; eauto.
Qed.

Lemma isprog_sterm_abs2bot {o} :
  forall (f : @ntseq o),
    isprog (sterm f)
    -> isprog (sterm (fun n => abs2bot (f n))).
Proof.
  introv isp.
  allrw @isprog_eq.
  inversion isp as [cl wf].
  rw @nt_wf_sterm_iff in wf.
  apply nt_wf_sterm_implies_isprogram.
  apply wfst; introv.
  pose proof (wf n) as k; clear wf; repnd.
  pose proof (implies_props_abs2bot (f n)) as h; repnd.
  autodimp h0 hyp.
  rw k1 in h1.
  rw k in h.
  apply subset_nil_implies_nil in h1.
  apply subset_nil_implies_nil in h.
  dands; auto.
Qed.
Hint Resolve isprog_sterm_abs2bot : slow.

Lemma implies_isprog_abs2bot {o} :
  forall (t : @NTerm o),
    isprog t
    -> isprog (abs2bot t).
Proof.
  introv isp.
  allrw @isprog_eq.
  inversion isp as [cl wf].
  pose proof (implies_props_abs2bot t) as h; repnd.
  constructor; auto.
  rw cl in h1.
  apply subset_nil_implies_nil; auto.
Qed.
Hint Resolve implies_isprog_abs2bot : slow.

Lemma isnoncan_like_abs2bot {o} :
  forall (t : @NTerm o),
    isnoncan_like t -> isnoncan_like (abs2bot t).
Proof.
  destruct t as [v|f|op bs]; unfold isnoncan_like; simpl; tcsp.
  intro h.
  destruct op; tcsp.
Qed.
Hint Resolve isnoncan_like_abs2bot : slow.

Lemma eapply_wf_def_sterm {o} :
  forall (f : @ntseq o),
    eapply_wf_def (sterm f).
Proof.
  introv.
  unfold eapply_wf_def; left; eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_sterm : slow.

Fixpoint abs2bot_sub {o} (sub : @Sub o) : Sub :=
  match sub with
  | [] => []
  | (v,t) :: sub => (v,abs2bot t) :: abs2bot_sub sub
  end.

Lemma dec_op_abs {o} :
  forall (op : @Opid o),
    decidable {abs : opabs & op = Abs abs}.
Proof.
  introv; unfold decidable.
  dopid op as [can|ncan|exc|abs] Case; try (complete (right; sp; ginv)).
  left; exists abs; auto.
Qed.

Lemma abs2bot_op_eq {o} :
  forall op (bs : list (@BTerm o)),
    abs2bot_op op bs
    = if dec_op_abs op
      then mk_bot
      else oterm op bs.
Proof.
  introv.
  destruct op; boolvar; exrepnd; simpl; ginv; tcsp.
  destruct n; eexists; eauto.
Qed.

Hint Rewrite @lsubst_aux_allvars_preserves_osize2 : slow.

Lemma unfold_lsubst2 {o} :
  forall vars (sub : @Sub o) t,
    {t' : NTerm
     & alpha_eq t t'
     # disjoint (bound_vars t') (vars ++ sub_free_vars sub)
     # alpha_eq (lsubst t sub) (lsubst_aux t' sub)}.
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd.
  pose proof (change_bvars_alpha_wspec (vars ++ sub_free_vars sub) t') as q.
  destruct q as [t'' q]; repnd.
  exists t''; dands; eauto 3 with slow.
  rewrite h0.
  apply lsubst_aux_alpha_congr_same_disj; auto.
  allrw disjoint_app_l; repnd; eauto 3 with slow.
Qed.

Hint Rewrite @sub_free_vars_var_ren : hslow.
Hint Resolve disjoint_dom_sub_filt2 : slow.
Hint Resolve subset_sub_bound_vars_sub_filter : slow.

Definition abs2vbot_op {o}
           v
           (op : @Opid o)
           (bs : list BTerm) : NTerm :=
  match op with
  | Abs abs => mk_vbot v
  | _ => oterm op bs
  end.

Fixpoint abs2vbot {o} v (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => abs2vbot v (f n))
  | oterm op bs => abs2vbot_op v op (map (abs2vbot_bterm v) bs)
  end
with abs2vbot_bterm {o} v (b : @BTerm o) : BTerm :=
       match b with
       | bterm vs t => bterm vs (abs2vbot v t)
       end.

Lemma abs2vbot_op_eq {o} :
  forall v op (bs : list (@BTerm o)),
    abs2vbot_op v op bs
    = if dec_op_abs op
      then mk_vbot v
      else oterm op bs.
Proof.
  introv.
  destruct op; boolvar; exrepnd; simpl; ginv; tcsp.
  destruct n; eexists; eauto.
Qed.

Lemma abs2bot_as_abs2vbot {o} :
  forall (t : @NTerm o), abs2bot t = abs2vbot nvarx t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; allsimpl; tcsp.

  - Case "sterm".
    f_equal.
    apply functional_extensionality; introv; auto.

  - Case "oterm".
    rewrite abs2bot_op_eq.
    rewrite abs2vbot_op_eq.
    boolvar; auto.
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    f_equal.
    eapply ind; eauto.
Qed.

Fixpoint abs2vbot_sub {o} v (sub : @Sub o) : Sub :=
  match sub with
  | [] => []
  | (x,t) :: sub => (x,abs2vbot v t) :: abs2vbot_sub v sub
  end.

Lemma sub_find_abs2vbot_sub {o} :
  forall v (sub : @Sub o) x,
    sub_find (abs2vbot_sub v sub) x
    = match sub_find sub x with
      | Some t => Some (abs2vbot v t)
      | None => None
      end.
Proof.
  induction sub; simpl; introv; tcsp; repnd; allsimpl.
  boolvar; auto.
Qed.

Lemma sub_filter_abs2vbot_sub {o} :
  forall v (sub : @Sub o) l,
    sub_filter (abs2vbot_sub v sub) l
    = abs2vbot_sub v (sub_filter sub l).
Proof.
  induction sub; introv; simpl; auto.
  repnd; simpl; boolvar; simpl; auto.
  rewrite IHsub; auto.
Qed.

Lemma abs2vbot_lsubst_aux {o} :
  forall v (t : @NTerm o) sub,
    abs2vbot v (lsubst_aux t sub)
    = lsubst_aux (abs2vbot v t) (abs2vbot_sub v sub).
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case; introv; simpl; auto.

  - Case "vterm".
    rewrite sub_find_abs2vbot_sub.
    remember (sub_find sub x) as sf; symmetry in Heqsf; destruct sf; auto.

  - Case "oterm".
    repeat (rewrite abs2vbot_op_eq).
    boolvar; simpl; autorewrite with slow; auto.
    f_equal.
    allrw map_map; unfold compose; simpl.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    f_equal.
    rewrite sub_filter_abs2vbot_sub.
    eapply ind; eauto.
Qed.

Lemma abs2vbot_sub_var_ren {o} :
  forall v l1 l2, @abs2vbot_sub o v (var_ren l1 l2) = var_ren l1 l2.
Proof.
  induction l1; introv; simpl; auto.
  destruct l2; simpl; auto.
  fold (@var_ren o l1 l2).
  rewrite IHl1; auto.
Qed.
Hint Rewrite @abs2vbot_sub_var_ren : slow.

Lemma implies_alpha_eq_abs2vbot {o} :
  forall v1 v2 (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (abs2vbot v1 t1) (abs2vbot v2 t2).
Proof.
  nterm_ind1s t1 as [x|f ind|op bs ind] Case; introv aeq; allsimpl.

  - Case "vterm".
    inversion aeq; subst; simpl; auto.

  - Case "sterm".
    inversion aeq as [|? ? imp|]; clear aeq; subst; allsimpl.
    constructor.
    introv.
    apply ind; auto.

  - Case "oterm".
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    repeat (rewrite abs2vbot_op_eq).
    boolvar; eauto 3 with slow.

    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rewrite <- map_combine in i.
    apply in_map_iff in i; exrepnd; allsimpl; ginv.
    destruct a0 as [l1 t1].
    destruct a as [l2 t2]; allsimpl.

    applydup aeq0 in i1.

    pose proof (fresh_vars
                  (length l1)
                  ((all_vars t1)
                     ++ all_vars t2
                     ++ all_vars (abs2vbot v1 t1)
                     ++ all_vars (abs2vbot v2 t2))) as fv.
    exrepnd.
    allrw disjoint_app_r; repnd.

    apply (alphabt_change_var_aux _ _ _ _ lvn) in i0; auto;
    [|allrw disjoint_app_r; auto].
    repnd.

    apply (al_bterm_aux lvn); auto;
    [allrw disjoint_app_r; auto|].

    pose proof (ind t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as q; clear ind.
    autorewrite with slow in *.
    repeat (autodimp q hyp); eauto 3 with slow.
    apply q in i2; clear q.
    repeat (rewrite abs2vbot_lsubst_aux in i2).
    autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_alpha_eq_abs2vbot : slow.

Lemma implies_alphaeq_sub_abs2vbot_sub {o} :
  forall v1 v2 (sub1 sub2 : @Sub o),
    alphaeq_sub sub1 sub2
    -> alphaeq_sub (abs2vbot_sub v1 sub1) (abs2vbot_sub v2 sub2).
Proof.
  induction sub1; introv aeq; inversion aeq; subst; auto; clear aeq; simpl.
  constructor; eauto 3 with slow.
  apply alphaeq_eq.
  apply implies_alpha_eq_abs2vbot.
  apply alphaeq_eq; auto.
Qed.

Lemma abs2bot_sub_as_abs2vbot_sub {o} :
  forall (sub : @Sub o), abs2bot_sub sub = abs2vbot_sub nvarx sub.
Proof.
  induction sub; allsimpl; auto.
  repnd; allsimpl; rewrite IHsub.
  rewrite abs2bot_as_abs2vbot; auto.
Qed.

Lemma subset_free_vars_abs2vbot {o} :
  forall v (t : @NTerm o),
    subset (free_vars (abs2vbot v t)) (free_vars t).
Proof.
  nterm_ind1s t as [x|f ind|op bs ind] Case; simpl; auto.
  Case "oterm".
  rewrite abs2vbot_op_eq; boolvar; simpl; autorewrite with slow; auto.
  rewrite flat_map_map; unfold compose; simpl.
  apply subset_flat_map2; introv i.
  destruct x as [l t]; simpl.
  apply subvars_eq.
  apply implies_subvars_remove_nvars.
  apply subvars_eq.
  eapply ind; eauto 3 with slow.
Qed.

Lemma subset_bound_vars_abs2vbot {o} :
  forall v (t : @NTerm o),
    subset (bound_vars (abs2vbot v t)) (v :: bound_vars t).
Proof.
  nterm_ind1s t as [x|f ind|op bs ind] Case; simpl; auto.
  Case "oterm".
  rewrite abs2vbot_op_eq; boolvar; simpl; eauto 3 with slow.
  rewrite flat_map_map; unfold compose; simpl.
  apply subset_flat_map; introv i.
  destruct x as [l t]; simpl.
  rw subset_app; dands.
  - apply subset_cons1.
    introv j; rw lin_flat_map; eexists; dands; eauto.
    simpl; rw in_app_iff; sp.
  - introv j.
    eapply ind in j; eauto 3 with slow.
    allsimpl; repndors; tcsp.
    right; apply lin_flat_map.
    eexists; dands; eauto.
    simpl; apply in_app_iff; sp.
Qed.

Lemma subset_sub_free_vars_abs2vbot_sub {o} :
  forall v (sub : @Sub o),
    subset (sub_free_vars (abs2vbot_sub v sub)) (sub_free_vars sub).
Proof.
  induction sub; simpl; auto.
  repnd; allsimpl.
  apply subset_app_lr; auto.
  apply subset_free_vars_abs2vbot.
Qed.

Lemma abs2bot_lsubst {o} :
  forall (t : @NTerm o) sub,
    alpha_eq
      (abs2bot (lsubst t sub))
      (lsubst (abs2bot t) (abs2bot_sub sub)).
Proof.
  introv.

  pose proof (ex_fresh_var (sub_free_vars sub)) as fv; exrepnd.
  repeat (rewrite abs2bot_as_abs2vbot).

  eapply alpha_eq_trans;
    [apply (implies_alpha_eq_abs2vbot _ v _ (lsubst t sub));
      eauto 3 with slow|].

  pose proof (unfold_lsubst sub t) as q; exrepnd; allsimpl.
  rewrite q0; clear q0.

  rewrite abs2bot_sub_as_abs2vbot_sub.

  eapply alpha_eq_trans;
    [|apply lsubst_alpha_congr3;
       [apply alpha_eq_refl
       |apply (implies_alphaeq_sub_abs2vbot_sub v _ sub _);
         eauto 3 with slow]
    ].

  pose proof (unfold_lsubst (abs2vbot_sub v sub) (abs2vbot nvarx t)) as h; exrepnd.
  rewrite h0; clear h0.

  rewrite abs2vbot_lsubst_aux.

  apply lsubst_aux_alpha_congr_same_disj;auto;[eauto 4 with slow|];[].

  eapply subset_disjoint;[apply subset_bound_vars_abs2vbot|].

  eapply subset_disjoint_r;[|apply subset_sub_free_vars_abs2vbot_sub].
  apply disjoint_cons_l; dands; auto.
Qed.

Lemma isexc_abs2bot {o} :
  forall (t : @NTerm o), isexc t -> isexc (abs2bot t).
Proof.
  introv ise.
  apply isexc_implies2 in ise; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve isexc_abs2bot : slow.

Definition same_sign_bs {o} (bs1 bs2 : list (@BTerm o)) :=
  map num_bvars bs1 = map num_bvars bs2.

Definition same_sign_bs_abs2bot {o} :
  forall (bs : list (@BTerm o)),
    same_sign_bs bs (map abs2bot_bterm bs).
Proof.
  introv; unfold same_sign_bs.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t]; unfold num_bvars; simpl; auto.
Qed.
Hint Resolve same_sign_bs_abs2bot : slow.

Lemma eapply_wf_def_oterm_change_bs {o} :
  forall (op : @Opid o) bs1 bs2,
   same_sign_bs bs1 bs2
    -> eapply_wf_def (oterm op bs1)
    -> eapply_wf_def (oterm op bs2).
Proof.
  introv len eap.
  allunfold @eapply_wf_def; repndors; exrepnd;
  allunfold @mk_nseq; allunfold @mk_lam; ginv.

  - unfold same_sign_bs in len; allsimpl.
    destruct bs2; allsimpl; ginv; eauto.

  - unfold same_sign_bs in len; allsimpl.
    unfold num_bvars in len; allsimpl.
    destruct bs2 as [|bt l]; allsimpl; ginv.
    destruct l; allsimpl; ginv.
    destruct bt as [l t]; allsimpl.
    destruct l as [|x l]; allsimpl; ginv.
    destruct l; ginv; eauto.
Qed.
Hint Resolve eapply_wf_def_oterm_change_bs : slow.

Lemma isvalue_like_abs2bot {o} :
  forall (t : @NTerm o), isvalue_like t -> isvalue_like (abs2bot t).
Proof.
  introv i.
  apply isvalue_like_implies_or1 in i.
  unfold is_can_or_exc in i; repndors.
  - apply iscan_implies in i; repndors; exrepnd; subst; simpl; eauto 3 with slow.
  - apply isexc_implies2 in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve isvalue_like_abs2bot : slow.

Lemma alpha_eq_mk_fresh_not_in {o} :
  forall v1 v2 (t : @NTerm o),
    !LIn v1 (free_vars t)
    -> !LIn v2 (free_vars t)
    -> alpha_eq (mk_fresh v1 t) (mk_fresh v2 t).
Proof.
  introv ni1 ni2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv h; repndors; tcsp; ginv.
  apply alpha_eq_bterm_bterm_disjoint;
    try (apply disjoint_singleton_l); auto.
Qed.
Hint Resolve alpha_eq_mk_fresh_not_in : slow.

Lemma  pushdown_fresh_abs2bot {o} :
  forall n (t : @NTerm o),
    isvalue_like t
    -> alpha_eq
         (pushdown_fresh n (abs2bot t))
         (abs2bot (pushdown_fresh n t)).
Proof.
  introv isv.
  unfold pushdown_fresh.
  destruct t as [v|f|op bs]; simpl; auto.
  repeat (rewrite abs2bot_op_eq).
  boolvar; simpl; auto.

  - exrepnd; subst.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - unfold mk_fresh_bterms.
    allrw map_map; unfold compose; simpl.
    apply alpha_eq_oterm_combine2.
    autorewrite with slow.
    dands; auto.
    introv i.
    rewrite <- map_combine in i.
    apply in_map_iff in i; exrepnd; ginv.
    apply in_combine_same in i1; repnd; subst.
    destruct a as [l t]; allsimpl.
    apply alpha_eq_bterm_congr; fold_terms.

    unfold maybe_new_var; boolvar; auto.

    pose proof (newvar_prop (abs2bot t)) as k.
    remember (newvar (abs2bot t)) as nv1; clear Heqnv1.

    pose proof (newvar_prop t) as h.
    remember (newvar t) as nv2; clear Heqnv2.

    assert (!LIn nv2 (free_vars (abs2bot t))) as j.
    {
      intro j.
      pose proof (implies_props_abs2bot t) as z; repnd.
      apply z1 in j; auto.
    }

    eauto 3 with slow.
Qed.

Lemma implies_nt_wf_abs2bot {o} :
  forall (t : @NTerm o), nt_wf t -> nt_wf (abs2bot t).
Proof.
  introv.
  pose proof (implies_props_abs2bot t); tcsp.
Qed.
Hint Resolve implies_nt_wf_abs2bot : slow.

Fixpoint abs2vbot_utok_sub {o} v (sub : @utok_sub o) : utok_sub :=
  match sub with
  | [] => []
  | (x,t) :: sub => (x,abs2vbot v t) :: abs2vbot_utok_sub v sub
  end.

Fixpoint abs2bot_utok_sub {o} (sub : @utok_sub o) : utok_sub :=
  match sub with
  | [] => []
  | (x,t) :: sub => (x,abs2bot t) :: abs2bot_utok_sub sub
  end.

Lemma utoks_sub_find_abs2vbot_utok_sub {o} :
  forall v (sub : @utok_sub o) a,
    utok_sub_find (abs2vbot_utok_sub v sub) a
    = match utok_sub_find sub a with
      | Some t => Some (abs2vbot v t)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; auto.
  repnd; simpl; boolvar; auto.
Qed.

Lemma abs2vbot_subst_utokens_aux {o} :
  forall v (t : @NTerm o) sub,
    abs2vbot v (subst_utokens_aux t sub)
    = subst_utokens_aux (abs2vbot v t) (abs2vbot_utok_sub v sub).
Proof.
  nterm_ind t as [x|f ind|op bs ind] Case; introv; auto.

  Case "oterm".
  rewrite subst_utokens_aux_oterm.
  simpl.
  repeat (rewrite abs2vbot_op_eq).
  boolvar; try (rewrite subst_utokens_aux_oterm); simpl.

  - exrepnd; subst; simpl; auto.

  - remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; simpl;
    allrw @map_map; unfold compose.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      rewrite utoks_sub_find_abs2vbot_utok_sub.
      remember (utok_sub_find sub g) as f; symmetry in Heqf; destruct f; auto.
      simpl.
      f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl.
      f_equal; eauto.

    + rewrite abs2vbot_op_eq; boolvar; tcsp; GC.
      f_equal.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl.
      f_equal; eauto.
Qed.

Lemma abs2bot_utok_sub_as_abs2vbot_utok_sub {o} :
  forall (sub : @utok_sub o), abs2bot_utok_sub sub = abs2vbot_utok_sub nvarx sub.
Proof.
  induction sub; allsimpl; auto.
  repnd; allsimpl; rewrite IHsub.
  rewrite abs2bot_as_abs2vbot; auto.
Qed.

Lemma implies_alphaeq_utok_sub_abs2vbot_utok_sub {o} :
  forall v1 v2 (sub1 sub2 : @utok_sub o),
    alphaeq_utok_sub sub1 sub2
    -> alphaeq_utok_sub (abs2vbot_utok_sub v1 sub1) (abs2vbot_utok_sub v2 sub2).
Proof.
  induction sub1; introv aeq; inversion aeq; subst; auto; clear aeq; simpl.
  constructor; eauto 3 with slow.
  apply alphaeq_eq.
  apply implies_alpha_eq_abs2vbot.
  apply alphaeq_eq; auto.
Qed.

Lemma subset_free_vars_utok_sub_abs2vbot_utok_sub {o} :
  forall v (sub : @utok_sub o),
    subset
      (free_vars_utok_sub (abs2vbot_utok_sub v sub))
      (free_vars_utok_sub sub).
Proof.
  induction sub; simpl; auto.
  repnd; allsimpl.
  apply subset_app_lr; auto.
  apply subset_free_vars_abs2vbot.
Qed.

Lemma abs2bot_subst_utokens {o} :
  forall (t : @NTerm o) sub,
    alpha_eq
      (abs2bot (subst_utokens t sub))
      (subst_utokens (abs2bot t) (abs2bot_utok_sub sub)).
Proof.
  introv.

  pose proof (ex_fresh_var (free_vars_utok_sub sub)) as fv; exrepnd.
  repeat (rewrite abs2bot_as_abs2vbot).

  eapply alpha_eq_trans;
    [apply (implies_alpha_eq_abs2vbot _ v _ (subst_utokens t sub));
      eauto 3 with slow|].

  pose proof (unfold_subst_utokens sub t) as q; exrepnd; allsimpl.
  rewrite q0; clear q0.

  rewrite abs2bot_utok_sub_as_abs2vbot_utok_sub.

  eapply alpha_eq_trans;
    [|apply alpha_eq_subst_utokens;
       [apply alpha_eq_refl
       |apply (implies_alphaeq_utok_sub_abs2vbot_utok_sub v _ sub _);
         eauto 3 with slow]
    ].

  pose proof (unfold_subst_utokens (abs2vbot_utok_sub v sub) (abs2vbot nvarx t)) as h; exrepnd.
  rewrite h0; clear h0.

  rewrite abs2vbot_subst_utokens_aux.

  apply alpha_eq_subst_utokens_aux;eauto 4 with slow.

  eapply subset_disjoint_r;[|apply subset_bound_vars_abs2vbot].

  eapply subset_disjoint;[apply subset_free_vars_utok_sub_abs2vbot_utok_sub|].
  apply disjoint_cons_r; dands; eauto 3 with slow.
Qed.

Hint Resolve wf_term_subst : slow.

Lemma compute_step_abs2bot {o} :
  forall (t : @NTerm o) u,
    wf_term t
    -> compute_step [] t = csuccess u
    -> {w : NTerm
        & compute_step [] (abs2bot t) = csuccess w
        # alpha_eq w (abs2bot u)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf comp.

  - Case "vterm".
    csunf; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; auto.
    eexists; csunf; simpl; dands; eauto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; auto.
      eexists; csunf; simpl; dands; eauto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            csunf; simpl; auto.
            eexists; dands; eauto.
          }

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv.
              csunf; simpl.
              dcwf h; simpl.
              boolvar; try lia.
              rewrite Znat.Nat2Z.id; auto.
              eexists; dands; eauto.

            + csunf; simpl.
              apply isexc_implies2 in comp0; exrepnd; subst.
              dcwf h; simpl; auto.
              eexists; dands; eauto.

            + fold_terms.
              rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.
              pose proof (ind arg2 arg2 []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              apply wf_term_eapply_iff in wf; exrepnd; allunfold @nobnd; ginv.
              apply h in comp1; clear h; auto.
              exrepnd; rewrite comp1.
              eexists; dands; eauto.
              simpl; repeat prove_alpha_eq4.
          }

          {
            SSCase "NFix".
            apply compute_step_fix_success in comp; repnd; subst.
            csunf; simpl; auto.
            eexists; dands; eauto.
          }

          {
            SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst.
            csunf; simpl; auto.
            eexists; dands; eauto.
            eapply alpha_eq_trans;[|apply alpha_eq_sym; apply abs2bot_lsubst]; auto.
          }

          {
            SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
            csunf; simpl.
            eexists; dands; eauto.
          }

          {
            SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.
            csunf; simpl.
            eexists; dands; eauto.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto; csunf; simpl; eexists; dands; eauto.
              eapply alpha_eq_trans;[|apply alpha_eq_sym; apply abs2bot_lsubst]; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto;
                  eexists; dands; eauto;
                  eapply alpha_eq_trans;
                  try (apply alpha_eq_sym; apply abs2bot_lsubst); auto.

                + unfold mk_nseq in *; allsimpl; ginv; GC.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try lia.
                  rewrite Znat.Nat2Z.id; auto.
                  eexists; dands; eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply wf_term_eapply_iff in wf; exrepnd; allunfold @nobnd; ginv.
                apply q in comp1; clear q; auto.
                exrepnd; rewrite comp1; auto.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
              eapply alpha_eq_trans;[|apply alpha_eq_sym; apply abs2bot_lsubst]; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
              eapply alpha_eq_trans;[|apply alpha_eq_sym; apply abs2bot_lsubst]; auto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto;
              csunf; simpl; eexists; dands; eauto;
              eapply alpha_eq_trans;
              try (apply alpha_eq_sym; apply abs2bot_lsubst); auto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
              eapply alpha_eq_trans;
                try (apply alpha_eq_sym; apply abs2bot_lsubst); auto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_sleep; simpl.
              eexists; dands; eauto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try lia.
              rewrite Znat.Nat2Z.id; auto.
              eexists; dands; eauto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_minus; simpl.
              eexists; dands; eauto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              eexists; dands; eauto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_parallel.
              eexists; dands; eauto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; simpl.

              - csunf; simpl.
                dcwf h.
                apply compute_step_compop_success_can_can in comp1; exrepnd; subst; ginv; GC.
                repndors; exrepnd; subst; allsimpl;
                unfold compute_step_comp; allrw;
                eexists; dands; eauto;
                boolvar; auto.

              - rewrite compute_step_ncompop_ncanlike2; eauto 3 with slow.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allrw @wf_term_ncompop_iff; exrepnd; ginv.
                apply q in comp4; clear q; auto.
                exrepnd.
                rewrite comp2; auto.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp; allsimpl.

              - csunf; simpl.
                dcwf h.
                apply compute_step_arithop_success_can_can in comp1; exrepnd; subst; ginv; GC.
                repndors; exrepnd; subst; allsimpl;
                unfold compute_step_comp; allrw;
                eexists; dands; eauto;
                boolvar; auto.

              - rewrite compute_step_narithop_ncanlike2; eauto 3 with slow.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                allrw @wf_term_narithop_iff; exrepnd; ginv.
                apply q in comp4; clear q; auto.
                exrepnd.
                rewrite comp2; auto.
                eexists; dands; eauto.
                repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              eexists; dands; eauto.
              destruct (canonical_form_test_for c can2); auto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step [] (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind
                          (oterm (NCan ncan2) bts)
                          (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.

            applydup @wf_oterm_iff in wf; repnd.
            pose proof (wf0 (bterm [] (oterm (NCan ncan2) bts))) as wfn; allsimpl.
            autodimp wfn hyp.
            allrw @wf_bterm_iff.

            apply q in Heqc; clear q; auto.
            exrepnd.
            csunf; allsimpl.
            rewrite Heqc1; auto; simpl.
            eexists; dands; eauto.
            repeat prove_alpha_eq4.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.
              eexists; dands; eauto.
              unfold mk_atom_eq.
              repeat prove_alpha_eq4.
              eapply alpha_eq_trans;
                try (apply alpha_eq_sym; apply abs2bot_lsubst); auto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.
              eexists; dands; eauto.

          + SSCase "Abs".

            csunf comp; allsimpl; ginv.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.
          eexists; dands; eauto.

        - rewrite compute_step_fresh_if_isvalue_like2; simpl; eauto 3 with slow.
          eexists; dands; eauto.
          apply pushdown_fresh_abs2bot; auto.

        - rewrite compute_step_fresh_if_isnoncan_like; simpl; eauto 3 with slow.

          allrw @wf_fresh_iff.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q; eauto 3 with slow;[].
          exrepnd; allsimpl.

          pose proof (abs2bot_lsubst t [(n,mk_utoken (get_fresh_atom t))]) as aeq.
          pose proof (compute_step_alpha
                        []
                        (abs2bot (lsubst t [(n, mk_utoken (get_fresh_atom t))]))
                        (lsubst (abs2bot t) (abs2bot_sub [(n, mk_utoken (get_fresh_atom t))]))
                        w) as comp.
          repeat (autodimp comp hyp).
          { apply implies_nt_wf_abs2bot.
            apply nt_wf_subst; eauto 2 with slow. }
          exrepnd; allsimpl.
          fold_terms; allrw @fold_subst.

          assert (!LIn (get_fresh_atom t) (get_utokens (abs2bot t))) as ni1.
          {
            intro h.
            pose proof (implies_props_abs2bot t) as q; repnd.
            apply q in h.
            apply get_fresh_atom_prop in h; tcsp.
          }

          assert (!LIn (get_fresh_atom (abs2bot t)) (get_utokens (abs2bot t))) as ni2.
          {
            intro h.
            apply get_fresh_atom_prop in h; tcsp.
          }

          pose proof (compute_step_subst_utoken
                        []
                        (abs2bot t)
                        t2'
                        [(n, mk_utoken (get_fresh_atom t))]) as comp'.
          repeat (autodimp comp' hyp); simpl; eauto 3 with slow.

          { unfold get_utokens_sub; simpl.
            apply disjoint_singleton_l; auto. }

          exrepnd; allsimpl.

          pose proof (comp'0 [(n, mk_utoken (get_fresh_atom (abs2bot t)))]) as comp''.
          allsimpl.
          repeat (autodimp comp'' hyp); eauto 3 with slow.

          { unfold get_utokens_sub; simpl.
            apply disjoint_singleton_l; auto. }

          exrepnd; allsimpl.
          allrw @fold_subst.
          rewrite comp''1; simpl.
          eexists; dands; eauto.

          apply implies_alpha_eq_mk_fresh.

          rename comp''0 into aeq1.
          assert (alpha_eq (subst w0 n (mk_utoken (get_fresh_atom t))) (abs2bot x)) as aeq2.
          { eauto 4 with slow. }

          unfold get_utokens_sub in *; allsimpl.
          allrw disjoint_singleton_l.

          eapply alpha_eq_trans;
            [|apply alpha_eq_sym; apply abs2bot_subst_utokens].
          simpl.

          eapply alpha_eq_trans;
            [apply alpha_eq_subst_utokens_same;exact aeq1|].

          eapply alpha_eq_trans;
            [apply simple_alphaeq_subst_utokens_subst;
              intro i; apply comp'4 in i; auto|].

          eapply alpha_eq_trans;
            [|apply alpha_eq_subst_utokens_same;exact aeq2].

          eapply alpha_eq_trans;
            [|apply alpha_eq_sym;apply simple_alphaeq_subst_utokens_subst;auto].

          auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.
      csunf; simpl.
      eexists; dands; eauto.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.
      unfold found_entry in comp0; allsimpl; ginv.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
