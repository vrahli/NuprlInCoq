(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export computation3.


Lemma oappl_OLL_cons {T} :
  forall l : list (OList T),
    oappl (OLL [] :: l) = oappl l.
Proof. sp. Qed.
Hint Rewrite @oappl_OLL_cons : slow.

Lemma oeqset_osubset {T} :
  forall (o1 o2 o3 : OList T),
    oeqset o1 o2 -> osubset o2 o3 -> osubset o1 o3.
Proof.
  introv h1 h2.
  eapply osubset_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma subset_not_in :
  forall (T : tuniv) (s1 s2 : list T) (x : T),
    subset s1 s2 -> !LIn x s2 -> !LIn x s1.
Proof.
  introv ss h i.
  apply ss in i; sp.
Qed.

Definition get_utokens_step_seq_arg1 {o}
           (f : @ntseq o)
           (t : @NTerm o) :=
  match t with
    | oterm (Can (Nint z)) _ =>
      if Z_le_gt_dec 0 z
      then get_utokens_step_seq (f (Z.to_nat z))
      else []
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_arg1 {o} :
  forall (f : @ntseq o)
         (t : @NTerm o),
    match t with
      | oterm (Can (Nint z)) _ =>
        if Z_le_gt_dec 0 z
        then get_utokens_step_seq (f (Z.to_nat z))
        else []
      | _ => []
    end = get_utokens_step_seq_arg1 f t.
Proof. sp. Qed.

Definition get_utokens_step_seq_bterm {o}
           (f : @ntseq o)
           (b : @BTerm o) :=
  match b with
    | bterm [] (oterm (Can (Nint z)) _) =>
      if Z_le_gt_dec 0 z
      then get_utokens_step_seq (f (Z.to_nat z))
      else []
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_bterm {o} :
  forall (f : @ntseq o)
         (b : @BTerm o),
    match b with
      | bterm [] (oterm (Can (Nint z)) _) =>
        if Z_le_gt_dec 0 z
        then get_utokens_step_seq (f (Z.to_nat z))
        else []
      | _ => []
    end = get_utokens_step_seq_bterm f b.
Proof. sp. Qed.

Definition get_utokens_step_seq_bterms {o}
           (f  : @ntseq o)
           (bs : list (@BTerm o)) :=
  match bs with
    | bterm [] (oterm (Can (Nint z)) _) :: _ =>
      if Z_le_gt_dec 0 z
      then get_utokens_step_seq (f (Z.to_nat z))
      else []
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_bterms {o} :
  forall f (bs : list (@BTerm o)),
    match bs with
      | bterm [] (oterm (Can (Nint z)) _) :: _ =>
        if Z_le_gt_dec 0 z
        then get_utokens_step_seq (f (Z.to_nat z))
        else []
      | _ => []
    end = get_utokens_step_seq_bterms f bs.
Proof. sp. Qed.

Definition get_utokens_step_seq_ncan {o}
           (f    : @ntseq o)
           (ncan : NonCanonicalOp)
           (bs   : list (@BTerm o)) :=
  match ncan with
    | NApply  => get_utokens_step_seq_bterms f bs
    | NEApply => get_utokens_step_seq_bterms f bs
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_ncan {o} :
  forall f ncan (bs : list (@BTerm o)),
    match ncan with
      | NApply  => get_utokens_step_seq_bterms f bs
      | NEApply => get_utokens_step_seq_bterms f bs
      | _ => []
    end = get_utokens_step_seq_ncan f ncan bs.
Proof. sp. Qed.

Lemma lsubst_aux_equal_mk_nat {o} :
  forall lib (t : @NTerm o) sub n u,
    nr_ut_sub lib u sub
    -> lsubst_aux t sub = mk_nat n
    -> t = mk_nat n.
Proof.
  introv nrut e.
  destruct t as [v|op bs]; allsimpl; ginv.
  - remember (sub_find sub v) as  sf; symmetry in Heqsf; destruct sf; subst; ginv.
    eapply nr_ut_some_implies in Heqsf; eauto; exrepnd; ginv.
  - inversion e as [e1]; subst; clear e.
    destruct bs; allsimpl; ginv.
Qed.

Lemma oappl_OLS_singleton {T} :
  forall (f : nat -> OList T), oappl [OLS f] = OLS f.
Proof. sp. Qed.
Hint Rewrite @oappl_OLS_singleton : slow.

Lemma nt_wf_Exc {o} :
  forall (bs : list (@BTerm o)),
    nt_wf (oterm Exc bs)
    <=> {a : NTerm
         & {b : NTerm
         & bs = [nobnd a, nobnd b]
         # nt_wf a
         # nt_wf b}}.
Proof.
  introv; split; intro h.
  - inversion h as [|? ? imp]; subst; allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    pose proof (imp (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (imp (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; dands; eauto.
  - exrepnd; subst.
    constructor; simpl; tcsp.
    introv i; repndors; subst; tcsp; apply bt_wf_iff; auto.
Qed.

Lemma nt_wf_NFix {o} :
  forall (bs : list (@BTerm o)),
    nt_wf (oterm (NCan NFix) bs)
    <=> {a : NTerm
         & bs = [nobnd a]
         # nt_wf a}.
Proof.
  introv; split; intro h.
  - inversion h as [|? ? imp]; subst; allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    destruct l1; allsimpl; ginv.
    pose proof (imp (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; dands; eauto.
  - exrepnd; subst.
    constructor; simpl; tcsp.
    introv i; repndors; subst; tcsp; apply bt_wf_iff; auto.
Qed.

Lemma wf_isexc_implies {o} :
  forall (t : @NTerm o),
    nt_wf t
    -> isexc t
    -> {a, e : NTerm $ t = mk_exception a e}.
Proof.
  introv wf ise.
  unfold isexc in ise.
  destruct t as [v|op bs]; allsimpl; tcsp.
  destruct op as [can|ncan|exc|abs]; allsimpl; tcsp; GC.
  apply nt_wf_Exc in wf; exrepnd; subst.
  eexists; eexists; reflexivity.
Qed.

Lemma nt_wf_NCbv {o} :
  forall (bs : list (@BTerm o)),
    nt_wf (oterm (NCan NCbv) bs)
    <=> {v : NVar
         & {a : NTerm
         & {b : NTerm
         & bs = [nobnd a, bterm [v] b]
         # nt_wf a
         # nt_wf b }}}.
Proof.
  introv; split; intro h.
  - inversion h as [|? ? imp]; subst; allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    destruct l1; allsimpl; ginv.
    destruct l2 as [|v l2]; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    pose proof (imp (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (imp (bterm [v] t2)) as h2; autodimp h2 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; dands; eauto.
  - exrepnd; subst.
    constructor; simpl; tcsp.
    introv i; repndors; subst; tcsp; apply bt_wf_iff; auto.
Qed.

Lemma nt_wf_NTryCatch {o} :
  forall (bs : list (@BTerm o)),
    nt_wf (oterm (NCan NTryCatch) bs)
    <=> {v : NVar
         & {a : NTerm
         & {b : NTerm
         & {c : NTerm
         & bs = [nobnd a, nobnd b, bterm [v] c]
         # nt_wf a
         # nt_wf b
         # nt_wf c }}}}.
Proof.
  introv; split; intro h.
  - inversion h as [|? ? imp]; subst; allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    destruct b1 as [l3 t3].
    destruct l1; allsimpl; ginv.
    destruct l2; allsimpl; ginv.
    destruct l3 as [|v l3]; allsimpl; ginv.
    destruct l3; allsimpl; ginv.
    pose proof (imp (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (imp (bterm [] t2)) as h2; autodimp h2 hyp.
    pose proof (imp (bterm [v] t3)) as h3; autodimp h3 hyp.
    allrw @bt_wf_iff.
    unfold nobnd.
    eexists; eexists; eexists; eexists; dands; eauto.
  - exrepnd; subst.
    constructor; simpl; tcsp.
    introv i; repndors; subst; tcsp; apply bt_wf_iff; auto.
Qed.

Lemma get_cutokens_onil_eq {o} :
  forall (t : @NTerm o),
    oapp (get_cutokens t) onil = get_cutokens t.
Proof.
  introv; rw <- @get_cutokens_onil; auto.
Qed.
Hint Rewrite @get_cutokens_onil_eq : slow.

Lemma iscan_lsubst_aux_nr_ut_sub_eq_doms {o} :
  forall lib (t u : @NTerm o) sub sub',
    nr_ut_sub lib u sub
    -> nr_ut_sub lib u sub'
    -> dom_sub sub = dom_sub sub'
    -> iscan (lsubst_aux t sub)
    -> iscan (lsubst_aux t sub').
Proof.
  introv nrut1 nrut2 eqdoms isc.
  destruct t as [v|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
  pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' v u) as h.
  repeat (autodimp h hyp).
  rw Heqsf in h; exrepnd.
  rw h0; simpl; tcsp.
Qed.
Hint Resolve iscan_lsubst_aux_nr_ut_sub_eq_doms : slow.

Lemma osubset_oapp_left_iff {T} :
  forall o o1 o2 : OList T,
    osubset (oapp o1 o2) o <=> (osubset o1 o # osubset o2 o).
Proof.
  introv; split; intro h; repnd; try (apply osubset_oapp_left; auto).
  dands; introv i; apply h; apply in_olist_oapp; sp.
Qed.

Lemma subset_flat_map_get_utokens_b {o} :
  forall (l : list (@BTerm o)),
    subset (flat_map get_utokens_b l)
           (flat_map get_utokens_step_seq_b l).
Proof.
  introv.
  apply subset_flat_map2; introv i.
  destruct x; simpl; eauto 3 with slow.
Qed.
Hint Resolve subset_flat_map_get_utokens_b : slow.

Definition ncan_nil {T} (ncan : NonCanonicalOp) : list T :=
  match ncan with
    | NApply => []
    | _ => []
  end.

Lemma fold_ncan_nil {T} :
  forall ncan,
    match ncan with
      | NApply => []
      | _ => []
    end = ([] : list T).
Proof.
  introv; destruct ncan; sp.
Qed.
Hint Rewrite @fold_ncan_nil : slow.

Lemma sub_find_sub_filter_singleton_eq {o} :
  forall (sub : @Sub o) (v : NVar),
    sub_find (sub_filter sub [v]) v = None.
Proof.
  introv.
  rw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; auto.
Qed.
Hint Rewrite @sub_find_sub_filter_singleton_eq : slow.

Lemma subset_get_utokens_step_seq_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_step_seq t) (get_utokens_step_seq (lsubst_aux t sub)).
Proof.
  nterm_ind1 t as [v ind|op bs ind] Case; introv; simpl; auto.
  Case "oterm".
  allrw subset_app; dands; eauto 3 with slow.
  - apply subset_app_l.
    allrw flat_map_map; unfold compose.
    apply subset_flat_map2; introv i.
    destruct x as [l t]; allsimpl.
    eapply ind; eauto.
Qed.

Definition is_utok_sub {o} (sub : @Sub o) :=
  forall v t, LIn (v,t) sub -> is_utok t.

Lemma is_utok_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    is_utok_sub ((v, t) :: sub) <=> (is_utok t # is_utok_sub sub).
Proof.
  introv.
  unfold is_utok_sub; simpl; split; introv h; repnd; dands; introv.
  - eapply h; eauto.
  - intro i; eapply h; eauto.
  - intro i; repndors; ginv; auto.
    eapply h; eauto.
Qed.

Lemma in_is_utok_sub {o} :
  forall (sub : @Sub o) v t,
    is_utok_sub sub
    -> LIn (v, t) sub
    -> is_utok t.
Proof.
  introv i j; apply i in j; auto.
Qed.

Lemma implies_is_utok_sub {o} :
  forall (sub : @Sub o) l, is_utok_sub sub -> is_utok_sub (sub_filter sub l).
Proof.
  introv isu i.
  allrw @in_sub_filter; repnd.
  apply isu in i0; sp.
Qed.
Hint Resolve implies_is_utok_sub : slow.

Lemma eqset_flat_map_get_utokens_step_seq_b_is_utok_sub {o} :
  forall (bs : list (@BTerm o)) sub,
    (forall (nt nt' : NTerm) (lv : list NVar),
       LIn (bterm lv nt) bs
       -> (osize nt') <=< (osize nt)
       -> forall sub : @Sub o,
            is_utok_sub sub
            -> eqset (get_utokens_step_seq (lsubst_aux nt' sub))
                     (get_utokens_step_seq nt' ++ get_utokens_sub (sub_keep_first sub (free_vars nt'))))
    -> is_utok_sub sub
    -> eqset
         (flat_map get_utokens_step_seq_b
                   (map (fun t => lsubst_bterm_aux t sub) bs))
         (flat_map get_utokens_step_seq_b bs ++
                   get_utokens_sub (sub_keep_first sub (flat_map free_vars_bterm bs))).
Proof.
  introv ind isu.
  allrw flat_map_map; unfold compose.
  introv; split; intro i.

  - rw lin_flat_map in i; exrepnd.
    destruct x0 as [l t]; allsimpl.
    eapply ind in i0; eauto 3 with slow.
    allrw in_app_iff; repndors.

    { left.
      rw lin_flat_map.
      eexists; dands; eauto. }

    { right.
      allrw @in_get_utokens_sub; exrepnd.
      exists v t0; dands; auto.
      allrw @in_sub_keep_first; repnd.
      allrw @sub_find_sub_filter_some; repnd; dands; auto.
      rw lin_flat_map.
      eexists; dands; eauto; simpl.
      allrw in_remove_nvars; dands; auto. }

  - allrw in_app_iff; allrw lin_flat_map.
    repndors; exrepnd.

    { eexists; dands; eauto.
      destruct x0 as [l t]; allsimpl.
      eapply ind; eauto 3 with slow.
      allrw in_app_iff; tcsp. }

    { allrw @in_range_iff; exrepnd.
      allrw @in_sub_keep_first; repnd.
      allrw lin_flat_map; exrepnd.
      eexists; dands; eauto.
      destruct x1 as [l t]; allsimpl.
      allrw in_remove_nvars; repnd.
      eapply ind; eauto 3 with slow.
      allrw in_app_iff.
      right.
      unfold get_utokens_sub.
      rw lin_flat_map; eexists; dands; eauto.
      allrw @in_range_iff; exists v.
      allrw @in_sub_keep_first; dands; auto.
      rw @sub_find_sub_filter_eq; boolvar; tcsp. }
Qed.

Lemma get_utokens_sub_sub_keep_first2 {o} :
  forall (sub : @Sub o) (l1 l2 : list NVar),
    subset l1 l2
    -> subset
         (get_utokens_sub (sub_keep_first sub l1))
         (get_utokens_sub (sub_keep_first sub l2)).
Proof.
  introv i j.
  allunfold @get_utokens_sub.
  allrw lin_flat_map; exrepnd.
  eexists; dands; eauto.
  allrw @in_range_iff; exrepnd.
  exists v.
  allrw @in_sub_keep_first; repnd; dands; auto.
Qed.

Lemma get_utokens_step_seq_lsubst_aux_is_utok_sub_aux1 {o} :
  forall a (sub : @Sub o) v l vs,
    is_utok_sub sub
    -> sub_find sub v = Some (mk_utoken a)
    -> eqset (l ++ get_utokens_sub (sub_keep_first sub (v :: vs)))
             (a :: l ++ get_utokens_sub (sub_keep_first sub vs)).
Proof.
  introv isu e; allrw in_app_iff; split; introv h;
  allsimpl; allrw in_app_iff; repndors; tcsp; allsimpl.

  - allunfold @get_utokens_sub.
    allrw lin_flat_map; exrepnd.
    allrw @in_range_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allsimpl; repndors; subst; tcsp.

    + rw h1 in e; ginv; allsimpl; repndors; tcsp.

    + right.
      right.
      exists x0; dands; auto.
      rw @in_range_iff.
      exists v0.
      rw @in_sub_keep_first; dands; auto.

  - subst.
    right.
    allunfold @get_utokens_sub.
    allrw lin_flat_map.
    exists (mk_utoken x); simpl; dands; tcsp.
    allrw @in_range_iff.
    exists v.
    allrw @in_sub_keep_first; simpl; dands; tcsp.

  - allunfold @get_utokens_sub.
    allrw lin_flat_map; exrepnd.
    allrw @in_range_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    right.
    exists x0; dands; auto.
    rw @in_range_iff.
    exists v0.
    rw @in_sub_keep_first; dands; simpl; tcsp.
Qed.

Lemma get_utokens_step_seq_lsubst_aux_is_utok_sub_aux2 {o} :
  forall (sub : @Sub o) v l vs,
    is_utok_sub sub
    -> sub_find sub v = None
    -> eqset (l ++ get_utokens_sub (sub_keep_first sub (v :: vs)))
             (l ++ get_utokens_sub (sub_keep_first sub vs)).
Proof.
  introv isu e; allrw in_app_iff; split; introv h;
  allsimpl; allrw in_app_iff; repndors; tcsp; allsimpl.

  - allunfold @get_utokens_sub.
    allrw lin_flat_map; exrepnd.
    allrw @in_range_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allsimpl; repndors; subst; tcsp.

    + rw h1 in e; ginv; allsimpl; repndors; tcsp.

    + right.
      exists x0; dands; auto.
      rw @in_range_iff.
      exists v0.
      rw @in_sub_keep_first; dands; auto.

  - allunfold @get_utokens_sub.
    allrw lin_flat_map; exrepnd.
    allrw @in_range_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    right.
    exists x0; dands; auto.
    rw @in_range_iff.
    exists v0.
    rw @in_sub_keep_first; dands; simpl; tcsp.
Qed.

Lemma implies_eqset_cons {T} :
  forall (x : T) l1 l2,
    eqset l1 l2
    -> eqset (x :: l1) (x :: l2).
Proof.
  introv e; introv; split; intro h; allsimpl; repndors; tcsp; right; apply e; auto.
Qed.

Lemma eqset_app_move2 :
  forall {T} (a b c : list T),
    eqset ((a ++ b) ++ c) ((a ++ c) ++ b).
Proof.
  introv; introv; split; intro i; allrw in_app_iff; sp.
Qed.

Lemma nr_ut_sub_is_utok_sub {o} :
  forall lib sub (t : @NTerm o),
    nr_ut_sub lib t sub
    -> is_utok_sub sub.
Proof.
  induction sub; introv h; eauto 3 with slow.
  - introv i; allsimpl; tcsp.
  - destruct a as [v u].
    apply is_utok_sub_cons.
    apply nr_ut_sub_cons_iff in h; exrepnd; subst.
    apply IHsub in h0; simpl; dands; auto.
Qed.
Hint Resolve nr_ut_sub_is_utok_sub : slow.

Lemma get_utokens_step_seq_lsubst_aux_is_utok_sub {o} :
  forall (t : @NTerm o) (sub : Substitution),
    is_utok_sub sub
    -> eqset
         (get_utokens_step_seq (lsubst_aux t sub))
         (get_utokens_step_seq t ++ get_utokens_sub (sub_keep_first sub (free_vars t))).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv isus; simpl; autorewrite with slow; auto.

  - Case "vterm".
    rw @sub_keep_singleton.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
    simpl; autorewrite with slow; auto.
    rw @get_utokens_sub_cons; autorewrite with slow; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase; simpl; autorewrite with slow;
    try (complete (apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto));[].

    + rw <- app_assoc.
      apply eqset_app_if; auto.
      apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto.
Qed.

Lemma get_utokens_so_subset_get_cutokens_so {o} :
  forall (t : @SOTerm o),
    subseto (get_utokens_so t) (get_cutokens_so t).
Proof.
  soterm_ind1s t as [v ts ind |op bs ind] Case; simpl;
  try (complete (eauto 3 with slow)).

  - Case "sovar".
    eapply subseto_oeqset;[|apply oeqset_sym;apply oeqset_oappl_OLL].
    apply subseto_flat_map2; auto.

  - Case "soterm".
    eapply subseto_oeqset;[|apply oeqset_sym;apply oeqset_oappl_OLL].
    apply subseto_app_l; dands; apply implies_subseto_app_r.

    + left; apply subseto_refl.

    + right.
      apply subseto_flat_map2; auto.
      introv i.
      destruct x as [l t]; allsimpl.
      eapply ind; eauto.
Qed.

Lemma not_in_olist {T} :
  forall (v : T), !in_olist v onil.
Proof.
  introv h.
  inversion h; subst; exrepnd; allsimpl; tcsp.
Qed.

Lemma no_utokens_implies_get_utokens_so_nil {o} :
  forall (t : @SOTerm o),
    no_utokens t
    -> get_utokens_so t = [].
Proof.
  introv h.
  unfold no_utokens in h; auto.
Qed.

Lemma lsubst_aux_CSVal2term {o} :
  forall v (sub : @Sub o),
    lsubst_aux (CSVal2term v) sub = CSVal2term v.
Proof.
  introv.
  apply lsubst_aux_trivial_cl_term2.
  eauto 3 with slow.
Qed.
Hint Rewrite @lsubst_aux_CSVal2term : slow.

Lemma implies_disjoint_get_utokens_lib_axioms_right {o} :
  forall lib l (t : @NTerm o),
    disjoint l (get_utokens_lib lib t)
    -> disjoint l (get_utokens_lib lib mk_axiom).
Proof.
  introv disj i j; apply disj in i; clear disj; destruct i.
  allunfold @get_utokens_lib; allsimpl; allrw in_app_iff; tcsp.
Qed.
Hint Resolve implies_disjoint_get_utokens_lib_axioms_right : slow.

Lemma get_utokens_lib_lsubst {o} :
  forall lib (t : @NTerm o) sub,
    eqset
      (get_utokens_lib lib (lsubst t sub))
      (get_utokens_lib lib t ++ get_utokens_sub (sub_keep_first sub (free_vars t))).
Proof.
  repeat introv; split; introv h; unfold get_utokens_lib in *; allrw in_app_iff; repndors; tcsp.
  - apply get_utokens_lsubst in h; allrw in_app_iff; tcsp.
  - left; apply get_utokens_lsubst; allrw in_app_iff; tcsp.
  - left; apply get_utokens_lsubst; allrw in_app_iff; tcsp.
Qed.

Lemma disjoint_get_utokens_and_library_implies_lib {o} :
  forall lib (t : @NTerm o) l,
    disjoint l (get_utokens t)
    -> disjoint l (get_utokens_library lib)
    -> disjoint l (get_utokens_lib lib t).
Proof.
  introv d1 d2 i j.
  applydup d1 in i as j1.
  applydup d2 in i as j2.
  unfold get_utokens_lib in j; rw in_app_iff in j; tcsp.
Qed.
Hint Resolve disjoint_get_utokens_and_library_implies_lib : slow.

Lemma find_value_of_cs_at_implies_subset_get_utokens_CSVal2term {o} :
  forall vals n (v : @ChoiceSeqVal o),
    find_value_of_cs_at vals n = Some v
    -> subset (get_utokens (CSVal2term v)) (flat_map getc_utokens vals).
Proof.
  induction vals; introv h; simpl in *; ginv.
  destruct n; simpl in *; ginv.
  - apply subset_app_r; auto.
  - apply subset_app_l; eapply IHvals; eauto.
Qed.

Lemma find_cs_value_at_implies_subset_get_utokens_CSVal2tern {o} :
  forall lib name n (v : @ChoiceSeqVal o),
    find_cs_value_at lib name n = Some v
    -> subset (get_utokens (CSVal2term v)) (get_utokens_library lib).
Proof.
  induction lib; simpl; introv h.
  - unfold find_cs_value_at in h; simpl in *; ginv.
  - unfold find_cs_value_at in h; simpl in *.
    destruct a; simpl in *; tcsp.
    + boolvar; subst; tcsp.
      * apply subset_app_r.
        eapply find_value_of_cs_at_implies_subset_get_utokens_CSVal2term; eauto.
      * remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
        apply subset_app_l.
        eapply IHlib.
        unfold find_cs_value_at; allrw; auto.
    + remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
      apply subset_app_l.
      eapply IHlib.
      unfold find_cs_value_at; allrw; auto.
Qed.
Hint Resolve find_cs_value_at_implies_subset_get_utokens_CSVal2tern : slow.

Lemma find_cs_value_at_implies_disjoint_get_utokens_lib {o} :
  forall lib name n (v : @ChoiceSeqVal o) l,
    find_cs_value_at lib name n = Some v
    -> disjoint l (get_utokens_library lib)
    -> disjoint l (get_utokens_lib lib (CSVal2term v)).
Proof.
  introv i d a b.
  apply d in a; clear d.
  unfold get_utokens_lib in b; apply in_app_iff in b; repndors; tcsp.
  apply find_cs_value_at_implies_subset_get_utokens_CSVal2tern in i; apply i in b; tcsp.
Qed.
Hint Resolve find_cs_value_at_implies_disjoint_get_utokens_lib : slow.

Lemma get_utokens_library_subset_get_utokens_lib {o} :
  forall lib (t : @NTerm o),
    subset (get_utokens_library lib) (get_utokens_lib lib t).
Proof.
  introv i; unfold get_utokens_lib; apply in_app_iff; tcsp.
Qed.
Hint Resolve get_utokens_library_subset_get_utokens_lib : slow.

Hint Rewrite @get_utokens_pushdown_fresh : slow.

Lemma get_utokens_lib_pushdown_fresh {o} :
  forall lib (t : @NTerm o) v,
    get_utokens_lib lib (pushdown_fresh v t)
    = get_utokens_lib lib t.
Proof.
  introv; unfold get_utokens_lib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_lib_pushdown_fresh : slow.

Lemma get_utokens_lib_mk_fresh {o} :
  forall lib (t : @NTerm o) v,
    get_utokens_lib lib (mk_fresh v t)
    = get_utokens_lib lib t.
Proof.
  introv; unfold get_utokens_lib; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_lib_mk_fresh : slow.

Lemma get_fresh_atom_prop_and_lib {o} :
  forall lib (t : @NTerm o),
    !LIn (get_fresh_atom lib t) (get_utokens_lib lib t).
Proof.
  introv i.
  unfold get_fresh_atom in i.
  match goal with
  | [ H : context[fresh_atom ?a ?b] |- _ ] =>
    destruct (fresh_atom a b); allsimpl; tcsp
  end.
Qed.

Lemma get_utokens_lib_mk_instance {o} :
  forall lib vars bs (rhs : @SOTerm o),
    matching_bterms vars bs
    -> subset
         (get_utokens_lib lib (mk_instance vars bs rhs))
         (get_utokens_so rhs ++ get_utokens_bs bs ++ get_utokens_library lib).
Proof.
  introv m i.
  unfold get_utokens_lib in i; allrw in_app_iff; repndors; tcsp.
  apply get_utokens_mk_instance in i; auto; allrw in_app_iff; tcsp.
Qed.

Lemma alphaeq_preserves_get_utokens_lib {o} :
  forall lib (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> get_utokens_lib lib t1 = get_utokens_lib lib t2.
Proof.
  introv aeq.
  unfold get_utokens_lib.
  f_equal.
  apply alphaeq_preserves_utokens; auto.
Qed.

Lemma get_utokens_lib_mk_fresh_choice_nat_seq_subset_get_utokens_lib {o} :
  forall a lib l (t : @NTerm o),
    subset
      (get_utokens_lib lib (mk_fresh_choice_nat_seq a lib l))
      (get_utokens_lib lib t).
Proof.
  introv h; simpl in *.
  unfold get_utokens_lib in *; simpl in *.
  apply in_app_iff; tcsp.
Qed.
Hint Resolve get_utokens_lib_mk_fresh_choice_nat_seq_subset_get_utokens_lib : slow.

Lemma get_utokens_csval2term_subset {o} :
  forall entry (v : @ChoiceSeqVal o),
    last_cs_entry entry = Some v
    -> subset (get_utokens (CSVal2term v))
              (flat_map getc_utokens entry).
Proof.
  induction entry; introv h; simpl in *; ginv.
  destruct entry; ginv; simpl in *; autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve get_utokens_csval2term_subset : slow.


Lemma find_last_cs_implies_subset_get_utokens_CSVal2term {o} :
  forall lib name entry (v : @ChoiceSeqVal o),
    find_cs lib name = Some entry
    -> last_cs_entry entry = Some v
    -> subset (get_utokens (CSVal2term v)) (get_utokens_library lib).
Proof.
  induction lib; simpl; introv h q; ginv.
  destruct a; simpl in *; tcsp; boolvar; subst; ginv; eauto 3 with slow.
Qed.
Hint Resolve find_last_cs_implies_subset_get_utokens_CSVal2term : slow.

Lemma disjoint_get_utokens_lib_csval2term_if_find_last_cs {o} :
  forall lib name entry (v : @ChoiceSeqVal o) l t,
    find_cs lib name = Some entry
    -> last_cs_entry entry = Some v
    -> disjoint l (get_utokens_lib lib t)
    -> disjoint l (get_utokens_lib lib (CSVal2term v)).
Proof.
  introv f eqv d x z; apply d in x; clear d; destruct x.
  apply in_app_iff in z; apply in_app_iff; repndors; tcsp.
  eapply find_last_cs_implies_subset_get_utokens_CSVal2term in z; eauto.
Qed.
Hint Resolve disjoint_get_utokens_lib_csval2term_if_find_last_cs : slow.

Lemma subset_get_utokens_lib_csval2term_get_utokens_lib {o} :
  forall lib name entry (v : @ChoiceSeqVal o) t,
    find_cs lib name = Some entry
    -> last_cs_entry entry = Some v
    -> subset (get_utokens_lib lib (CSVal2term v))
              (get_utokens_lib lib t).
Proof.
  introv f q h.
  allrw in_app_iff; repndors; tcsp.
  eapply find_last_cs_implies_subset_get_utokens_CSVal2term in h; eauto.
Qed.
Hint Resolve subset_get_utokens_lib_csval2term_get_utokens_lib : slow.

Lemma lsubst_aux_find_last_entry_default {o} :
  forall lib name (a : @NTerm o) sub,
    lsubst_aux (find_last_entry_default lib name a) sub
    = find_last_entry_default lib name (lsubst_aux a sub).
Proof.
  introv.
  unfold find_last_entry_default.
  remember (find_cs lib name) as fcs; destruct fcs; tcsp.
  remember (last_cs_entry c) as lcs; destruct lcs; tcsp.
  autorewrite with slow; auto.
Qed.

Lemma get_utokens_lib_mk_last_cs_choice_seq {o} :
  forall lib name (a : @NTerm o),
    get_utokens_lib lib (mk_last_cs (mk_choice_seq name) a)
    = get_utokens_lib lib a.
Proof.
  introv.
  unfold get_utokens_lib; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_lib_mk_last_cs_choice_seq : slow.

Lemma get_utokens_lib_find_last_entry_default_subset {o} :
  forall lib name (a : @NTerm o),
    subset
      (get_utokens_lib lib (find_last_entry_default lib name a))
      (get_utokens_lib lib a).
Proof.
  introv i.
  unfold find_last_entry_default in i.
  remember (find_cs lib name) as fcs; destruct fcs; symmetry in Heqfcs; simpl in *; tcsp.
  remember (last_cs_entry c) as lcs; destruct lcs; symmetry in Heqlcs; simpl in *; tcsp.
  autorewrite with slow in *.
  eapply subset_get_utokens_lib_csval2term_get_utokens_lib; eauto.
Qed.
Hint Resolve get_utokens_lib_find_last_entry_default_subset : slow.

Lemma implies_disjoint_get_utokens_lib_find_last_entry_default {o} :
  forall l lib name (a : @NTerm o),
    disjoint l (get_utokens_lib lib a)
    -> disjoint l (get_utokens_lib lib (find_last_entry_default lib name a)).
Proof.
  introv disj h q.
  apply get_utokens_lib_find_last_entry_default_subset in q; apply disj in q; tcsp.
Qed.
Hint Resolve implies_disjoint_get_utokens_lib_find_last_entry_default : slow.

Lemma implies_subset_get_utokens_lib_mk_swap_cs1 {o} :
  forall lib (a b c d e f : @NTerm o),
    subset (get_utokens_lib lib a) (get_utokens_lib lib d)
    -> subset (get_utokens_lib lib b) (get_utokens_lib lib e)
    -> subset (get_utokens_lib lib c) (get_utokens_lib lib f)
    -> subset
         (get_utokens_lib lib (mk_swap_cs1 a b c))
         (get_utokens_lib lib (mk_swap_cs1 d e f)).
Proof.
  introv sa sb sc i; unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
  allrw in_app_iff; repndors; tcsp.
  { pose proof (sa x) as sa; autodimp sa hyp; allrw in_app_iff; tcsp. }
  { pose proof (sb x) as sb; autodimp sb hyp; allrw in_app_iff; tcsp. }
  { pose proof (sc x) as sc; autodimp sc hyp; allrw in_app_iff; tcsp. }
Qed.
Hint Resolve implies_subset_get_utokens_lib_mk_swap_cs1 : slow.

Lemma implies_subset_get_utokens_lib_mk_swap_cs0 {o} :
  forall lib (a b c d e f : @NTerm o),
    subset (get_utokens_lib lib a) (get_utokens_lib lib d)
    -> subset (get_utokens_lib lib b) (get_utokens_lib lib e)
    -> subset (get_utokens_lib lib c) (get_utokens_lib lib f)
    -> subset
         (get_utokens_lib lib (mk_swap_cs0 a b c))
         (get_utokens_lib lib (mk_swap_cs0 d e f)).
Proof.
  introv sa sb sc i; unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
  allrw in_app_iff; repndors; tcsp.
  { pose proof (sa x) as sa; autodimp sa hyp; allrw in_app_iff; tcsp. }
  { pose proof (sb x) as sb; autodimp sb hyp; allrw in_app_iff; tcsp. }
  { pose proof (sc x) as sc; autodimp sc hyp; allrw in_app_iff; tcsp. }
Qed.
Hint Resolve implies_subset_get_utokens_lib_mk_swap_cs0 : slow.

(*Lemma implies_subset_get_utokens_lib_mk_swap_cs {o} :
  forall lib (a b c d e f : @NTerm o),
    subset (get_utokens_lib lib a) (get_utokens_lib lib d)
    -> subset (get_utokens_lib lib b) (get_utokens_lib lib e)
    -> subset (get_utokens_lib lib c) (get_utokens_lib lib f)
    -> subset
         (get_utokens_lib lib (mk_swap_cs a b c))
         (get_utokens_lib lib (mk_swap_cs d e f)).
Proof.
  introv sa sb sc i; unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
  allrw in_app_iff; repndors; tcsp.
  { pose proof (sa x) as sa; autodimp sa hyp; allrw in_app_iff; tcsp. }
  { pose proof (sb x) as sb; autodimp sb hyp; allrw in_app_iff; tcsp. }
  { pose proof (sc x) as sc; autodimp sc hyp; allrw in_app_iff; tcsp. }
Qed.
Hint Resolve implies_subset_get_utokens_lib_mk_swap_cs : slow.*)

Lemma implies_subset_get_utokens_lib_mk_swap_cs2 {o} :
  forall lib a b (c d : @NTerm o),
    subset (get_utokens_lib lib c) (get_utokens_lib lib d)
    -> subset
         (get_utokens_lib lib (mk_swap_cs2 a b c))
         (get_utokens_lib lib (mk_swap_cs2 a b d)).
Proof.
  introv sa i; unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
  allrw in_app_iff; repndors; tcsp.
  pose proof (sa x) as sa; autodimp sa hyp; allrw in_app_iff; tcsp.
Qed.
Hint Resolve implies_subset_get_utokens_lib_mk_swap_cs2 : slow.

Lemma nr_ut_lsubst_aux_choice_seq_implies {o} :
  forall lib (u : @NTerm o) sub t name,
    nr_ut_sub lib u sub
    -> lsubst_aux t sub = mk_choice_seq name
    -> t = mk_choice_seq name.
Proof.
  introv nrut h.
  destruct t as [v|op bs]; simpl in *.
  { remember (sub_find sub v) as find; symmetry in Heqfind; destruct find; subst; simpl in *; tcsp.
    eapply nr_ut_some_implies in Heqfind; eauto; exrepnd; ginv. }
  destruct op; simpl in *; ginv.
  destruct c; simpl in *; tcsp; ginv.
  destruct bs; simpl in *; tcsp; ginv.
Qed.

Lemma nr_ut_lsubst_aux_exc_implies {o} :
  forall lib (u : @NTerm o) sub t l,
    nr_ut_sub lib u sub
    -> lsubst_aux t sub = oterm Exc l
    -> {k : list BTerm & t = oterm Exc k # l = lsubst_bterms_aux k sub}.
Proof.
  introv nrut h.
  destruct t as [v|op bs]; simpl in *.
  { remember (sub_find sub v) as find; symmetry in Heqfind; destruct find; subst; simpl in *; tcsp; ginv.
    eapply nr_ut_some_implies in Heqfind; eauto; exrepnd; ginv. }
  destruct op; simpl in *; ginv.
  eexists; dands; eauto.
Qed.

Lemma range_sw_sub {o} :
  forall a b l, range (@sw_sub o a b l) = map (fun v => mk_swap_cs2 a b (mk_var v)) l.
Proof.
  induction l; introv; simpl; auto; try congruence.
Qed.
Hint Rewrite @range_sw_sub : slow.

Lemma get_utokens_push_swap_cs_sub_term {o} :
  forall a b l (t : @NTerm o),
    get_utokens (push_swap_cs_sub_term a b l t) = get_utokens t.
Proof.
  introv; unfold push_swap_cs_sub_term.
  apply get_utokens_lsubst_aux_trivial1.
  unfold get_utokens_sub; autorewrite with slow.
  rewrite flat_map_map; unfold compose; simpl.
  apply implies_null_flat_map; tcsp.
Qed.
Hint Rewrite @get_utokens_push_swap_cs_sub_term : slow.

Lemma flat_map_get_utokens_b_push_swap_cs_bterm {o} :
  forall n1 n2 (bs : list (@BTerm o)),
    flat_map get_utokens_b (push_swap_cs_bterms n1 n2 bs)
    = get_utokens_bs bs.
Proof.
  introv; unfold push_swap_cs_bterms.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_get_utokens_b_push_swap_cs_bterm : slow.

Lemma nr_ut_sub_implies_disjoint_sub_free_vars {o} :
  forall lib t (sub : @Sub o) vs,
    nr_ut_sub lib t sub
    -> disjoint (sub_free_vars sub) vs.
Proof.
  introv nrut i.
  apply in_sub_free_vars in i; exrepnd.
  eapply in_nr_ut_sub in i0; eauto; exrepnd; subst; simpl in *; tcsp.
Qed.
Hint Resolve nr_ut_sub_implies_disjoint_sub_free_vars : slow.

Lemma get_utokens_c_swap_cs_can {o} :
  forall sw (can : @CanonicalOp o),
    get_utokens_c (swap_cs_can sw can) = get_utokens_c can.
Proof.
  introv; destruct can; simpl; auto.
Qed.
Hint Rewrite @get_utokens_c_swap_cs_can : slow.

Lemma lsubst_nat {o} :
  forall k (sub : @Sub o),
    lsubst (mk_nat k) sub = mk_nat k.
Proof.
  introv; apply lsubst_trivial4; simpl; auto.
Qed.
Hint Rewrite @lsubst_nat : slow.

Lemma swap_cs_sub_if_nr_ut_sub {o} :
  forall lib sw (sub : @Sub o) t,
    nr_ut_sub lib t sub
    -> swap_cs_sub sw sub = sub.
Proof.
  induction sub; introv h; simpl; auto.
  inversion h as [|? ? ? ? i q]; subst; clear h; simpl.
  erewrite IHsub; eauto.
Qed.

Lemma get_utokens_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    get_utokens (swap_cs_term sw t)
    = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  autorewrite with slow; f_equal.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl; eapply ind; eauto.
Qed.
Hint Rewrite @get_utokens_swap_cs_term : slow.

Lemma get_utokens_lib_swap_cs_term {o} :
  forall lib sw (t : @NTerm o),
    get_utokens_lib lib (swap_cs_term sw t)
    = get_utokens_lib lib t.
Proof.
  introv; unfold get_utokens_lib; autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_lib_swap_cs_term : slow.

Lemma lsubst_aux_sw_sub_nr_ut_sub_swap {o} :
  forall a b (t : @NTerm o) l sub,
    is_utok_sub sub
    -> disjoint l (dom_sub sub)
    -> lsubst_aux (lsubst_aux t (sw_sub a b l)) sub
       = lsubst_aux (lsubst_aux t sub) (sw_sub a b l).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv nrut disj; simpl in *; tcsp.

  { rewrite sub_find_sw_sub; boolvar; tcsp.
    { applydup disj in l0; simpl; autorewrite with slow.
      rewrite sub_find_none_if; simpl; tcsp.
      rewrite sub_find_sw_sub; boolvar; tcsp. }
    { simpl.
      remember (sub_find sub v) as x; destruct x; symmetry in Heqx; simpl in *; tcsp.
      { apply sub_find_some in Heqx; apply nrut in Heqx.
        apply is_utok_implies in Heqx; exrepnd; subst; simpl; tcsp. }
      { rewrite sub_find_sw_sub; boolvar;tcsp. } } }

  allrw map_map; unfold compose; simpl.
  f_equal; apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  autorewrite with slow.
  eapply ind; eauto; try (rewrite <- dom_sub_sub_filter); eauto 3 with slow;
    try (complete (apply disjoint_remove_nvars_l; repeat apply disjoint_remove_nvars_weak_r; auto)).
Qed.

Lemma lsubst_aux_nr_ut_sub_push_swap_cs_sub_term {o} :
  forall a b l (t : @NTerm o) sub,
    is_utok_sub sub
    -> disjoint l (dom_sub sub)
    -> lsubst_aux (push_swap_cs_sub_term a b l t) sub
       = push_swap_cs_sub_term a b l (lsubst_aux t sub).
Proof.
  introv nrut disj; unfold push_swap_cs_sub_term.
  apply lsubst_aux_sw_sub_nr_ut_sub_swap; eauto 3 with slow.
Qed.

Lemma alpha_eq_lsubst_sw_sub_cl_sub {o} :
  forall a b (t : @NTerm o) l sub,
    cl_sub sub
    -> disjoint l (dom_sub sub)
    -> alpha_eq
         (lsubst_aux (lsubst_aux t (sw_sub a b l)) sub)
         (lsubst_aux (lsubst_aux t sub) (sw_sub a b l)).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cl disj; simpl in *.

  { rewrite sub_find_sw_sub; boolvar; simpl; autorewrite with slow.

    { applydup disj in l0.
      rewrite sub_find_none_if; auto; simpl.
      rewrite sub_find_sw_sub; boolvar; simpl; tcsp. }

    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl.

    { applydup @sub_find_some in Heqsf.
      apply in_cl_sub in Heqsf0; auto.
      rewrite lsubst_aux_trivial_cl_term2; auto. }

    rewrite sub_find_sw_sub; boolvar; tcsp. }

  allrw map_map; unfold compose.
  apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
  introv i; rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
  apply in_combine_same in i1; repnd; subst.
  destruct a0; simpl.
  apply alpha_eq_bterm_congr.
  rewrite computation_preserve1.sub_filter_sw_sub.
  eapply ind; eauto; eauto 3 with slow.
  rewrite <- dom_sub_sub_filter.
  apply disjoint_remove_nvars_l.
  eapply subset_disjoint_r; eauto.
  introv i; apply in_remove_nvars in i; repnd.
  apply in_remove_nvars in i1; repnd; auto.
Qed.

Lemma disjoint_free_vars_lsubst_aux_dom_sub {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> disjoint (free_vars (lsubst_aux t sub)) (dom_sub sub).
Proof.
  introv cl i j.
  apply free_vars_lsubst_aux_subset in i.
  rewrite sub_free_vars_if_cl_sub in i; auto; autorewrite with slow in *.
  apply in_remove_nvars in i; repnd; tcsp.
Qed.
Hint Resolve disjoint_free_vars_lsubst_aux_dom_sub : slow.

Lemma sub_filter_all {o} :
  forall (sub : @Sub o),
    sub_filter sub (dom_sub sub) = [].
Proof.
  introv.
  pose proof (sub_filter_nil_combine sub []) as q; simpl in q; auto.
Qed.
Hint Rewrite @sub_filter_all : slow.

Lemma cl_lsubst_aux_twice {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> lsubst_aux (lsubst_aux t sub) sub = lsubst_aux t sub.
Proof.
  introv cl.
  rewrite <- cl_lsubst_aux_app; auto.
  rewrite cl_lsubst_aux_app_sub_filter; autorewrite with slow; auto.
Qed.

Lemma get_utokens_sub_sw_sub {o} :
  forall a b l,
    @get_utokens_sub o (sw_sub a b l) = [].
Proof.
  introv; unfold get_utokens_sub; autorewrite with slow.
  rewrite flat_map_map; unfold compose; simpl; autorewrite with slow.
  apply flat_map_empty; tcsp.
Qed.
Hint Rewrite @get_utokens_sub_sw_sub : slow.

Lemma get_utokens_lsubst_aux_sw_sub {o} :
  forall (t : @NTerm o) a b l,
    get_utokens (lsubst_aux t (sw_sub a b l)) = get_utokens t.
Proof.
  introv; apply get_utokens_lsubst_aux_trivial1; eauto 3 with slow.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @get_utokens_lsubst_aux_sw_sub : slow.

Lemma compute_step_subst_utoken {o} :
  forall lib (t u : @NTerm o) sub,
    nt_wf t
    -> compute_step lib (lsubst t sub) = csuccess u
    -> nr_ut_sub lib t sub
    -> disjoint (get_utokens_sub sub) (get_utokens_lib lib t)
    -> {w : NTerm
        & alpha_eq u (lsubst w sub)
        # disjoint (get_utokens_sub sub) (get_utokens_lib lib w)
        # subvars (free_vars w) (free_vars t)
        # subset (get_utokens_lib lib w) (get_utokens_lib lib t)
        # (forall sub',
             nr_ut_sub lib t sub'
             -> dom_sub sub = dom_sub sub'
             -> disjoint (get_utokens_sub sub') (get_utokens_lib lib t)
             -> {s : NTerm
                 & compute_step lib (lsubst t sub') = csuccess s
                 # alpha_eq s (lsubst w sub')})}.
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv wf comp nrut disj; tcsp.

  - Case "vterm".
    unflsubst in comp; eauto with slow.
    allsimpl.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf.

    + applydup @sub_find_some in Heqsf.
      eapply in_nr_ut_sub in Heqsf0; eauto; exrepnd; subst.
      csunf comp; allsimpl; ginv.
      exists (@mk_var o v).
      unflsubst; simpl; rw Heqsf; dands; eauto 3 with slow.
      introv nrut' eqdoms disj'.
      pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' v (vterm v)) as h.
      repeat (autodimp h hyp).
      rw Heqsf in h; exrepnd.
      unflsubst; simpl; rw h0.
      csunf; simpl.
      eexists; dands; eauto.
      unflsubst; simpl; rw h0; auto.

    + csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      unflsubst in comp; allsimpl.
      csunf comp; allsimpl; ginv.
      exists (oterm (Can can) bs).
      allrw app_nil_r; allsimpl.
      unflsubst; allsimpl; dands; eauto 3 with slow.

      introv nrut' eqdoms disj'.
      repeat unflsubst; simpl; csunf; simpl.
      eexists; dands; eauto.

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv));[|].

      { csunf comp; simpl in *.
        apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *.
        exists (@mk_nat o (lib_depth lib)); simpl; autorewrite with slow.
        dands; eauto 3 with slow.
        introv nrut' eqdoms disj'.
        csunf; simpl; eexists; dands; eauto. }

      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|op bts]; try (complete (allsimpl; ginv));
        [ | ].

        { unflsubst in comp; allsimpl.
          allrw @sub_filter_nil_r.
          remember (sub_find sub x) as sf; symmetry in Heqsf; destruct sf;
          [|csunf comp; allsimpl; ginv].

          applydup @sub_find_some in Heqsf.
          eapply in_nr_ut_sub in Heqsf0; eauto; exrepnd; subst.
          apply compute_step_ncan_vterm_success in comp.
          repndors; exrepnd; subst.

          - exists (@mk_axiom o); allsimpl.
            rw @cl_lsubst_trivial; simpl; dands; eauto 3 with slow.

            { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; auto. }

            introv nrut' eqdoms disj'.
            exists (@mk_axiom o); allsimpl.
            rw (@cl_lsubst_trivial o mk_axiom); simpl; dands; eauto 3 with slow.
            unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' x (oterm (NCan NParallel) (bterm [] (vterm x) :: bs))) as h; repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; rw h0.
            csunf; simpl.
            unfold compute_step_parallel; auto.

          - destruct bs; allsimpl; cpx; GC.
            exists (@mk_apply o (mk_var x) (mk_fix (mk_var x))).
            unflsubst; simpl; allrw @sub_filter_nil_r; allrw; dands; eauto 3 with slow.
            introv nrut' eqdoms disj'.
            repeat unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' x (oterm (NCan NFix) [bterm [] (vterm x)])) as h; repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; rw h0.
            csunf; simpl.
            eexists; dands; eauto.

          - destruct bs; allsimpl; cpx.
            destruct bs; allsimpl; cpx.
            destruct b0 as [l t].
            destruct l; allsimpl; cpx.

            exists (lsubst t [(x0, mk_var x)]).
            dands; allrw app_nil_r.

            + eapply alpha_eq_trans;[|apply alpha_eq_sym; apply combine_1var_sub]; eauto 2 with slow.
              simpl.
              unflsubst (@mk_var o x); simpl; rw Heqsf.
              rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
              unfold subst; rw <- @cl_lsubst_app; eauto 3 with slow; simpl.
              apply alpha_eq_lsubst_if_ext_eq; auto.
              introv i; simpl.
              rw @sub_find_app; rw @sub_find_sub_filter_eq; rw memvar_singleton.
              boolvar; simpl; boolvar; simpl; tcsp.
              remember (sub_find sub v) as sf; destruct sf; allsimpl; auto.

            + eapply disjoint_eqset_r;[apply eqset_sym; apply get_utokens_lib_lsubst|].
              eapply subset_disjoint_r; eauto 3 with slow.
              apply app_subset; dands;
                [apply subset_get_utokens_implies_subset_get_utokens_lib;simpl;eauto 3 with slow|].
              eapply subset_trans;[apply get_utokens_sub_sub_keep_first|].
              unfold get_utokens_sub; simpl; auto.

            + eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint]; simpl.
              unfold dom_sub; simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

            + apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              autorewrite with slow.
              eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
              unfold get_cutokens_sub; simpl; boolvar; simpl;
              autorewrite with slow; eauto 3 with slow.

            + introv nrut' eqdoms disj'.
              unflsubst; simpl; allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan NCbv) [bterm [] (vterm x), bterm [x0] t])) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; rw h0.
              csunf; simpl.
              eexists; dands; eauto.
              unfold apply_bterm; simpl.
              rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
              eapply alpha_eq_trans;[|apply alpha_eq_sym; apply combine_1var_sub]; eauto 2 with slow; simpl.
              fold_terms; rw <- @cl_lsubst_app; eauto 3 with slow; simpl.
              unflsubst (@mk_var o x); simpl; rw h0.
              apply alpha_eq_lsubst_if_ext_eq; auto.
              introv i; simpl.
              rw @sub_find_app; rw @sub_find_sub_filter_eq; rw memvar_singleton.
              boolvar; simpl; boolvar; simpl; tcsp.
              remember (sub_find sub' v) as sf; destruct sf; allsimpl; auto.

          - repeat (destruct bs; allsimpl; ginv).
            destruct b0 as [l1 t1]; allsimpl.
            destruct b1 as [l2 t2]; allsimpl.
            allunfold @nobnd.
            destruct l1, l2; allsimpl; ginv.
            allrw @sub_filter_nil_r; allrw app_nil_r; allrw remove_nvars_nil_l.

            exists (mk_atom_eq t1 t1 (mk_var x) mk_bot).
            unflsubst; simpl.
            allrw @sub_filter_nil_r; allrw app_nil_r; allrw remove_nvars_nil_l;
            allrw @sub_find_sub_filter_eq;
            allrw; dands; eauto 3 with slow.

            { allrw disjoint_app_r; repnd; dands; eauto 3 with slow. }

            { allrw subvars_app_l; dands; eauto 3 with slow. }

            { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              autorewrite with slow; eauto 3 with slow. }

            introv nrut' eqdoms disj'.
            unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub
                          lib sub sub' x
                          (oterm (NCan NTryCatch) [bterm [] (vterm x), bterm [] t1, bterm [x0] t2])) as h; repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; rw h0.
            csunf; simpl.
            eexists; dands; eauto; fold_terms.
            unflsubst; simpl;
            allrw @sub_filter_nil_r;
            allrw @sub_find_sub_filter_eq;
            allrw memvar_singleton;
            allrw <- beq_var_refl;
            allrw; auto.

          - repndors; exrepnd; subst.

            + repeat (destruct bs; allsimpl; ginv).
              destruct b as [l1 u1].
              destruct b0 as [l2 u2].
              destruct b1 as [l3 u3]; allsimpl.
              destruct l1, l2, l3; allsimpl; boolvar; ginv;[].
              allrw @sub_filter_nil_r; allrw app_nil_r.
              allunfold @nobnd.
              repeat (apply cons_inj in comp1; repnd); GC; ginv.
              inversion comp0 as [epk]; clear comp0.
              fold_terms.

              repndors; repnd; subst; allrw @sub_filter_nil_r.

              * exists u2.
                unflsubst; dands; eauto 4 with slow.

                {
                  eapply subset_disjoint_r;[eauto|].
                  apply subset_get_utokens_implies_subset_get_utokens_lib.
                  simpl; eauto 4 with slow.
                }

                {
                  apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                  autorewrite with slow; eauto 3 with slow.
                }

                introv nrut' eqdoms disj'.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              lib sub sub' x
                              (oterm (NCan (NCompOp CompOpEq))
                                     [nobnd (mk_var x), nobnd u1, nobnd u2, nobnd u3])) as h; repeat (autodimp h hyp).
                rw Heqsf in h; exrepnd.
                unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
                assert (disjoint (get_utokens_sub sub) (get_utokens u1)) as ni2.
                { allrw disjoint_app_r; sp. }
                applydup @sub_find_some in Heqsf.
                unfold get_utokens_sub in ni2.
                apply in_sub_eta in Heqsf0; repnd.
                disj_flat_map; allsimpl; allrw disjoint_singleton_l.
                eapply lsubst_aux_utoken_eq_utoken_implies in Heqsf2; eauto; exrepnd; subst; allsimpl; allrw Heqsf2; GC.
                pose proof (nr_ut_sub_some_eq
                              lib sub v x a (oterm (NCan (NCompOp CompOpEq))
                                               [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3]))
                  as k; repeat (autodimp k hyp); subst; simpl; tcsp.
                allrw; csunf; simpl; boolvar; allsimpl; tcsp; GC.
                dcwf h; allsimpl.
                unfold compute_step_comp; simpl; boolvar; tcsp; GC.
                eexists; dands; eauto.
                unflsubst; auto.

              * exists u3.
                unflsubst; dands; eauto 4 with slow.

                {
                  eapply subset_disjoint_r;[eauto|].
                  apply subset_get_utokens_implies_subset_get_utokens_lib.
                  simpl; eauto 4 with slow.
                }

                {
                  apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                  autorewrite with slow; eauto 3 with slow.
                }

                introv nrut' eqdoms disj'.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              lib sub sub' x
                              (oterm (NCan (NCompOp CompOpEq))
                                     [nobnd (mk_var x), nobnd u1, nobnd u2, nobnd u3])) as h; repeat (autodimp h hyp).
                rw Heqsf in h; exrepnd.
                unflsubst; simpl; allrw @sub_filter_nil_r; allrw app_nil_r; allrw.
                allapply @lsubst_aux_pk2term_eq_utoken_implies_or; repndors; exrepnd; subst; allsimpl.

                { dup epk1 as e.
                  eapply nr_ut_some_implies in e;[|exact nrut].
                  destruct e as [a' e].
                  allapply @pk2term_utoken; subst; allsimpl.
                  assert (a' <> a) as d by (intro e; subst; tcsp).

                  pose proof (nr_ut_sub_some_diff
                                lib sub v x a' a
                                (oterm (NCan (NCompOp CompOpEq))
                                       [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3])) as h; repeat (autodimp h hyp).
                  pose proof (sub_find_some_eq_doms_nr_ut_sub
                                lib sub sub' v
                                (oterm (NCan (NCompOp CompOpEq))
                                       [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3])) as k; repeat (autodimp k hyp).
                  assert (sub_find sub v = Some (mk_utoken a')) as e by auto; allrw e; GC; exrepnd; rw k0.
                  pose proof (nr_ut_sub_some_diff2
                                lib sub' v x a1 a0
                                (oterm (NCan (NCompOp CompOpEq))
                                       [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3])) as hh;
                    repeat (autodimp hh hyp); allsimpl; tcsp.
                  csunf; simpl; boolvar; allsimpl; tcsp; GC.
                  dcwf q; allsimpl.
                  unfold compute_step_comp; simpl; boolvar; ginv; tcsp.
                  eexists; dands; eauto; unflsubst.
                }

                { allrw @lsubst_aux_pk2term.
                  allrw @pk2term_eq; allsimpl; allrw app_nil_r.
                  csunf; simpl.
                  dcwf h.
                  unfold compute_step_comp; simpl.
                  allrw @get_param_from_cop_pk2can.
                  boolvar; subst; eexists; dands; eauto; unflsubst.
                  allsimpl.
                  allrw disjoint_cons_r; repnd.
                  apply sub_find_some in h0.
                  rw @in_get_utokens_sub in disj'; destruct disj'.
                  eexists; eexists; dands; eauto; simpl; auto.
                }

            + destruct bs; allsimpl; cpx.
              destruct b as [l t].
              destruct l; allsimpl; cpx; fold_terms; ginv.
              allrw @sub_filter_nil_r.
              pose proof (ind t t []) as h; repeat (autodimp h hyp); clear ind; eauto 3 with slow.
              rw <- @cl_lsubst_lsubst_aux in comp1; eauto with slow.

              allrw @nt_wf_NCompOp; exrepnd; ginv; allsimpl; autorewrite with slow in *.
              allrw disjoint_app_r; repnd.

              pose proof (h x0 sub) as k; clear h; repeat (autodimp k hyp).

              {
                eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow.
              }

              {
                simpl in *; eauto 3 with slow.
              }

              exrepnd.

              exists (oterm (NCan (NCompOp CompOpEq))
                            (nobnd (mk_var x) :: nobnd w :: nobnd t3 :: nobnd t4 ::[])).
              unflsubst; simpl; autorewrite with slow in *; allrw @sub_filter_nil_r; allrw.
              dands; eauto 4 with slow.

              * prove_alpha_eq4; allrw map_length.
                introv k; destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in k1.

              * rw disjoint_app_r; dands; auto.
                allrw disjoint_app_r; dands; simpl in *; repnd; eauto 3 with slow.

              * unfold get_utokens_lib; simpl; autorewrite with slow.
                repeat (apply implies_subset_app); eauto 4 with slow.
                eapply subset_trans;[apply get_utokens_subset_get_utokens_lib|].
                eapply subset_trans;[eauto|].
                unfold get_utokens_lib; simpl; autorewrite with slow.
                repeat (apply implies_subset_app); eauto 4 with slow.

              * introv nrut' eqdoms disj'.
                unflsubst; simpl; allrw @sub_filter_nil_r.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              lib sub sub' x
                              (oterm (NCan (NCompOp CompOpEq))
                                     (nobnd (mk_var x)
                                            :: nobnd t2
                                            :: nobnd t3
                                            :: nobnd t4
                                            :: []))) as h; repeat (autodimp h hyp).
                rw Heqsf in h; exrepnd; allrw.
                pose proof (k0 sub') as h; clear k0; repeat (autodimp h hyp).

                {
                  eapply nr_ut_sub_change_term;[|idtac|eauto];
                    allsimpl; allrw remove_nvars_nil_l; eauto 3 with slow.
                }

                {
                  eapply subset_disjoint_r;[eauto|].
                  apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                  eauto 3 with slow.
                }

                exrepnd.
                eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto.
                unfold mk_utoken.
                rw @compute_step_ncompop_ncanlike2; eauto with slow; boolvar; allsimpl; tcsp;[].
                unflsubst in h2; fold_terms; rw h2.
                eexists; dands; auto.
                unflsubst; simpl; allrw @sub_filter_nil_r; allrw.

                prove_alpha_eq4; allrw map_length.
                introv k; destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in h1.

            + apply isexc_implies2 in comp2; exrepnd; subst.
              destruct bs; allsimpl; ginv.
              destruct b as [l1 t1].
              destruct l1; allsimpl; ginv.
              fold_terms; cpx.
              allrw @sub_filter_nil_r.
              destruct t1; allsimpl; ginv.
              { remember (sub_find sub n) as sfn; symmetry in Heqsfn; destruct sfn; ginv.
                apply sub_find_some in Heqsfn.
                eapply in_nr_ut_sub in Heqsfn; eauto; exrepnd; ginv; auto. }
              exists (oterm Exc l0).
              unflsubst; simpl; dands; eauto 4 with slow.

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                autorewrite with slow; eauto 3 with slow.
              }

              introv nrut' eqdoms disj'.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan (NCompOp CompOpEq))
                                   (nobnd (mk_var x) :: nobnd (oterm Exc l0) :: bs))) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.

              unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
              csunf; simpl; boolvar; allsimpl; tcsp; GC.
              eexists; dands; eauto.
              unflsubst.

          - destruct bs; simpl in *; ginv.
            destruct b as [l1 u1]; simpl in *.
            inversion comp0; subst; simpl in *; clear comp0.
            repndors; exrepnd; subst; simpl in *; autorewrite with slow in *.

            { rewrite <- cl_lsubst_lsubst_aux in comp1; eauto 3 with slow;[].
              apply nt_wf_swap_cs1_iff in wf; exrepnd.
              inversion wf1; subst; clear wf1; simpl in *.
              eapply ind in comp1; try (right; left); eauto; eauto 3 with slow;
                try (complete (eapply nr_ut_sub_change_term; try exact nrut; simpl; autorewrite with slow; eauto 3 with slow));
                try (complete (eapply subset_disjoint_r; try exact disj;
                               apply subset_get_utokens_implies_subset_get_utokens_lib;
                               simpl; autorewrite with slow; eauto 3 with slow)).
              exrepnd; autorewrite with slow in *.
              exists (oterm (NCan NSwapCs1) [nobnd (mk_var x), nobnd w, nobnd c]).
              simpl; autorewrite with slow.
              dands; fold_terms; eauto 4 with slow.
              { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow;[].
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                  apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
                rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan NSwapCs1)
                                   [nobnd (mk_var x), nobnd b, nobnd c])) as h;
                repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
              unfold mk_utoken; rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow;
                try (eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto; eauto 3 with slow);[].
              pose proof (comp0 sub') as comp0; repeat (autodimp comp0 hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term; try exact nrut'; simpl; autorewrite with slow; eauto 3 with slow. }
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              exrepnd; unflsubst in comp0; allrw.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow; allrw.
              apply alpha_eq_oterm_combine; simpl; dands; auto.
              introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
              rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }

            { rewrite <- cl_lsubst_lsubst_aux in comp1; eauto 3 with slow;[].
              apply nt_wf_swap_cs0_iff in wf; exrepnd.
              inversion wf1; subst; clear wf1; simpl in *.
              eapply ind in comp1; try (right; left); eauto; eauto 3 with slow;
                try (complete (eapply nr_ut_sub_change_term; try exact nrut; simpl; autorewrite with slow; eauto 3 with slow));
                try (complete (eapply subset_disjoint_r; try exact disj;
                               apply subset_get_utokens_implies_subset_get_utokens_lib;
                               simpl; autorewrite with slow; eauto 3 with slow)).
              exrepnd; autorewrite with slow in *.
              exists (oterm (NCan NSwapCs0) [nobnd (mk_var x), nobnd w, nobnd c]).
              simpl; autorewrite with slow.
              dands; fold_terms; eauto 4 with slow.
              { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow;[].
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                  apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
                rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan NSwapCs0)
                                   [nobnd (mk_var x), nobnd b, nobnd c])) as h;
                repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
              unfold mk_utoken; rewrite compute_step_swap_cs0_if_isnoncan_like; eauto 3 with slow;
                try (eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto; eauto 3 with slow);[].
              pose proof (comp0 sub') as comp0; repeat (autodimp comp0 hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term; try exact nrut'; simpl; autorewrite with slow; eauto 3 with slow. }
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              exrepnd; unflsubst in comp0; allrw.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow; allrw.
              apply alpha_eq_oterm_combine; simpl; dands; auto.
              introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
              rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }

            { exists u1; dands; try unflsubst; eauto 3 with slow.
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              { apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              eapply isexc_lsubst_aux_nr_ut_sub in comp0; eauto.
              applydup @isexc_implies2 in comp0; exrepnd; subst; simpl in *; GC.
              unflsubst; csunf; simpl; autorewrite with slow.
              eapply sub_find_some_eq_doms_nr_ut_sub in eqdoms; try rewrite Heqsf in eqdoms; eauto.
              exrepnd; allrw; simpl; eexists; dands; eauto.
              unflsubst. }

            { exists u1; dands; try unflsubst; eauto 3 with slow.
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              { apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              eapply isexc_lsubst_aux_nr_ut_sub in comp0; eauto.
              applydup @isexc_implies2 in comp0; exrepnd; subst; simpl in *; GC.
              unflsubst; csunf; simpl; autorewrite with slow.
              eapply sub_find_some_eq_doms_nr_ut_sub in eqdoms; try rewrite Heqsf in eqdoms; eauto.
              exrepnd; allrw; simpl; eexists; dands; eauto.
              unflsubst. }

          - destruct bs; simpl in *; ginv.
            exists (@mk_var o x).
            simpl; autorewrite with slow.
            dands; fold_terms; eauto 4 with slow.
            { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow; allrw; auto. }
            introv nrut' eqdoms disj'.
            pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' x (oterm (NCan (NSwapCs2 nfo)) [nobnd (mk_var x)])) as h;
              repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; allrw.
            unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
            csunf; simpl; eexists; dands; eauto.
            unfold push_swap_cs_can; simpl.
            unflsubst; simpl; autorewrite with slow; allrw; auto.

(*          - destruct bs; simpl in *; ginv.
            destruct b as [l1 u1]; simpl in *.
            inversion comp0; subst; simpl in *; clear comp0.
            repndors; exrepnd; subst; simpl in *; autorewrite with slow in *.

            { rewrite <- cl_lsubst_lsubst_aux in comp1; eauto 3 with slow;[].
              apply nt_wf_swap_cs_iff in wf; exrepnd.
              inversion wf1; subst; clear wf1; simpl in *.
              eapply ind in comp1; try (right; left); eauto; eauto 3 with slow;
                try (complete (eapply nr_ut_sub_change_term; try exact nrut; simpl; autorewrite with slow; eauto 3 with slow));
                try (complete (eapply subset_disjoint_r; try exact disj;
                               apply subset_get_utokens_implies_subset_get_utokens_lib;
                               simpl; autorewrite with slow; eauto 3 with slow)).
              exrepnd; autorewrite with slow in *.
              exists (oterm (NCan NSwapCs) [nobnd (mk_var x), nobnd w, nobnd c]).
              simpl; autorewrite with slow.
              dands; fold_terms; eauto 4 with slow.
              { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow;[].
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                  apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
                rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan NSwapCs)
                                   [nobnd (mk_var x), nobnd b, nobnd c])) as h;
                repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
              unfold mk_utoken; rewrite compute_step_swap_cs_if_isnoncan_like; eauto 3 with slow;
                try (eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp2; eauto; eauto 3 with slow).
              pose proof (comp0 sub') as comp0; repeat (autodimp comp0 hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term; try exact nrut'; simpl; autorewrite with slow; eauto 3 with slow. }
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              exrepnd; unflsubst in comp0; allrw.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow; allrw.
              apply alpha_eq_oterm_combine; simpl; dands; auto.
              introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
              rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }

            { exists u1; dands; try unflsubst; eauto 3 with slow.
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              { apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              eapply isexc_lsubst_aux_nr_ut_sub in comp0; eauto.
              applydup @isexc_implies2 in comp0; exrepnd; subst; simpl in *; GC.
              unflsubst; csunf; simpl; autorewrite with slow.
              eapply sub_find_some_eq_doms_nr_ut_sub in eqdoms; try rewrite Heqsf in eqdoms; eauto.
              exrepnd; allrw; simpl; eexists; dands; eauto.
              unflsubst. }*)

          - repeat (destruct bs; allsimpl; ginv).
            destruct b as [l1 u1].
            destruct b0 as [l2 u2]; allsimpl.
            destruct l1, l2; ginv; boolvar; tcsp; GC; fold_terms; ginv.
            repndors; repnd; subst; allrw @sub_filter_nil_r.

            + exists u1; unflsubst; dands; eauto 4 with slow.

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                autorewrite with slow; eauto 3 with slow.
              }

              introv nrut' eqdoms disj'.
              unflsubst; simpl; boolvar.
              allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan (NCanTest CanIsuatom))
                                   [nobnd (mk_var x), nobnd u1, nobnd u2])) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              csunf; simpl; eexists; dands; eauto.
              unflsubst.

            + exists u2; unflsubst; dands; eauto 4 with slow.

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                autorewrite with slow; eauto 3 with slow.
              }

              introv nrut' eqdoms disj'.
              unflsubst; simpl; boolvar.
              allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            lib sub sub' x
                            (oterm (NCan (NCanTest x0))
                                   [nobnd (mk_var x), nobnd u1, nobnd u2])) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              csunf; simpl; eexists; dands; eauto.
              unflsubst.
              destruct x0; sp.
        }

        dopid op as [can2|ncan2|exc2|abs2] SSCase.

        * SSCase "Can".
          dopid_noncan ncan SSSCase.

          { SSSCase "NApply".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; fold_terms.

            { repeat (destruct bs; allsimpl; ginv).
              repeat (destruct bts; allsimpl; ginv).
              destruct b0 as [l1 u1].
              destruct b1 as [l2 u2].
              destruct l1; allsimpl; ginv; fold_terms; cpx.
              allrw @sub_filter_nil_r.

              - exists (subst u2 v u1).
                rw <- @cl_lsubst_lsubst_aux; try (complete (boolvar; eauto with slow)).
                unfold subst.
                autorewrite with slow in *.
                dands; eauto 3 with slow.

                + pose proof (combine_sub_nest u2 [(v, u1)] sub) as h.
                  eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                  pose proof (combine_sub_nest u2 (sub_filter sub [v]) [(v, lsubst_aux u1 sub)]) as h.
                  eapply alpha_eq_trans;[apply h|]; clear h.
                  simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                  apply alpha_eq_lsubst_if_ext_eq; auto.
                  rw <- @cl_lsubst_lsubst_aux; eauto with slow.
                  unfold ext_alpha_eq_subs; simpl; introv i.
                  rw @sub_find_app; rw @sub_find_sub_filter_eq; rw memvar_singleton.
                  boolvar; simpl; boolvar; simpl; tcsp.
                  remember (sub_find sub v0) as sf; destruct sf; simpl; tcsp.

                + eapply subset_disjoint_r;[exact disj|]; simpl.
                  eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                  simpl; boolvar; unfold get_utokens_sub; simpl; autorewrite with slow;
                    [|apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; eauto 3 with slow];
                    apply implies_subset_app;
                    [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; eauto 3 with slow|].
                  eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib].
                  simpl; autorewrite with slow; eauto 3 with slow.

                + allrw remove_nvars_nil_l; allrw app_nil_r.
                  eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                  simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

                + autorewrite with slow.
                  eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                  apply subset_app; dands; eauto 3 with slow;
                    [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                     autorewrite with slow; eauto 3 with slow|].

                  unfold get_utokens_sub; simpl; boolvar; simpl;
                    unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 3 with slow.

                + introv nrut' eqdoms diff'.
                  unflsubst; simpl; allrw @sub_filter_nil_r.
                  csunf; simpl.
                  allrw <- @cl_lsubst_lsubst_aux; eauto with slow.
                  eexists; dands; eauto.
                  unfold apply_bterm; simpl.

                  pose proof (combine_sub_nest u2 [(v,u1)] sub') as h.
                  eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                  pose proof (combine_sub_nest u2 (sub_filter sub' [v]) [(v, lsubst u1 sub')]) as h.
                  eapply alpha_eq_trans;[apply h|]; clear h.
                  simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                  apply alpha_eq_lsubst_if_ext_eq; auto.
                  unfold ext_alpha_eq_subs; simpl; introv i.
                  rw @sub_find_app; rw @sub_find_sub_filter_eq; rw memvar_singleton.
                  boolvar; simpl; boolvar; simpl; tcsp.
                  remember (sub_find sub' v0) as sf; destruct sf; simpl; tcsp.
            }

            { destruct bts; ginv.
              repeat (destruct bs; allsimpl; ginv).
              destruct b as [l t].
              destruct l; allsimpl; ginv.
              allrw @sub_filter_nil_r; fold_terms; ginv.
              allrw app_nil_r; allrw remove_nvars_nil_l.

              exists (mk_eapply (mk_choice_seq n) t).
              simpl; autorewrite with slow in *.
              dands; eauto 3 with slow.

              - unflsubst; simpl.
                allrw @sub_filter_nil_r; fold_terms; auto.

              - introv nrut' eqdoms diff'.
                unflsubst; simpl; allrw @sub_filter_nil_r; fold_terms.
                csunf; simpl.
                eexists; dands; eauto.

                unflsubst; simpl.
                allrw @sub_filter_nil_r; fold_terms; auto.
            }
          }

          { SSSCase "NEApply".

            unflsubst in comp; allsimpl.
            apply nt_wf_eapply_iff in wf; exrepnd; ginv.
            csunf comp; allsimpl.
            eapply compute_step_eapply_success in comp; exrepnd.
            allunfold @nobnd; allsimpl; ginv; autorewrite with slow in *.
            allrw disjoint_app_r; repnd.

            repndors; exrepnd; subst.

            - apply compute_step_eapply2_success in comp1; repnd; GC.
              repndors; exrepnd; allsimpl; subst; ginv.

              + repeat (destruct bts; allsimpl; ginv;[]).
                destruct b1; allsimpl; ginv.
                unfold mk_lam in comp3; ginv; autorewrite with slow in *.
                unfold apply_bterm; simpl.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                exists (subst n v b).
                allsimpl; autorewrite with slow in *.

                dands; eauto 3 with slow.

                * eapply alpha_eq_trans;[apply combine_sub_nest|].
                  eapply alpha_eq_trans;[|apply alpha_eq_sym; apply combine_sub_nest].
                  simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow;[].
                  apply alpha_eq_lsubst_if_ext_eq; auto.
                  unfold ext_alpha_eq_subs; simpl; introv i.
                  rw @sub_find_app; allrw @sub_find_sub_filter_eq; allrw memvar_cons.
                  boolvar; simpl; boolvar; simpl; tcsp; GC;[].
                  remember (sub_find sub v0) as sf; destruct sf; simpl; tcsp.

                * eapply disjoint_eqset_r;[apply eqset_sym;apply get_utokens_lib_subst|].
                  allrw disjoint_app_r; dands; eauto 3 with slow.
                  boolvar; eauto 3 with slow.

                * eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                  simpl; allrw subvars_app_l; dands; eauto 3 with slow.
                  boolvar; simpl; autorewrite with slow; eauto 3 with slow.

                * autorewrite with slow.
                  eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                  apply subset_app; dands; eauto 3 with slow;
                    [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                     autorewrite with slow; eauto 3 with slow|].

                  unfold get_utokens_sub; simpl; boolvar; simpl;
                    unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 3 with slow.

                * introv nrut' eqdoms diff'.
                  unflsubst; simpl; autorewrite with slow in *.
                  fold_terms; unfold mk_eapply.
                  rw @compute_step_eapply_lam_iscan; eauto 3 with slow;[].
                  eexists; dands; eauto.
                  repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).

                  eapply alpha_eq_trans;[|apply alpha_eq_sym; apply combine_sub_nest].
                  eapply alpha_eq_trans;[apply combine_sub_nest|].
                  simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow;[].
                  apply alpha_eq_lsubst_if_ext_eq; auto.
                  unfold ext_alpha_eq_subs; simpl; introv i.
                  rw @sub_find_app; rw @sub_find_sub_filter_eq; rw memvar_singleton.
                  boolvar; simpl; boolvar; simpl; tcsp.
                  remember (sub_find sub' v0) as sf; destruct sf; simpl; tcsp.

              + allunfold @mk_choice_seq; destruct bts; allsimpl; ginv; allsimpl; fold_terms.
                eapply lsubst_aux_equal_mk_nat in comp4;[|eauto]; subst; allsimpl.
                exists (CSVal2term v).
                unflsubst; simpl; fold_terms; autorewrite with slow.

                dands; eauto 3 with slow;[|].

                {
                  unfold get_utokens_lib; simpl; autorewrite with slow.
                  repeat (apply implies_subset_app); eauto 4 with slow.
                }

                introv nrut' eqdoms diff'.
                unflsubst; simpl; fold_terms.
                csunf; simpl; dcwf h; simpl; boolvar; try omega;[].
                rw Znat.Nat2Z.id.
                unflsubst; allrw; autorewrite with slow.
                eexists; dands; eauto.

            - eapply isexc_lsubst_aux_nr_ut_sub in comp0; eauto;[].
              apply wf_isexc_implies in comp0; exrepnd; subst; allsimpl; autorewrite with slow in *; auto;[].
              allrw disjoint_app_r; repnd.
              exists (mk_exception a e); unflsubst; simpl; autorewrite with slow in *.
              allrw disjoint_app_r.
              allrw subvars_app_l.
              allrw @oappl_app_as_oapp.
              allrw @oeqset_oappl_cons; autorewrite with slow in *.
              dands; eauto 3 with slow.

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                autorewrite with slow; eauto 3 with slow.
              }

              introv nrut' eqdoms' disj'.
              allrw disjoint_app_r; repnd.
              unflsubst; simpl; autorewrite with slow in *.
              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isexc; simpl; eauto 3 with slow;
              [|eapply eapply_wf_def_len_implies;[|eauto];
                allrw map_map; unfold compose;
                apply eq_maps; introv i; destruct x; simpl; unfold num_bvars; simpl; auto].
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow in *; auto.

            - pose proof (ind b b []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow;[].
              pose proof (h x sub) as ih; clear h.
              rw <- @cl_lsubst_lsubst_aux in comp1; eauto 3 with slow;[].
              repeat (autodimp ih hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term;[| |exact nrut]; simpl;
                autorewrite with slow in *; eauto 3 with slow. }
              exrepnd.

              exists (mk_eapply (oterm (Can can2) bts) w).
              unflsubst; simpl; autorewrite with slow in *.
              allrw disjoint_app_r; repnd.
              allrw subvars_app_l.
              allrw @oappl_app_as_oapp.
              allrw @oeqset_oappl_cons; autorewrite with slow in *.
              rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
              dands; eauto 3 with slow.

              + prove_alpha_eq3.

              + unfold get_utokens_lib; simpl; autorewrite with slow.
                repeat (apply implies_subset_app); eauto 4 with slow.
                eapply subset_trans;[apply get_utokens_subset_get_utokens_lib|].
                eapply subset_trans;[eauto|].
                unfold get_utokens_lib;  simpl; autorewrite with slow; eauto 3 with slow.

              + introv nrut' eqdoms' disj'.
                unflsubst; simpl; autorewrite with slow in *.
                eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto;[].
                fold_terms; unfold mk_eapply.
                rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow;
                [|eapply eapply_wf_def_len_implies;[|eauto];
                  allrw map_map; unfold compose;
                  apply eq_maps; introv i; destruct x0; simpl; unfold num_bvars; simpl; auto];
                [].
                pose proof (ih0 sub') as h'; clear ih0.
                repeat (autodimp h' hyp); eauto 3 with slow.

                {
                  eapply nr_ut_sub_change_term;[| |exact nrut']; simpl;
                    autorewrite with slow; eauto 3 with slow.
                }

                {
                  eapply subset_disjoint_r;[eauto|].
                  apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                  autorewrite with slow; eauto 3 with slow.
                }

                exrepnd.
                unflsubst in h'1.
                rw h'1.
                eexists; dands; eauto.
                unflsubst; simpl; autorewrite with slow.
                unflsubst in h'0.
                prove_alpha_eq3.
          }

(*          { SSSCase "NApseq".

            clear ind.
            unflsubst in comp; allsimpl.
            csunf comp; allsimpl.
            apply compute_step_apseq_success in comp; exrepnd; subst; allsimpl.
            repeat (destruct bts; allsimpl; ginv).
            repeat (destruct bs; allsimpl; ginv).
            fold_terms.

            exists (@mk_nat o (n n0)).
            unflsubst; simpl; fold_terms.
            autorewrite with slow.
            dands; eauto 3 with slow.
            introv nrut' eqdoms diff'.
            unflsubst; simpl.
            csunf; simpl.
            boolvar; try omega.
            rw @Znat.Nat2Z.id.
            eexists; dands; eauto.
          }*)

          { SSSCase "NFix".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_fix_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            allrw @sub_filter_nil_r.
            exists (mk_apply (oterm (Can can2) bts) (mk_fix (oterm (Can can2) bts))).
            unflsubst; simpl; autorewrite with slow.
            allrw @oappl_app_as_oapp.
            allrw @oeqset_oappl_cons; autorewrite with slow in *.
            allrw @osubset_oapp_left_iff.
            allrw disjoint_app_r; repnd.
            allrw subset_app.

            dands; simpl; eauto 3 with slow;
              try (complete (eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib];
                             simpl; autorewrite with slow; eauto 3 with slow)).

            { introv nrut' eqdoms diff'.
              unflsubst; simpl; allrw @sub_filter_nil_r.
              csunf; simpl.
              eexists; dands; eauto.
              unflsubst; simpl; allrw @sub_filter_nil_r; auto.
            }
          }

          { SSSCase "NSpread".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_spread_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).
            destruct b0 as [l1 u1].
            destruct b1 as [l2 u2].
            destruct b2 as [l3 u3].
            destruct l1; allsimpl; ginv; fold_terms; cpx.
            autorewrite with slow in *.
            allunfold @nobnd; ginv; allsimpl.

            - exists (lsubst u1 [(va,u2),(vb,u3)]).
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              dands.

              + pose proof (combine_sub_nest u1 [(va,u2),(vb,u3)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub [va,vb]) [(va,lsubst u2 sub),(vb,lsubst u3 sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.

              + eapply subset_disjoint_r;[exact disj|]; simpl.
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                csunf; simpl; allrw @sub_filter_nil_r.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @lsubst_aux_nil.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                pose proof (combine_sub_nest u1 [(va,u2),(vb,u3)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub' [va,vb]) [(va,lsubst u2 sub'),(vb,lsubst u3 sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v) as sf; destruct sf; simpl; tcsp.
          }

          { SSSCase "NDsup".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_dsup_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).
            destruct b0 as [l1 u1].
            destruct b1 as [l2 u2].
            destruct b2 as [l3 u3].
            destruct l1; allsimpl; ginv; fold_terms; cpx.
            autorewrite with slow in *.
            allunfold @nobnd; ginv; allsimpl.

            - exists (lsubst u1 [(va,u2),(vb,u3)]).
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              dands.

              + pose proof (combine_sub_nest u1 [(va,u2),(vb,u3)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub [va,vb]) [(va,lsubst u2 sub),(vb,lsubst u3 sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.

              + eapply subset_disjoint_r;[exact disj|]; simpl.
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                csunf; simpl; allrw @sub_filter_nil_r.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @lsubst_aux_nil.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                pose proof (combine_sub_nest u1 [(va,u2),(vb,u3)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub' [va,vb]) [(va,lsubst u2 sub'),(vb,lsubst u3 sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v) as sf; destruct sf; simpl; tcsp.
          }

          { SSSCase "NDecide".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_decide_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).
            destruct b0 as [l1 u1].
            destruct b1 as [l2 u2].
            destruct b as [l3 u3].
            destruct l1; allsimpl; ginv; fold_terms; cpx.
            autorewrite with slow in *.
            allunfold @nobnd; ginv; allsimpl.

            repndors; repnd; subst; ginv; cpx; allrw memvar_singleton.

            - exists (subst u3 v1 u2).
              unfold subst.
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              dands.

              + pose proof (combine_sub_nest u3 [(v1,u2)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u3 (sub_filter sub [v1]) [(v1,lsubst u2 sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.

              + eapply subset_disjoint_r;[exact disj|]; simpl.
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                allrw @sub_filter_nil_r; allsimpl.
                csunf; simpl.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @lsubst_aux_nil.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                pose proof (combine_sub_nest u3 [(v1,u2)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u3 (sub_filter sub' [v1]) [(v1,lsubst u2 sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v) as sf; destruct sf; simpl; tcsp.

            - exists (subst u1 v2 u2).
              unfold subst.
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              dands.

              + pose proof (combine_sub_nest u1 [(v2,u2)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub [v2]) [(v2,lsubst u2 sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v) as sf; destruct sf; simpl; tcsp.

              + eapply subset_disjoint_r;[exact disj|]; simpl.
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                allrw @sub_filter_nil_r; allsimpl.
                csunf; simpl.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @lsubst_aux_nil.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                pose proof (combine_sub_nest u1 [(v2,u2)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub' [v2]) [(v2,lsubst u2 sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v) as sf; destruct sf; simpl; tcsp.
          }

          { SSSCase "NCbv".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_cbv_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            destruct b as [l1 u1].
            destruct l1; allsimpl; ginv; fold_terms; cpx.
            autorewrite with slow in *.

            - exists (subst u1 v (oterm (Can can2) bts)).
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              unfold subst.
              dands.

              + pose proof (combine_sub_nest u1 [(v,oterm (Can can2) bts)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub [v]) [(v, lsubst_aux (oterm (Can can2) bts) sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v0) as sf; destruct sf; simpl; tcsp.

              + eapply subset_disjoint_r;[exact disj|]; simpl.
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_lsubst|].
                apply subset_app; dands; eauto 3 with slow;
                  [apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                   autorewrite with slow; eauto 3 with slow|].

                unfold get_utokens_sub; simpl; boolvar; simpl;
                  unfold get_utokens_lib; simpl;
                    autorewrite with slow; eauto 4 with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                allrw @sub_filter_nil_r.
                csunf; simpl.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @lsubst_aux_nil.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

                pose proof (combine_sub_nest u1 [(v,oterm (Can can2) bts)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u1 (sub_filter sub' [v]) [(v, lsubst_aux (oterm (Can can2) bts) sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v0) as sf; destruct sf; simpl; tcsp.
          }

          { SSSCase "NSleep".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_sleep_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).

            - exists (@mk_axiom o).
              unflsubst; simpl; dands; eauto 3 with slow.

              introv nrut' eqdoms diff'.
              repeat (unflsubst; simpl).
              csunf; simpl.
              unfold compute_step_sleep; simpl.
              eexists; dands; eauto.
          }

          { SSSCase "NTUni".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_tuni_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).

            - exists (@mk_uni o 0 n).
              unflsubst; simpl; dands; eauto 3 with slow.

              introv nrut' eqdoms diff'.
              repeat (unflsubst; simpl).
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              eexists; dands; eauto.
              rw Znat.Nat2Z.id; auto.
          }

          { SSSCase "NMinus".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            apply compute_step_minus_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).

            - exists (@mk_integer o (- z)).
              unflsubst; simpl; dands; eauto 3 with slow.

              introv nrut' eqdoms diff'.
              repeat (unflsubst; simpl).
              csunf; simpl.
              unfold compute_step_minus; simpl.
              eexists; dands; eauto.
          }

          { SSSCase "NFresh".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp; ginv.
          }

          { SSSCase "NTryCatch".

            clear ind; unflsubst in comp; allsimpl; csunf comp; simpl in comp.
            allrw @sub_filter_nil_r.
            apply compute_step_try_success in comp; exrepnd; subst; fold_terms.
            repeat (destruct bs; allsimpl; ginv).
            destruct b as [l1 u1].
            destruct b0 as [l2 u2].
            destruct l1; allsimpl; ginv; fold_terms; cpx.

            - exists (mk_atom_eq u1 u1 (oterm (Can can2) bts) mk_bot).
              unflsubst; simpl.
              allrw @sub_filter_nil_r; allrw app_nil_r; allrw @remove_nvars_nil_l.
              allrw @sub_find_sub_filter_eq; allrw memvar_singleton.
              allrw <- beq_var_refl; simpl; fold_terms.
              allrw subvars_app_l.
              allrw subset_app.
              allrw disjoint_app_r; repnd.
              allrw @oappl_app_as_oapp; autorewrite with slow in *.
              allrw @oeqset_oappl_cons; autorewrite with slow in *.
              allrw @osubset_oapp_left_iff; autorewrite with slow.

              dands; simpl; eauto 3 with slow;
                try (complete (eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib];
                               simpl; autorewrite with slow; eauto 3 with slow)).

              introv nrut' eqdoms diff'.
              unflsubst; simpl; allrw @sub_filter_nil_r.
              csunf; simpl.
              eexists; dands; eauto.
              unflsubst.
              simpl.
              allrw @sub_filter_nil_r; allrw app_nil_r; allrw @remove_nvars_nil_l.
              allrw @sub_find_sub_filter_eq; allrw memvar_singleton.
              allrw <- beq_var_refl; auto.
          }

          { SSSCase "NParallel".
            unflsubst in comp; allsimpl.
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; subst; allsimpl.
            exists (@mk_axiom o).
            unflsubst; simpl; fold_terms.
            dands; autorewrite with slow in *; eauto 3 with slow.

            {
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; auto.
            }

            introv nrut' eqdoms disj'.
            exists (@mk_axiom o); allsimpl.
            rw (@cl_lsubst_trivial o mk_axiom); simpl; dands; eauto 3 with slow.
            unflsubst.
          }

          { SSSCase "NSwapCs1".
            unflsubst in comp; allsimpl.
            csunf comp; simpl in *.
            apply compute_step_swap_cs1_success in comp; repndors; exrepnd; subst; ginv; simpl in *.

            { repeat (destruct bs; simpl in *; tcsp).
              destruct b, b0; simpl in *.
              inversion comp2; subst; simpl in *; autorewrite with slow in *; clear comp2.
              destruct bts; simpl in *; tcsp; GC; fold_terms.
              match goal with [ H : lsubst_aux _ _ = oterm (Can (Ncseq _)) _ |- _ ] => rename H into eql end.
              eapply nr_ut_lsubst_aux_choice_seq_implies in eql; eauto; subst; simpl in *.

              exists (mk_swap_cs2 n1 n2 n0).
              unflsubst; simpl; autorewrite with slow.
              dands; eauto 3 with slow.
              introv nrut' eqdoms disj'.
              unflsubst; csunf; simpl; eexists; dands; eauto; autorewrite with slow; eauto 3 with slow.
              rewrite lsubst_mk_swap_cs2_choice_seq_var_ren; eauto 3 with slow; try unflsubst. }

            { destruct bs; simpl in *; tcsp; ginv.
              destruct b; simpl in *.
              inversion comp0; subst; simpl in *; autorewrite with slow in *; clear comp0.
              match goal with [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eql end.
              eapply nr_ut_lsubst_aux_exc_implies in eql; eauto; subst; simpl in *.
              exrepnd; subst; simpl in *.
              exists (oterm Exc k).
              unflsubst; simpl; dands; eauto 3 with slow.
              { eapply subset_disjoint_r; eauto.
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto; eauto 3 with slow. }
              { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              unflsubst; csunf; simpl; eexists; dands; eauto; autorewrite with slow.
              unflsubst; rewrite <- lsubst_aux_swap_cs_term. }

            { destruct bs; simpl in *; tcsp; ginv.
              destruct b; simpl in *.
              inversion comp0; subst; simpl in *; autorewrite with slow in *; clear comp0.
              match goal with [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eql end.
              rewrite <- cl_lsubst_lsubst_aux in comp2; eauto 3 with slow;[].
              apply nt_wf_swap_cs1_iff in wf; exrepnd.
              inversion wf1; subst; simpl in *; clear wf1; autorewrite with slow in *.
              eapply ind in comp2; try (right; left); eauto; eauto 3 with slow;
                try (complete (eapply nr_ut_sub_change_term; try exact nrut; simpl; autorewrite with slow; eauto 3 with slow));
                try (complete (eapply subset_disjoint_r; try exact disj;
                               apply subset_get_utokens_implies_subset_get_utokens_lib;
                               simpl; autorewrite with slow; eauto 3 with slow));[].
              exrepnd; autorewrite with slow in *.
              exists (oterm (NCan NSwapCs1) [nobnd (oterm (Can can2) bts), nobnd w, nobnd c]).
              simpl; autorewrite with slow.
              dands; fold_terms; eauto 4 with slow.
              { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow;[].
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                  apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
                rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              unflsubst; simpl; autorewrite with slow in *.
              dup comp3 as isn; rewrite <- eql in isn.
              eapply isnoncan_like_lsubst_aux_nr_ut_implies in isn; eauto.
              rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow.
              pose proof (comp0 sub') as comp0.
              repeat (autodimp comp0 hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term; try exact nrut'; simpl; autorewrite with slow; eauto 3 with slow. }
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              exrepnd; unflsubst in comp0; allrw.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow; allrw.
              apply alpha_eq_oterm_combine; simpl; dands; auto.
              introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
              rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
          }

          { SSSCase "NSwapCs2".
            unflsubst in comp; allsimpl.
            csunf comp; simpl in *.
            apply compute_step_swap_cs2_success in comp; repndors; exrepnd; subst; ginv; simpl in *.

            repeat (destruct bs; simpl in *; tcsp; GC); autorewrite with slow.
            exists (push_swap_cs_can (swap_cs_nfo_name1 s) (swap_cs_nfo_name2 s) can2 bts).
            unflsubst; simpl; autorewrite with slow.
            dands; eauto 3 with slow.
            { apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
              unfold push_swap_cs_bterms; introv i; rewrite <- map_combine in i.
              apply in_map_iff in i; exrepnd; ginv.
              rewrite <- map_combine in i1; apply in_map_iff in i1; exrepnd; ginv.
              apply in_combine_same in i1; repnd; subst.
              destruct a1; simpl; apply alpha_eq_bterm_congr; fold_terms; autorewrite with slow; tcsp.
              rewrite lsubst_aux_nr_ut_sub_push_swap_cs_sub_term; eauto 3 with slow;
                try (apply disjoint_sym; apply disjoint_dom_sub_filt). }
            { eapply subset_disjoint_r; eauto.
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto. }
            { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto. }
            introv nrut' eqdoms disj'.
            unflsubst; csunf; simpl; eexists; dands; eauto; autorewrite with slow.
            unflsubst; simpl.
            apply alpha_eq_oterm_combine; autorewrite with slow; dands; auto.
            unfold push_swap_cs_bterms; introv i; rewrite <- map_combine in i.
            apply in_map_iff in i; exrepnd; ginv.
            rewrite <- map_combine in i1; apply in_map_iff in i1; exrepnd; ginv.
            apply in_combine_same in i1; repnd; subst.
            destruct a1; simpl; apply alpha_eq_bterm_congr; fold_terms; autorewrite with slow; tcsp.
            rewrite lsubst_aux_nr_ut_sub_push_swap_cs_sub_term; eauto 3 with slow;
              try (apply disjoint_sym; apply disjoint_dom_sub_filt). }

          { SSSCase "NSwapCs0".
            unflsubst in comp; allsimpl.
            csunf comp; simpl in *.
            apply compute_step_swap_cs0_success in comp; repndors; exrepnd; subst; ginv; simpl in *.

            { repeat (destruct bs; simpl in *; tcsp).
              destruct b, b0; simpl in *.
              inversion comp2; subst; simpl in *; autorewrite with slow in *; clear comp2.
              destruct bts; simpl in *; tcsp; GC; fold_terms.
              match goal with [ H : lsubst_aux _ _ = oterm (Can (Ncseq _)) _ |- _ ] => rename H into eql end.
              eapply nr_ut_lsubst_aux_choice_seq_implies in eql; eauto; subst; simpl in *.

              exists (push_swap_cs_sub_term n1 n2 (remove_nvars (dom_sub sub) (free_vars n0)) (swap_cs_term (n1,n2) n0)).
              unfold push_swap_cs0, push_swap_cs_sub_term.
              unflsubst; simpl; autorewrite with slow.
              dands; eauto 3 with slow;
                try (complete (unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *; auto)).

              { eapply alpha_eq_trans;[|apply alpha_eq_sym;apply alpha_eq_lsubst_sw_sub_cl_sub]; eauto 3 with slow.
                rewrite free_vars_lsubst_aux_cl; eauto 3 with slow.
                repeat rewrite <- lsubst_aux_swap_cs_term.
                repeat (erewrite swap_cs_sub_if_nr_ut_sub; eauto). }

              introv nrut' eqdoms disj'.
              unflsubst; csunf; simpl; eexists; dands; eauto; autorewrite with slow; eauto 3 with slow.
              unfold push_swap_cs0, push_swap_cs_sub_term.
              unflsubst; simpl; autorewrite with slow.
              rewrite eqdoms.
              eapply alpha_eq_trans;[|apply alpha_eq_sym; apply alpha_eq_lsubst_sw_sub_cl_sub]; eauto 3 with slow.
              rewrite <- lsubst_aux_swap_cs_term.
              erewrite swap_cs_sub_if_nr_ut_sub; eauto.
              rewrite free_vars_lsubst_aux_cl; eauto 3 with slow. }

            { destruct bs; simpl in *; tcsp; ginv.
              destruct b; simpl in *.
              inversion comp0; subst; simpl in *; autorewrite with slow in *; clear comp0.
              match goal with [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eql end.
              eapply nr_ut_lsubst_aux_exc_implies in eql; eauto; subst; simpl in *.
              exrepnd; subst; simpl in *.
              exists (oterm Exc k).
              unflsubst; simpl; dands; eauto 3 with slow.
              { eapply subset_disjoint_r; eauto.
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto; eauto 3 with slow. }
              { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; autorewrite with slow; auto; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              unflsubst; csunf; simpl; eexists; dands; eauto; autorewrite with slow.
              unflsubst; rewrite <- lsubst_aux_swap_cs_term. }

            { destruct bs; simpl in *; tcsp; ginv.
              destruct b; simpl in *.
              inversion comp0; subst; simpl in *; autorewrite with slow in *; clear comp0.
              match goal with [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eql end.
              rewrite <- cl_lsubst_lsubst_aux in comp2; eauto 3 with slow;[].
              apply nt_wf_swap_cs0_iff in wf; exrepnd.
              inversion wf1; subst; simpl in *; clear wf1; autorewrite with slow in *.
              eapply ind in comp2; try (right; left); eauto; eauto 3 with slow;
                try (complete (eapply nr_ut_sub_change_term; try exact nrut; simpl; autorewrite with slow; eauto 3 with slow));
                try (complete (eapply subset_disjoint_r; try exact disj;
                               apply subset_get_utokens_implies_subset_get_utokens_lib;
                               simpl; autorewrite with slow; eauto 3 with slow));[].
              exrepnd; autorewrite with slow in *.
              exists (oterm (NCan NSwapCs0) [nobnd (oterm (Can can2) bts), nobnd w, nobnd c]).
              simpl; autorewrite with slow.
              dands; fold_terms; eauto 4 with slow.
              { rewrite cl_lsubst_lsubst_aux; eauto 3 with slow; simpl; autorewrite with slow;[].
                apply alpha_eq_oterm_combine; simpl; dands; auto.
                introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                  apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
                rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
              introv nrut' eqdoms disj'.
              unflsubst; simpl; autorewrite with slow in *.
              dup comp3 as isn; rewrite <- eql in isn.
              eapply isnoncan_like_lsubst_aux_nr_ut_implies in isn; eauto.
              rewrite compute_step_swap_cs0_if_isnoncan_like; eauto 3 with slow.
              pose proof (comp0 sub') as comp0.
              repeat (autodimp comp0 hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term; try exact nrut'; simpl; autorewrite with slow; eauto 3 with slow. }
              { eapply subset_disjoint_r; eauto; simpl.
                apply subset_get_utokens_implies_subset_get_utokens_lib.
                simpl; autorewrite with slow; eauto 3 with slow. }
              exrepnd; unflsubst in comp0; allrw.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow; allrw.
              apply alpha_eq_oterm_combine; simpl; dands; auto.
              introv xx; repndors; ginv; tcsp; eauto 3 with slow;
                apply alphaeqbt_nilv2; allrw; eauto 3 with slow.
              rewrite <- cl_lsubst_lsubst_aux; eauto 3 with slow. }
          }

          { SSSCase "NLDepth".
            unflsubst in comp; csunf comp; simpl in *; ginv. }

          { SSSCase "NLastCs".
            unflsubst in comp; allsimpl.
            csunf comp; allsimpl.
            apply compute_step_last_cs_success in comp.
            exrepnd; subst; allsimpl.
            repeat (destruct bts; simpl in *; ginv).
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *; destruct b; simpl in *; ginv;[].

            exists (find_last_entry_default lib name n).
            autorewrite with slow.

            unflsubst.
            rewrite lsubst_aux_find_last_entry_default.
            fold (@mk_choice_seq o name) in *; fold_terms.
            fold (@mk_last_cs o (mk_choice_seq name) n) in *.
            autorewrite with slow in *.
            dands; eauto 3 with slow.

            introv nrut' eqdoms disj'.
            csunf; simpl; allrw.
            eexists; dands; eauto.
            repeat unflsubst; rewrite lsubst_aux_find_last_entry_default.
            simpl; autorewrite with slow; auto.
          }

          { SSSCase "NCompSeq1".
            unflsubst in comp; allsimpl.
            csunf comp; allsimpl.
            apply compute_step_comp_seq1_success in comp.
            exrepnd; subst; allsimpl.
            repeat (destruct bts; simpl in *; ginv).
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *.
            destruct b; simpl in *.
            destruct l; ginv; simpl in *.
            repndors; repnd; subst.

            { exists (mk_fresh_choice_nat_seq a lib []); allsimpl.
              unflsubst; simpl.
              dands; auto; eauto 3 with slow;[].

              introv nrut' eqdoms disj'.
              exists (mk_fresh_choice_nat_seq a lib []); allsimpl.
              unflsubst. }

            autorewrite with slow.
            exists (mk_comp_seq2 a [] i (mk_apply n mk_zero) n).
            unflsubst; simpl.
            autorewrite with slow.
            dands; eauto 3 with slow.

            { introv x b; apply disj in x; destruct x.
              unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
              allrw in_app_iff; repndors; tcsp. }

            { introv z.
              unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
              allrw in_app_iff; repndors; tcsp. }

            introv nrut' eqdoms disj'.
            exists (mk_comp_seq2 a [] i (mk_apply (lsubst n sub') mk_zero) (lsubst n sub')).
            unflsubst; simpl.
            csunf; simpl.
            boolvar; autorewrite with slow in *; try omega;[].
            unflsubst; dands; auto.
            unflsubst; simpl; autorewrite with slow; auto.
          }

          { SSSCase "NCompSeq2".
            unflsubst in comp; allsimpl.
            csunf comp; allsimpl.
            apply compute_step_comp_seq2_success in comp.
            exrepnd; subst; allsimpl.
            repeat (destruct bts; simpl in *; ginv).
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *.
            destruct b; simpl in *.
            destruct l0; ginv; simpl in *.
            repndors; repnd; subst.

            { exists (mk_fresh_choice_nat_seq a lib (snoc l k)); allsimpl.
              unflsubst; simpl.
              dands; auto; eauto 3 with slow;[].

              introv nrut' eqdoms disj'.
              exists (mk_fresh_choice_nat_seq a lib (snoc l k)); allsimpl.
              unflsubst; simpl.
              dands; auto.
              csunf; simpl.
              boolvar; ginv; autorewrite with slow; try omega; auto. }

            autorewrite with slow.
            exists (mk_comp_seq2 a (snoc l k) i (mk_apply n (mk_nat (S (length l)))) n).
            unflsubst; simpl.
            autorewrite with slow.
            dands; eauto 3 with slow.

            { introv z b; apply disj in z; destruct z.
              unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
              allrw in_app_iff; repndors; tcsp. }

            { introv z.
              unfold get_utokens_lib in *; simpl in *; autorewrite with slow in *.
              allrw in_app_iff; repndors; tcsp. }

            introv nrut' eqdoms disj'.
            exists (mk_comp_seq2 a (snoc l k) i (mk_apply (lsubst n sub') (mk_nat (S (length l)))) (lsubst n sub')).
            unflsubst; simpl.
            csunf; simpl.
            boolvar; autorewrite with slow in *; try omega;[].
            unflsubst; dands; auto.
            unflsubst; simpl; autorewrite with slow; auto.
          }

          { SSSCase "NCompOp".

            unflsubst in comp; allsimpl.
            allrw @sub_filter_nil_r.
            apply compute_step_ncompop_can1_success in comp; repnd.
            repndors; exrepnd; subst.

            - (* Can case *)
              repeat (destruct bs; allsimpl; ginv).
              destruct b as [l1 u1].
              destruct b0 as [l2 u2].
              destruct b1 as [l3 u3].
              destruct l1; allsimpl; ginv; fold_terms.
              allrw @sub_filter_nil_r; allrw app_nil_r.
              allunfold @nobnd.
              repeat (apply cons_inj in comp1; repnd); GC; ginv.
              inversion comp2 as [epk]; clear comp2.
              fold_terms.
              apply compute_step_compop_success_can_can in comp1; exrepnd; subst; GC.
              repeat (destruct bts; allsimpl; ginv).
              autorewrite with slow in *.
              repndors; exrepnd; subst;
              allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.

              + allapply @lsubst_aux_eq_spcan_implies; repndors; exrepnd; allsimpl;
                subst; allsimpl; fold_terms; boolvar; ginv.

                * assert (sub_find sub v = Some (mk_integer n2)) as e by auto.
                  apply sub_find_some in e.
                  eapply in_nr_ut_sub in e; eauto; exrepnd; ginv.

                * assert (sub_find sub v = Some (mk_integer n2)) as e by auto.
                  apply sub_find_some in e.
                  eapply in_nr_ut_sub in e; eauto; exrepnd; ginv.

                * exists u2; unflsubst; allsimpl; autorewrite with slow in *.
                  allrw @oappl_app_as_oapp; autorewrite with slow in *.
                  allrw @oeqset_oappl_cons; autorewrite with slow in *.
                  allrw @osubset_oapp_left_iff; autorewrite with slow.
                  dands; eauto 4 with slow.

                  {
                    eapply subset_disjoint_r;[eauto|].
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 3 with slow.
                  }

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 3 with slow.
                  }

                  introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                  allrw @sub_filter_nil_r.
                  csunf; simpl; eexists; dands; eauto.
                  boolvar; allsimpl; tcsp; GC.
                  dcwf h; allsimpl;[].
                  unfold compute_step_comp; simpl.
                  boolvar; tcsp; try omega.
                  unflsubst.

                * exists u3; unflsubst; allsimpl; autorewrite with slow in *.
                  allrw @oappl_app_as_oapp; autorewrite with slow in *.
                  allrw @oeqset_oappl_cons; autorewrite with slow in *.
                  allrw @osubset_oapp_left_iff; autorewrite with slow.
                  dands; eauto 4 with slow.

                  {
                    eapply subset_disjoint_r;[eauto|].
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 3 with slow.
                  }

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 3 with slow.
                  }

                  introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                  allrw @sub_filter_nil_r.
                  csunf; simpl; boolvar; allsimpl; tcsp; GC.
                  dcwf h; allsimpl;[].
                  unfold compute_step_comp; simpl.
                  boolvar; tcsp; try omega.
                  eexists; dands; eauto.
                  unflsubst.

              + allapply @lsubst_aux_eq_spcan_implies; repndors; exrepnd; allsimpl; subst; allsimpl.

                * dup epk1 as sf.
                  eapply nr_ut_some_implies in sf; eauto; exrepnd;[].
                  rw <- @pk2term_eq in sf0.
                  apply pk2term_utoken in sf0; subst; allsimpl; fold_terms.

                  exists (if param_kind_deq pk1 (PKa a) then u2 else u3).
                  allrw disjoint_app_r; repnd.
                  autorewrite with slow in *.
                  allrw @oappl_app_as_oapp; autorewrite with slow in *.
                  allrw @oeqset_oappl_cons; autorewrite with slow in *.
                  allrw @osubset_oapp_left_iff; autorewrite with slow.
                  dands; boolvar; subst; eauto 3 with slow; try unflsubst;allsimpl.

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 3 with slow.
                  }

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    eauto 4 with slow.
                  }

                  { introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                    allrw disjoint_singleton_r.
                    apply sub_find_some in epk1.
                    destruct disj6.
                    apply in_get_utokens_sub.
                    eexists; eexists; dands; eauto; simpl; tcsp. }

                  { introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                    allrw @sub_filter_nil_r; allsimpl.

                    pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' v) as h.
                    applydup h in nrut'; auto; clear h;[].
                    rw epk1 in nrut'0; exrepnd.
                    rw nrut'1; allsimpl.

                    csunf; simpl.
                    dcwf h; allsimpl;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can.
                    unflsubst.
                    boolvar; eexists; dands; eauto.

                    subst; allsimpl.
                    allrw disjoint_cons_r; repnd.
                    apply sub_find_some in nrut'1.
                    rw @in_get_utokens_sub in diff'; destruct diff'.
                    eexists; eexists; dands; eauto; simpl; auto. }

                * exists (if param_kind_deq pk1 pk2 then u2 else u3).
                  allrw disjoint_app_r; repnd.
                  autorewrite with slow in *.
                  repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
                  repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
                  allrw @osubset_oapp_left_iff; autorewrite with slow.
                  dands; boolvar; subst; eauto 4 with slow; try unflsubst;allsimpl.

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    autorewrite with slow; eauto 4 with slow.
                  }

                  {
                    apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                    autorewrite with slow; eauto 4 with slow.
                  }

                  { introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                    allrw @sub_filter_nil_r; allsimpl.
                    csunf; simpl.
                    dcwf h; allsimpl;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; tcsp.
                    eexists; dands; eauto.
                    unflsubst. }

                  { introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                    allrw @sub_filter_nil_r; allsimpl.
                    csunf; simpl.
                    dcwf h; allsimpl;[].
                    unfold compute_step_comp; simpl.
                    allrw @get_param_from_cop_pk2can; boolvar; tcsp.
                    eexists; dands; eauto.
                    unflsubst. }

            - (* NCan/Abs Case *)
              destruct bs; allsimpl; ginv.
              destruct b as [l1 u1].
              destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl.
              allrw @sub_filter_nil_r.
              pose proof (ind u1 u1 []) as h.
              repeat (autodimp h hyp); clear ind; eauto 3 with slow.
              rw <- @cl_lsubst_lsubst_aux in comp4; eauto 3 with slow.
              allrw @nt_wf_NCompOp; exrepnd; ginv; allsimpl.
              autorewrite with slow in *.
              allrw disjoint_app_r; repnd.

              pose proof (h t' sub) as k; clear h.
              repeat (autodimp k hyp).

              {
                eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow.
              }

              {
                simpl in *; eauto 3 with slow.
              }

              exrepnd.
              exists (oterm (NCan (NCompOp c))
                            (nobnd (oterm (Can can2) bts)
                                   :: nobnd w
                                   :: nobnd t3
                                   :: nobnd t4
                                   :: [])).
              unflsubst; simpl.
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
              allrw @osubset_oapp_left_iff; autorewrite with slow.
              allrw subset_app.
              dands; simpl; autorewrite with slow; eauto 4 with slow;
                try (complete (eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib];
                               simpl; autorewrite with slow; eauto 4 with slow));
                try (complete (repnd; eapply subset_trans;[eauto|];
                               apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                               autorewrite with slow; eauto 4 with slow)).

              + prove_alpha_eq4; introv h; allrw map_length.
                destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in k1.

              + repeat (rw disjoint_app_r); dands; eauto with slow;
                eapply subset_disjoint_r; try (exact disj); simpl;
                  eauto with slow.

              + introv nrut' eqdoms diff'.
                unflsubst; simpl.
                allrw @sub_filter_nil_r.
                eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto.
                rw @compute_step_ncompop_ncanlike2; boolvar; allsimpl; tcsp; eauto with slow.
                dcwf h;[].
                pose proof (k0 sub') as h; repeat (autodimp h hyp).
                { eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
                { allsimpl; allrw disjoint_app_r; sp. }
                exrepnd.
                unflsubst in h1; rw h1.
                eexists; dands; eauto.
                unflsubst; simpl; allrw @sub_filter_nil_r.
                prove_alpha_eq4; introv h; allrw map_length.
                destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in h0.

            - (* Exc Case *)
              destruct bs; allsimpl; cpx;[].
              destruct b as [l1 u1].
              destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl;[].
              allrw @sub_filter_nil_r.
              assert (isexc u1) as ise.
              { eapply isexc_lsubst_aux_nr_ut_sub in comp1; eauto. }
              apply isexc_implies2 in ise; exrepnd; subst; allsimpl; GC.
              exists (oterm Exc l); unflsubst; simpl.
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              allrw @osubset_oapp_left_iff; autorewrite with slow.
              dands; autorewrite with slow; eauto 4 with slow.

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              introv nrut' eqdoms diff'.
              unflsubst; simpl; csunf; simpl; boolvar; allsimpl; tcsp.
              dcwf h;[].
              eexists; dands; eauto.
              allrw @sub_filter_nil_r.
              unflsubst.
          }

          { SSSCase "NArithOp".

            unflsubst in comp; allsimpl.
            apply compute_step_narithop_can1_success in comp; repnd.
            repndors; exrepnd; subst.

            - (* Can case *)
              repeat (destruct bs; allsimpl; ginv);[].
              destruct b as [l1 u1].
              destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl;[].
              allrw @sub_filter_nil_r.
              apply compute_step_arithop_success_can_can in comp1; exrepnd; subst; GC.
              repeat (destruct bts; allsimpl; ginv).
              autorewrite with slow in *.
              repndors; exrepnd; subst;
              allapply @get_param_from_cop_pki;
              allapply @get_param_from_cop_pka;
              allapply @get_param_from_cop_pks;
              subst; allsimpl; GC; fold_terms.

              assert (lsubst_aux u1 sub = mk_integer n2) as e by auto.
              allrw e; GC.

              allapply @lsubst_aux_eq_spcan_implies; repndors; exrepnd; allsimpl;
              subst; allsimpl; fold_terms; boolvar; ginv.

              * assert (sub_find sub v = Some (mk_integer n2)) as e by auto.
                apply sub_find_some in e.
                eapply in_nr_ut_sub in e; eauto; exrepnd; ginv.

              * exists (@mk_integer o (get_arith_op a n1 n2)); unflsubst; dands; simpl; eauto 3 with slow.
                introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                csunf; simpl; boolvar; allsimpl; tcsp; GC.
                dcwf h;allsimpl;[].
                eexists; dands; eauto.

            - (* NCan/Abs Case *)
              destruct bs; allsimpl; ginv.
              destruct b as [l1 u1].
              destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl.
              allrw @sub_filter_nil_r.
              pose proof (ind u1 u1 []) as h.
              repeat (autodimp h hyp); clear ind; eauto 3 with slow.
              rw <- @cl_lsubst_lsubst_aux in comp4; eauto 3 with slow.
              allrw @nt_wf_NArithOp; exrepnd; ginv; allsimpl.
              autorewrite with slow in *.
              allrw disjoint_app_r; repnd.

              pose proof (h t' sub) as k; clear h.
              repeat (autodimp k hyp).

              {
                eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow.
              }

              {
                simpl in *; eauto 3 with slow.
              }

              exrepnd.
              exists (oterm (NCan (NArithOp a))
                            (nobnd (oterm (Can can2) bts)
                                   :: nobnd w
                                   :: [])).
              unflsubst; simpl.
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
              allrw @osubset_oapp_left_iff; autorewrite with slow.
              dands; autorewrite with slow; eauto 4 with slow.

              + prove_alpha_eq4; introv h; allrw map_length; destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in k1.

              + repeat (rw disjoint_app_r); dands; eauto with slow;
                eapply subset_disjoint_r; try (exact disj); simpl;
                eauto with slow.

              + allrw subset_app.
                dands; simpl; autorewrite with slow; eauto 4 with slow;
                  try (complete (eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib];
                                 simpl; autorewrite with slow; eauto 4 with slow));
                  try (complete (repnd; eapply subset_trans;[eauto|];
                                 apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                                 autorewrite with slow; eauto 4 with slow)).

              + introv nrut' eqdoms diff'.
                unflsubst; simpl; allrw @sub_filter_nil_r.
                eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto.
                rw @compute_step_narithop_ncanlike2; boolvar; allsimpl; tcsp; eauto with slow.
                pose proof (k0 sub') as h; repeat (autodimp h hyp).
                { eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
                { allsimpl; allrw disjoint_app_r; sp. }
                exrepnd.
                unflsubst in h1; rw h1.
                dcwf h; allsimpl; [].
                eexists; dands; eauto.
                unflsubst; simpl; allrw @sub_filter_nil_r.
                prove_alpha_eq4; introv h; allrw map_length.
                destruct n; cpx.
                destruct n; cpx.
                apply alphaeqbt_nilv2.
                unflsubst in h0.

            - (* Exc Case *)
              destruct bs; allsimpl; cpx.
              destruct b as [l1 u1].
              destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl.
              allrw @sub_filter_nil_r.
              assert (isexc u1) as ise.
              { eapply isexc_lsubst_aux_nr_ut_sub in comp1; eauto. }
              apply isexc_implies2 in ise; exrepnd; subst; allsimpl; GC.
              exists (oterm Exc l); unflsubst; simpl.
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
              repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
              allrw @osubset_oapp_left_iff; autorewrite with slow.
              dands; autorewrite with slow; eauto 4 with slow.

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              introv nrut' eqdoms diff'.
              unflsubst; simpl; csunf; simpl; boolvar; allsimpl; tcsp.
              dcwf h; allsimpl; [].
              eexists; dands; eauto.
              allrw @sub_filter_nil_r.
              unflsubst.
          }

          { SSSCase "NCanTest".

            unflsubst in comp; allsimpl; csunf comp; allsimpl.
            autorewrite with slow in *.
            apply compute_step_can_test_success in comp; exrepnd.
            repeat (destruct bs; allsimpl; ginv).
            destruct b as [l1 u1].
            destruct b0 as [l2 u2].
            destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl.
            allrw @sub_filter_nil_r.
            exists (if canonical_form_test_for c can2 then u1 else u2).
            repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
            repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
            repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
            allrw @osubset_oapp_left_iff; autorewrite with slow.
            allrw disjoint_app_r; repnd.
            unflsubst; simpl; dands; autorewrite with slow; eauto 4 with slow;
              try (complete (remember (canonical_form_test_for c can2) as cft; destruct cft; eauto 3 with slow)).

            {
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              autorewrite with slow.
              remember (canonical_form_test_for c can2) as cft; destruct cft; eauto 3 with slow.
            }

            introv nrut' eqdoms diff'.
            unflsubst; simpl; csunf; simpl.
            allrw @sub_filter_nil_r.
            eexists; dands; eauto.
            unflsubst.
            remember (canonical_form_test_for c can2) as cft; destruct cft; auto.
          }

        * SSCase "NCan".
          unflsubst in comp; allsimpl.
          autorewrite with slow in *.
          allrw disjoint_app_r; repnd.

          rw @compute_step_ncan_ncan in comp.

          remember (compute_step
                      lib
                      (oterm (NCan ncan2)
                             (map (fun t : BTerm => lsubst_bterm_aux t sub)
                                  bts))) as c; symmetry in Heqc; destruct c; ginv;[].

          pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as h.
          repeat (autodimp h hyp); clear ind; eauto 3 with slow.

          pose proof (h n sub) as k; clear h.
          unflsubst in k; allsimpl.
          autorewrite with slow in *.
          allrw disjoint_app_r.
          applydup @nt_wf_oterm_fst in wf.

          repeat (autodimp k hyp);[|].
          { eapply nr_ut_sub_change_term;[|idtac|eauto];
            allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
          exrepnd.
          exists (oterm (NCan ncan) (nobnd w :: bs)).
          unflsubst; simpl.
          autorewrite with slow in *.
          allrw disjoint_app_r.
          allrw subvars_app_l.
          repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
          repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
          repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
          allrw @osubset_oapp_left_iff; autorewrite with slow.
          dands; autorewrite with slow in *; eauto 3 with slow.

          { prove_alpha_eq4; introv k; destruct n0; cpx.
            apply alphaeqbt_nilv2.
            unflsubst in k1. }

          {
            simpl; tcsp.
          }

          {
            unfold get_utokens_lib; simpl.
            repeat (apply implies_subset_app); eauto 3 with slow.
            eapply subset_trans;[apply get_utokens_subset_get_utokens_lib|].
            eapply subset_trans;[eauto|].
            unfold get_utokens_lib; simpl; autorewrite with slow; eauto 3 with slow.
          }

          { introv nrut' eqdoms diff'.
            pose proof (k0 sub') as h.
            repeat (autodimp h hyp).
            { eapply nr_ut_sub_change_term;[|idtac|eauto];
              allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
            { allsimpl; allrw disjoint_app_r; sp. }
            exrepnd.
            unflsubst; simpl.
            rw @compute_step_ncan_ncan.
            allrw @sub_filter_nil_r.
            unflsubst in h1; allsimpl; rw h1.
            eexists; dands; eauto.
            unflsubst; unflsubst in h0; simpl; allrw @sub_filter_nil_r.
            prove_alpha_eq4; introv k; destruct n0; cpx.
            apply alphaeqbt_nilv2; auto.
          }

        * SSCase "Exc".
          unflsubst in comp; csunf comp; allsimpl.

          autorewrite with slow in *.
          allrw disjoint_app_r; repnd.

          apply compute_step_catch_success in comp; repnd; repndors; exrepnd; subst.

          { repeat (destruct bs; allsimpl; ginv).
            repeat (destruct bts; allsimpl; ginv).
            destruct b0 as [l1 u1].
            destruct b1 as [l2 u2].
            destruct b2 as [l3 u3].
            destruct b3 as [l4 u4].
            destruct l1; allsimpl; ginv; fold_terms; cpx; allsimpl.
            autorewrite with slow in *.

            exists (mk_atom_eq u1 u3 (subst u2 v u4) (mk_exception u3 u4)).
            repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
            unfold subst.

            allsimpl; autorewrite with slow in *.
            allrw disjoint_app_r; repnd.
            allrw subvars_app_l.
            repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
            repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
            repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
            allrw @osubset_oapp_left_iff; autorewrite with slow.
            allrw subset_app.

            dands; eauto 4 with slow; fold_terms;
              try (complete (simple; auto));
              try (complete (simpl; auto; eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib];
                             simpl; autorewrite with slow; eauto 4 with slow)).

            + eapply alpha_eq_trans;
              [|apply alpha_eq_sym; apply alpha_eq_mk_atom_eq_lsubst].
              apply implies_alpha_eq_mk_atom_eq; auto.

              * pose proof (combine_sub_nest u2 [(v,u4)] sub) as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u2 (sub_filter sub [v]) [(v, lsubst u4 sub)]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub v0) as sf; destruct sf; simpl; tcsp.

              * eapply alpha_eq_trans;
                [|apply alpha_eq_sym; apply alpha_eq_mk_exception_lsubst].
                apply implies_alphaeq_exception; auto.

            + eapply disjoint_eqset_r;[apply eqset_sym; apply get_utokens_lsubst|].
              allrw disjoint_app_r; dands; eauto 3 with slow;[].
              eapply subset_disjoint_r;[|apply get_utokens_sub_sub_keep_first].
              unfold get_utokens_sub at 2; simpl; autorewrite with slow; eauto 3 with slow.

            + simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
              allrw subvars_app_l; dands; eauto 4 with slow.
              eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
              allsimpl; boolvar; allsimpl; allrw app_nil_r;
              allrw subvars_app_l; dands; eauto with slow.

            + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
              eapply subset_trans;[|apply get_utokens_subset_get_utokens_lib].
              simpl; autorewrite with slow.
              apply subset_app; dands; eauto 3 with slow.
              unfold get_utokens_sub; simpl; boolvar; simpl;
              autorewrite with slow; eauto 3 with slow.

            + introv nrut' eqdoms diff'.
              unflsubst; simpl.
              csunf; simpl.
              allrw @sub_filter_nil_r.
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
              eexists; dands; eauto.

              eapply alpha_eq_trans;
                [|apply alpha_eq_sym; apply alpha_eq_mk_atom_eq_lsubst].
              apply implies_alpha_eq_mk_atom_eq; auto.

              * pose proof (combine_sub_nest u2 [(v,u4)] sub') as h.
                eapply alpha_eq_trans;[|apply alpha_eq_sym; apply h]; clear h.
                pose proof (combine_sub_nest u2 (sub_filter sub' [v]) [(v, lsubst u4 sub')]) as h.
                eapply alpha_eq_trans;[apply h|]; clear h.
                simpl; rw @lsubst_sub_shallow_cl_sub; eauto 3 with slow.
                apply alpha_eq_lsubst_if_ext_eq; auto.
                unfold ext_alpha_eq_subs; simpl; introv i.
                rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
                boolvar; simpl; boolvar; simpl; tcsp.
                remember (sub_find sub' v0) as sf; destruct sf; simpl; tcsp.

              * eapply alpha_eq_trans;
                [|apply alpha_eq_sym; apply alpha_eq_mk_exception_lsubst].
                apply implies_alphaeq_exception; auto.
          }

          { exists (oterm Exc bts); unflsubst; simpl.
            allrw @oappl_app_as_oapp; autorewrite with slow in *.
            dands; eauto 3 with slow.

            {
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              eauto 3 with slow.
            }

            introv nrut' eqdoms diff'.
            unflsubst; simpl.
            csunf; simpl.
            rw @compute_step_catch_if_diff; auto.
            allrw @sub_filter_nil_r.
            eexists; dands; eauto.
            unflsubst.
          }

        * SSCase "Abs".
          unflsubst in comp; allsimpl.

          autorewrite with slow in *.
          allrw disjoint_app_r; repnd.

          rw @compute_step_ncan_abs in comp.

          remember (compute_step_lib
                      lib abs2
                      (map (fun t : BTerm => lsubst_bterm_aux t sub)
                           bts)) as c; symmetry in Heqc; destruct c; ginv.
          pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as h.
          repeat (autodimp h hyp); clear ind; eauto 3 with slow.

          pose proof (h n sub) as k; clear h.
          unflsubst in k; allsimpl.
          autorewrite with slow in *.
          allrw disjoint_app_r.
          applydup @nt_wf_oterm_fst in wf.

          repeat (autodimp k hyp);[|].
          { eapply nr_ut_sub_change_term;[|idtac|eauto];
            allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
          exrepnd.
          exists (oterm (NCan ncan) (nobnd w :: bs)).
          unflsubst; simpl.
          autorewrite with slow in *.
          allrw disjoint_app_r.
          allrw subvars_app_l.
          repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
          repeat (allrw @oeqset_oappl_cons; autorewrite with slow in *).
          repeat (allrw @oappl_app_as_oapp; autorewrite with slow in *).
          allrw @osubset_oapp_left_iff; autorewrite with slow.
          dands; autorewrite with slow in *; eauto 3 with slow.

          { prove_alpha_eq4; introv k; destruct n0; cpx.
            apply alphaeqbt_nilv2.
            unflsubst in k1. }

          {
            simpl in *; tcsp.
          }

          {
            unfold get_utokens_lib; simpl.
            repeat (apply implies_subset_app); eauto 3 with slow.
            eapply subset_trans;[apply get_utokens_subset_get_utokens_lib|].
            eapply subset_trans;[eauto|].
            unfold get_utokens_lib; simpl; autorewrite with slow; eauto 3 with slow.
          }

          { introv nrut' eqdoms diff'.
            pose proof (k0 sub') as h.
            repeat (autodimp h hyp).
            { eapply nr_ut_sub_change_term;[|idtac|eauto];
              allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
            { allsimpl; allrw disjoint_app_r; sp. }
            exrepnd.
            unflsubst; simpl.
            rw @compute_step_ncan_abs.
            allrw @sub_filter_nil_r.
            unflsubst in h1; csunf h1; allsimpl; rw h1.
            eexists; dands; eauto.
            unflsubst; unflsubst in h0; simpl.
            prove_alpha_eq4; introv k; destruct n0; cpx.
            allrw @sub_filter_nil_r.
            apply alphaeqbt_nilv2; auto.
          }
      }

      { (* Fresh case *)
        unflsubst in comp; csunf comp; allsimpl.
        autorewrite with slow in *.
        apply compute_step_fresh_success in comp; exrepnd; subst; allsimpl.
        repeat (destruct bs; allsimpl; ginv); autorewrite with slow in *.
        allrw @nt_wf_fresh.

        repndors; exrepnd; subst.

        - apply lsubst_aux_eq_vterm_implies in comp0; repndors; exrepnd; subst; allsimpl.
          { apply sub_find_some in comp0.
            apply in_cl_sub in comp0; eauto with slow.
            allunfold @closed; allsimpl; sp. }

          exists (@mk_fresh o n (mk_var n)); unflsubst; simpl.
          autorewrite with slow in *.
          dands; eauto 3 with slow.

          introv ntuf' eqdoms diff'.
          unflsubst; csunf.
          simpl; rw @sub_find_sub_filter_eq; rw memvar_singleton; boolvar; tcsp.
          exists (@mk_fresh o n (mk_var n)); dands; auto.
          rw @cl_lsubst_trivial; simpl; eauto 3 with slow.
          autorewrite with slow in *; simpl; auto.

        - apply isvalue_like_lsubst_aux_implies in comp0;
          repndors; exrepnd; subst; allsimpl; fold_terms.

          + exists (pushdown_fresh n t).
            rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
            autorewrite with slow in *.
            rw @free_vars_pushdown_fresh.
            dands; eauto 3 with slow.

            * apply alpha_eq_sym.
              apply cl_lsubst_pushdown_fresh; eauto 3 with slow.

            * introv nrut' eqdoms' disj'.
              unflsubst; simpl.
              rw @compute_step_fresh_if_isvalue_like2; eauto 3 with slow.
              eexists; dands; eauto.
              rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
              apply alpha_eq_sym.
              apply cl_lsubst_pushdown_fresh; eauto with slow.

          + allrw.
            rw @sub_find_sub_filter_eq in comp1; rw memvar_singleton in comp1.
            boolvar; ginv.
            applydup @sub_find_some in comp1 as sf.
            apply (in_nr_ut_sub lib _ _ _ (mk_fresh n (mk_var v))) in sf; auto.
            exrepnd; subst.
            allsimpl; fold_terms.
            exists (@mk_var o v).
            unflsubst; simpl; fold_terms.
            allrw.
            dands; eauto 3 with slow.

            { rw subvars_prop; simpl; introv i; repndors; tcsp; subst.
              rw in_remove_nvars; simpl; sp. }

            { introv nrut' eqdoms' disj'.
              unflsubst; simpl.
              rw @sub_find_sub_filter_eq; rw memvar_singleton.
              boolvar; tcsp.
              pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' v (mk_fresh n (mk_var v))) as h.
              repeat (autodimp h hyp).
              rw comp1 in h; exrepnd.
              rw h0.
              csunf; simpl; fold_terms.
              eexists; dands; eauto.
              unflsubst; simpl; allrw; auto.
            }

        - apply (isnoncan_like_lsubst_aux_nr_ut_implies lib _ _ (oterm (NCan NFresh) [bterm [n] t])) in comp1;
          [|apply nr_ut_sub_sub_filter_disj; auto; simpl;
            rw app_nil_r; rw disjoint_singleton_l; rw in_remove_nvar;
            complete sp].
          repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
          repeat (rw <- @cl_lsubst_lsubst_aux in comp2; eauto 3 with slow).
          remember (get_fresh_atom lib (lsubst t (sub_filter sub [n]))) as a'.
          unfold subst in comp2.

          pose proof (cl_lsubst_app t (sub_filter sub [n]) [(n,mk_utoken a')]) as h.
          repeat (autodimp h hyp); eauto 3 with slow; rw <- h in comp2; clear h.

          pose proof (ind t t [n]) as h.
          repeat (autodimp h hyp); eauto 3 with slow.

          pose proof (get_fresh_atom_prop_and_lib lib (lsubst t (sub_filter sub [n]))) as fap.
          rw <- Heqa' in fap.

          pose proof (h x (sub_filter sub [n] ++ [(n, mk_utoken a')])) as k; clear h.
          repeat (autodimp k hyp); eauto 3 with slow.

          { apply implies_nr_ut_sub_app; eauto 3 with slow.
            - apply (nr_ut_sub_sub_filter_change_term_disj lib _ _ (mk_fresh n t)); allsimpl; tcsp; allrw app_nil_r; auto.
              { apply disjoint_singleton_l; rw in_remove_nvars; simpl; sp. }
              { rw subvars_prop; introv i; rw in_app_iff; rw in_remove_nvars; simpl.
                destruct (deq_nvar x0 n); tcsp.
                left; sp. }
          }

          { rw @get_utokens_sub_app; rw @get_utokens_sub_cons; rw @get_utokens_sub_nil; rw app_nil_r; simpl.
            fold_terms.
            autorewrite with slow in *.
            rw disjoint_app_l; rw disjoint_singleton_l; dands; eauto 3 with slow.
            - apply (subset_disjoint _ _ (get_utokens_sub sub)); eauto 3 with slow.
              apply get_utokens_sub_filter_subset.
            - intro i; destruct fap.
              apply get_utokens_lib_lsubst; auto.
              rw in_app_iff; sp.
          }

          exrepnd.
          exists (mk_fresh n w); dands; allsimpl;
            fold_terms; autorewrite with slow in *;
              eauto 3 with slow.

          + pose proof (implies_alpha_eq_mk_fresh_subst_utokens
                          n a' x
                          (lsubst w (sub_filter sub [n] ++ [(n, mk_utoken a')]))
                          k1) as h.
            eapply alpha_eq_trans;[exact h|clear h].
            allrw @get_utokens_sub_app; allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil.
            allrw app_nil_r; allsimpl.
            allrw disjoint_app_l; allrw disjoint_singleton_l; repnd.

            pose proof (cl_lsubst_app w (sub_filter sub [n]) [(n,mk_utoken a')]) as h.
            repeat (autodimp h hyp); eauto 3 with slow.
            rw h; clear h; allrw @fold_subst.
            eapply alpha_eq_trans;
              [apply implies_alpha_eq_mk_fresh; apply simple_alphaeq_subst_utokens_subst|];
              [|repeat unflsubst];[].

            intro h.
            allrw @get_utokens_lsubst.
            allrw @get_utokens_lib_lsubst.
            allrw in_app_iff.
            allrw not_over_or; repnd.
            repndors; tcsp;[].

            destruct fap.
            allrw @in_get_utokens_sub; exrepnd.
            exists v t0; dands; auto;[].
            allrw @in_sub_keep_first; repnd; dands; auto.
            rw subvars_prop in k3; apply k3 in h0; auto.

          + apply subars_remove_nvars_lr; auto.

          + introv nrut' eqdoms diff'.
            unflsubst; simpl.
            rw @compute_step_fresh_if_isnoncan_like; eauto with slow.
            remember (get_fresh_atom lib (lsubst_aux t (sub_filter sub' [n]))) as a''.
            unfold subst; repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
            rw <- @cl_lsubst_app; eauto with slow.

            pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t (sub_filter sub' [n]))) as fap'.
            rw <- Heqa'' in fap'; repnd.
            repeat (rw <- @cl_lsubst_lsubst_aux in fap'; eauto 3 with slow).

            pose proof (k0 (sub_filter sub' [n] ++ [(n, mk_utoken a'')])) as h.
            repeat (autodimp h hyp).

            { apply implies_nr_ut_sub_app; eauto 3 with slow.
              - apply (nr_ut_sub_sub_filter_change_term_disj lib _ _ (mk_fresh n t)); allsimpl; tcsp; allrw app_nil_r; auto.
                { apply disjoint_singleton_l; rw in_remove_nvars; simpl; sp. }
                { rw subvars_prop; introv i; rw in_app_iff; rw in_remove_nvars; simpl.
                  destruct (deq_nvar x0 n); tcsp.
                  left; sp. }
            }

            { allrw @dom_sub_app; simpl; allrw <- @dom_sub_sub_filter; allrw; auto. }

            { rw @get_utokens_sub_app; rw @get_utokens_sub_cons; rw @get_utokens_sub_nil; rw app_nil_r; simpl.
              rw disjoint_app_l; rw disjoint_singleton_l; dands.
              - apply (subset_disjoint _ _ (get_utokens_sub sub')); eauto with slow.
                apply get_utokens_sub_filter_subset.
              - intro i; destruct fap'.
                apply get_utokens_lib_lsubst; eauto 3 with slow.
                rw in_app_iff; tcsp.
            }

            exrepnd.
            rw h1; simpl.
            eexists; dands; eauto.

            pose proof (implies_alpha_eq_mk_fresh_subst_utokens
                          n a'' s
                          (lsubst w (sub_filter sub' [n] ++ [(n, mk_utoken a'')]))
                          h0) as h.
            eapply alpha_eq_trans;[exact h|clear h].

            pose proof (cl_lsubst_app w (sub_filter sub' [n]) [(n,mk_utoken a'')]) as h.
            repeat (autodimp h hyp); eauto 3 with slow.
            rw h; clear h; allrw @fold_subst.
            eapply alpha_eq_trans;[apply implies_alpha_eq_mk_fresh; apply simple_alphaeq_subst_utokens_subst|].

            { intro h; destruct fap'.
              allrw @get_utokens_lsubst.
              allrw @get_utokens_lib_lsubst.
              allrw in_app_iff; allrw not_over_or; repnd.
              repndors; tcsp.

              {
                apply (get_utokens_subset_get_utokens_lib lib) in h.
                apply k4 in h.
                unfold get_utokens_lib in h; rw in_app_iff in h; repndors; tcsp.
              }

              allrw @in_get_utokens_sub; exrepnd.
              right.
              exists v t0; dands; auto.
              allrw @in_sub_keep_first; repnd; dands; auto.
              rw subvars_prop in k3; apply k3 in h2; auto. }

            repeat unflsubst.
      }

    + SCase "Exc".
      unflsubst in comp; csunf comp; allsimpl; ginv.
      exists (oterm Exc bs); unflsubst; simpl; dands; eauto with slow.

      { introv nrut' eqdoms diff'.
        unflsubst; csunf; simpl; eexists; dands; eauto. }

    + SCase "Abs".
      unflsubst in comp; csunf comp; allsimpl; ginv.
      apply compute_step_lib_success in comp; exrepnd; subst.

      pose proof (found_entry_change_bs abs oa2 vars rhs lib (lsubst_bterms_aux bs sub) correct bs comp0) as fe.
      autodimp fe hyp.
      { unfold lsubst_bterms_aux; rw map_map; unfold compose.
        apply eq_maps; introv i; destruct x as [l t]; simpl.
        unfold num_bvars; simpl; auto. }
      apply found_entry_implies_matching_entry in fe; auto.
      unfold matching_entry in fe; repnd.

      exists (mk_instance vars bs rhs); unflsubst; simpl; dands;
      autorewrite with slow; eauto 4 with slow.

      { pose proof (alpha_eq_lsubst_aux_mk_instance rhs vars bs sub) as h.
        repeat (autodimp h hyp); eauto with slow. }

      { eapply subset_disjoint_r;[|apply get_utokens_lib_mk_instance]; auto.
        eapply subset_disjoint_r;[exact disj|].
        unfold get_utokens_lib; simpl.
        autorewrite with slow.
        unfold correct_abs in correct; repnd.
        dup correct as c.
        apply no_utokens_implies_get_utokens_so_nil in c.
        rw c; simpl.
        apply subset_app_lr; auto. }

      { eapply subvars_trans;[apply subvars_free_vars_mk_instance|]; auto.
        unfold correct_abs in correct; sp. }

      { eapply subset_trans;[apply get_utokens_lib_mk_instance|]; auto.
        unfold correct_abs in correct; repnd.
        dup correct as c.
        apply no_utokens_implies_get_utokens_so_nil in c.
        rw c; simpl.
        unfold get_utokens_lib; simpl.
        apply subset_app_lr; auto. }

      { introv nrut' eqdoms diff'.
        unflsubst; csunf; simpl.

        pose proof (found_entry_change_bs abs oa2 vars rhs lib (lsubst_bterms_aux bs sub) correct (lsubst_bterms_aux bs sub') comp0) as fe'.
        autodimp fe' hyp.
        { unfold lsubst_bterms_aux; allrw map_map; unfold compose.
          apply eq_maps; introv i; destruct x as [l t]; simpl.
          unfold num_bvars; simpl; auto. }
        apply found_entry_implies_compute_step_lib_success in fe'.
        unfold lsubst_bterms_aux in fe'; rw fe'.
        eexists; dands; eauto.
        unflsubst.
        fold (lsubst_bterms_aux bs sub').
        apply alpha_eq_lsubst_aux_mk_instance; eauto with slow.
      }
Qed.

Lemma compute_step_preserves_utokens {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> compute_step lib t = csuccess u
    -> subset (get_utokens_lib lib u) (get_utokens_lib lib t).
Proof.
  introv wf comp.
  pose proof (compute_step_subst_utoken lib t u []) as h.
  autorewrite with slow in *.
  repeat (autodimp h hyp); exrepnd; autorewrite with slow in *.
  eapply alphaeq_preserves_get_utokens_lib in h1; rw h1; eauto.
Qed.

(*
Lemma compute_step_preserves_utokens {o} :
  forall lib (t u : @NTerm o),
    compute_step lib t = csuccess u
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv comp.
  apply compute_step_preserves in comp; repnd.
  introv i.
  apply comp in i; sp.
Qed.
*)
