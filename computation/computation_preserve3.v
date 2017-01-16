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
  forall (t : @NTerm o) sub n u,
    nr_ut_sub u sub
    -> lsubst_aux t sub = mk_nat n
    -> t = mk_nat n.
Proof.
  introv nrut e.
  destruct t as [v|f|op bs]; allsimpl; ginv.
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
  - inversion h as [|?|? ? imp]; subst; allsimpl.
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
  - inversion h as [|?|? ? imp]; subst; allsimpl.
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
  destruct t as [v|f|op bs]; allsimpl; tcsp.
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
  - inversion h as [|?|? ? imp]; subst; allsimpl.
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
  - inversion h as [|?|? ? imp]; subst; allsimpl.
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
  forall (t u : @NTerm o) sub sub',
    nr_ut_sub u sub
    -> nr_ut_sub u sub'
    -> dom_sub sub = dom_sub sub'
    -> iscan (lsubst_aux t sub)
    -> iscan (lsubst_aux t sub').
Proof.
  introv nrut1 nrut2 eqdoms isc.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; allsimpl; tcsp.
  pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v u) as h.
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

Definition get_utokens_step_seq_bterms_seq {o}
           (bs : list (@BTerm o)) :=
  match bs with
    | bterm [] (sterm f) :: bterm [] (oterm (Can (Nint z)) _) :: _ =>
      if Z_le_gt_dec 0 z
      then get_utokens_step_seq (f (Z.to_nat z))
      else []
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_bterms_seq {o} :
  forall (bs : list (@BTerm o)),
    match bs with
      | bterm [] (sterm f) :: bterm [] (oterm (Can (Nint z)) _) :: _ =>
        if Z_le_gt_dec 0 z
        then get_utokens_step_seq (f (Z.to_nat z))
        else []
      | _ => []
    end = get_utokens_step_seq_bterms_seq bs.
Proof. sp. Qed.

Definition get_utokens_step_seq_ncan_seq {o}
           (ncan : NonCanonicalOp)
           (bs   : list (@BTerm o)) :=
  match ncan with
    | NApply  => get_utokens_step_seq_bterms_seq bs
    | NEApply => get_utokens_step_seq_bterms_seq bs
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_ncan_seq {o} :
  forall ncan (bs : list (@BTerm o)),
    match ncan with
      | NApply  => get_utokens_step_seq_bterms_seq bs
      | NEApply => get_utokens_step_seq_bterms_seq bs
      | _ => []
    end = get_utokens_step_seq_ncan_seq ncan bs.
Proof. sp. Qed.

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

Definition get_utokens_step_seq_op_seq {o}
           (op : @Opid o)
           (bs : list (@BTerm o)) :=
  match op with
    | NCan NApply  => get_utokens_step_seq_bterms_seq bs
    | NCan NEApply => get_utokens_step_seq_bterms_seq bs
    | _ => []
  end.

Lemma fold_get_utokens_step_seq_op_seq {o} :
  forall op (bs : list (@BTerm o)),
    match op with
      | NCan NApply  => get_utokens_step_seq_bterms_seq bs
      | NCan NEApply => get_utokens_step_seq_bterms_seq bs
      | _ => []
    end = get_utokens_step_seq_op_seq op bs.
Proof. sp. Qed.

Lemma subset_get_utokens_step_seq_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    subset (get_utokens_step_seq t) (get_utokens_step_seq (lsubst_aux t sub)).
Proof.
  nterm_ind1 t as [v|f ind|op bs ind] Case; introv; simpl; auto.
  Case "oterm".
  allrw @fold_get_utokens_step_seq_bterms_seq.
  allrw @fold_get_utokens_step_seq_op_seq.
  allrw subset_app; dands; eauto 3 with slow.
  - apply subset_app_l.
    apply subset_app_r.
    allrw flat_map_map; unfold compose.
    apply subset_flat_map2; introv i.
    destruct x as [l t]; allsimpl.
    eapply ind; eauto.
  - apply subset_app_l.
    apply subset_app_l.
    dopid op as [can|ncan|exc|abs] SCase; simpl; auto;[].
    SCase "NCan".
    allrw @fold_get_utokens_step_seq_ncan_seq.
    destruct ncan; simpl; auto;[|].
    + destruct bs; simpl; auto;[].
      destruct b as [l t]; simpl;[].
      destruct l; simpl; auto;[].
      destruct t as [v|f|op bs1]; simpl; autorewrite with slow in *; auto;[].
      destruct bs; simpl; auto;[].
      destruct b as [l t].
      destruct l; simpl; auto;[].
      destruct t as [v|f1|op bs1]; simpl; autorewrite with slow in *; auto.
    + destruct bs; simpl; auto;[].
      destruct b as [l t]; simpl;[].
      destruct l; simpl; auto;[].
      destruct t as [v|f|op bs1]; simpl; autorewrite with slow in *; auto;[].
      destruct bs; simpl; auto;[].
      destruct b as [l t].
      destruct l; simpl; auto;[].
      destruct t as [v|f1|op bs1]; simpl; autorewrite with slow in *; auto.
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
  forall sub (t : @NTerm o),
    nr_ut_sub t sub
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
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv isus; simpl; autorewrite with slow; auto.

  - Case "vterm".
    rw @sub_keep_singleton.
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
    simpl; autorewrite with slow; auto.
    rw @get_utokens_sub_cons; autorewrite with slow; eauto 3 with slow.
    apply sub_find_some in Heqsf.
    apply isus in Heqsf.
    apply is_utok_implies in Heqsf; exrepnd; subst; simpl; auto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase; simpl; autorewrite with slow;
    try (complete (apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto));[|].

    + rw <- app_assoc.
      apply eqset_app_if; auto.
      apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto.

    + destruct ncan; allsimpl; autorewrite with slow in *;
      try (complete (apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto));
      allrw @fold_get_utokens_step_seq_bterms_seq;[|].

      * eapply eqset_trans;[|apply eqset_sym;apply eqset_app_move2].
        apply eqset_app_if.

        { apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto. }

        { destruct bs as [|b bs]; simpl; auto.
          destruct b as [l t]; simpl.
          destruct l as [|v l]; allsimpl; auto; autorewrite with slow.
          destruct t as [v|f|op bs1]; allsimpl; auto;[|].

          - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
            allsimpl; autorewrite with slow; auto;[].
            applydup @sub_find_some in Heqsf as j.
            apply isus in j.
            apply is_utok_implies in j; exrepnd; subst; allsimpl; autorewrite with slow in *; auto.

          - destruct bs as [|b bs]; allsimpl; auto;[].
            destruct b as [l t]; allsimpl.
            destruct l as [|v l]; allsimpl; autorewrite with slow; auto;[].
            destruct t as [v|f1|op bs1]; allsimpl; auto;[].
            remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
            allsimpl; autorewrite with slow; auto;[].
            applydup @sub_find_some in Heqsf as j.
            apply isus in j.
            apply is_utok_implies in j; exrepnd; subst; allsimpl; autorewrite with slow in *; auto.
        }

      * eapply eqset_trans;[|apply eqset_sym;apply eqset_app_move2].
        apply eqset_app_if.

        { apply eqset_flat_map_get_utokens_step_seq_b_is_utok_sub; auto. }

        { destruct bs as [|b bs]; simpl; auto.
          destruct b as [l t]; simpl.
          destruct l as [|v l]; allsimpl; auto; autorewrite with slow.
          destruct t as [v|f|op bs1]; allsimpl; auto;[|].

          - remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
            allsimpl; autorewrite with slow; auto;[].
            applydup @sub_find_some in Heqsf as j.
            apply isus in j.
            apply is_utok_implies in j; exrepnd; subst; allsimpl; autorewrite with slow in *; auto.

          - destruct bs as [|b bs]; allsimpl; auto;[].
            destruct b as [l t]; allsimpl.
            destruct l as [|v l]; allsimpl; autorewrite with slow; auto;[].
            destruct t as [v|f1|op bs1]; allsimpl; auto;[].
            remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf;
            allsimpl; autorewrite with slow; auto;[].
            applydup @sub_find_some in Heqsf as j.
            apply isus in j.
            apply is_utok_implies in j; exrepnd; subst; allsimpl; autorewrite with slow in *; auto.
        }
Qed.

Lemma get_utokens_so_subset_get_cutokens_so {o} :
  forall (t : @SOTerm o),
    subseto (get_utokens_so t) (get_cutokens_so t).
Proof.
  soterm_ind1s t as [v ts ind | |op bs ind] Case; simpl;
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

Lemma compute_step_subst_utoken {o} :
  forall lib (t u : @NTerm o) sub,
    nt_wf t
    -> compute_step lib (lsubst t sub) = csuccess u
    -> nr_ut_sub t sub
    -> disjoint (get_utokens_sub sub) (get_utokens t)
    -> {w : NTerm
        & alpha_eq u (lsubst w sub)
        # disjoint (get_utokens_sub sub) (get_utokens w)
        # subvars (free_vars w) (free_vars t)
        # subset (get_utokens w) (get_utokens t)
        # (forall sub',
             nr_ut_sub t sub'
             -> dom_sub sub = dom_sub sub'
             -> disjoint (get_utokens_sub sub') (get_utokens t)
             -> {s : NTerm
                 & compute_step lib (lsubst t sub') = csuccess s
                 # alpha_eq s (lsubst w sub')})}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf comp nrut disj; tcsp.

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
      pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v (vterm v)) as h.
      repeat (autodimp h hyp).
      rw Heqsf in h; exrepnd.
      unflsubst; simpl; rw h0.
      csunf; simpl.
      eexists; dands; eauto.
      unflsubst; simpl; rw h0; auto.

    + csunf comp; allsimpl; ginv.

  - Case "sterm".
    allsimpl.
    unflsubst in comp; allsimpl.
    csunf comp; allsimpl; ginv.
    exists (sterm f); simpl.
    unflsubst; simpl.
    dands; eauto 3 with slow.
    introv nrut' eqdoms' disj'.
    unflsubst; simpl.
    csunf; simpl.
    eexists; dands; eauto.

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
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));
        [ | | ].

        { unflsubst in comp; allsimpl.
          allrw @sub_filter_nil_r.
          remember (sub_find sub x) as sf; symmetry in Heqsf; destruct sf;
          [|csunf comp; allsimpl; ginv].

          applydup @sub_find_some in Heqsf.
          eapply in_nr_ut_sub in Heqsf0; eauto; exrepnd; subst.
          apply compute_step_ncan_vterm_success in comp.
          repndors; exrepnd; subst.

          - exists (@mk_axiom o); allsimpl.
            rw @cl_lsubst_trivial; simpl; dands; eauto with slow.
            introv nrut' eqdoms disj'.
            exists (@mk_axiom o); allsimpl.
            rw (@cl_lsubst_trivial o mk_axiom); simpl; dands; eauto 3 with slow.
            unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' x (oterm (NCan NParallel) (bterm [] (vterm x) :: bs))) as h; repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; rw h0.
            csunf; simpl.
            unfold compute_step_parallel; auto.

          - destruct bs; allsimpl; cpx; GC.
            exists (@mk_apply o (mk_var x) (mk_fix (mk_var x))).
            unflsubst; simpl; allrw @sub_filter_nil_r; allrw; dands; eauto 3 with slow.
            introv nrut' eqdoms disj'.
            repeat unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' x (oterm (NCan NFix) [bterm [] (vterm x)])) as h; repeat (autodimp h hyp).
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

            + eapply disjoint_eqset_r;[apply eqset_sym; apply get_utokens_lsubst|].
              eapply subset_disjoint_r; eauto 3 with slow.
              apply app_subset; dands; eauto 3 with slow.
              eapply subset_trans;[apply get_utokens_sub_sub_keep_first|].
              unfold get_utokens_sub; simpl; auto.

            + eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint]; simpl.
              unfold dom_sub; simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

            + autorewrite with slow.
              eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
              unfold get_cutokens_sub; simpl; boolvar; simpl;
              autorewrite with slow; eauto 3 with slow.

            + introv nrut' eqdoms disj'.
              unflsubst; simpl; allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            sub sub' x
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

            introv nrut' eqdoms disj'.
            unflsubst; simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub
                          sub sub' x
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

                introv nrut' eqdoms disj'.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              sub sub' x
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
                              sub v x a (oterm (NCan (NCompOp CompOpEq))
                                               [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3]))
                  as k; repeat (autodimp k hyp); subst; simpl; tcsp.
                allrw; csunf; simpl; boolvar; allsimpl; tcsp; GC.
                dcwf h; allsimpl.
                unfold compute_step_comp; simpl; boolvar; tcsp; GC.
                eexists; dands; eauto.
                unflsubst; auto.

              * exists u3.
                unflsubst; dands; eauto 4 with slow.

                introv nrut' eqdoms disj'.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              sub sub' x
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
                                sub v x a' a
                                (oterm (NCan (NCompOp CompOpEq))
                                       [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3])) as h; repeat (autodimp h hyp).
                  pose proof (sub_find_some_eq_doms_nr_ut_sub
                                sub sub' v
                                (oterm (NCan (NCompOp CompOpEq))
                                       [nobnd (mk_var x), nobnd (mk_var v), nobnd u2, nobnd u3])) as k; repeat (autodimp k hyp).
                  assert (sub_find sub v = Some (mk_utoken a')) as e by auto; allrw e; GC; exrepnd; rw k0.
                  pose proof (nr_ut_sub_some_diff2
                                sub' v x a1 a0
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
              { eapply nr_ut_sub_change_term;[|idtac|eauto];
                allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
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
                allrw disjoint_app_r; dands; eauto 3 with slow.

              * introv nrut' eqdoms disj'.
                unflsubst; simpl; allrw @sub_filter_nil_r.
                pose proof (sub_find_some_eq_doms_nr_ut_sub
                              sub sub' x
                              (oterm (NCan (NCompOp CompOpEq))
                                     (nobnd (mk_var x)
                                            :: nobnd t2
                                            :: nobnd t3
                                            :: nobnd t4
                                            :: []))) as h; repeat (autodimp h hyp).
                rw Heqsf in h; exrepnd; allrw.
                pose proof (k0 sub') as h; clear k0; repeat (autodimp h hyp).
                { eapply nr_ut_sub_change_term;[|idtac|eauto];
                  allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
                { allsimpl; introv i j; apply disj' in i.
                  allrw in_app_iff; sp. }
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

              introv nrut' eqdoms disj'.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            sub sub' x
                            (oterm (NCan (NCompOp CompOpEq))
                                   (nobnd (mk_var x) :: nobnd (oterm Exc l0) :: bs))) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.

              unflsubst; simpl; allrw @sub_filter_nil_r; allrw.
              csunf; simpl; boolvar; allsimpl; tcsp; GC.
              eexists; dands; eauto.
              unflsubst.

          - repeat (destruct bs; allsimpl; ginv).
            destruct b as [l1 u1].
            destruct b0 as [l2 u2]; allsimpl.
            destruct l1, l2; ginv; boolvar; tcsp; GC; fold_terms; ginv.
            repndors; repnd; subst; allrw @sub_filter_nil_r.

            + exists u1; unflsubst; dands; eauto 4 with slow.

              introv nrut' eqdoms disj'.
              unflsubst; simpl; boolvar.
              allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            sub sub' x
                            (oterm (NCan (NCanTest CanIsuatom))
                                   [nobnd (mk_var x), nobnd u1, nobnd u2])) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              csunf; simpl; eexists; dands; eauto.
              unflsubst.

            + exists u2; unflsubst; dands; eauto with slow.

              introv nrut' eqdoms disj'.
              unflsubst; simpl; boolvar.
              allrw @sub_filter_nil_r.
              pose proof (sub_find_some_eq_doms_nr_ut_sub
                            sub sub' x
                            (oterm (NCan (NCanTest x0))
                                   [nobnd (mk_var x), nobnd u1, nobnd u2])) as h; repeat (autodimp h hyp).
              rw Heqsf in h; exrepnd; allrw.
              csunf; simpl; eexists; dands; eauto.
              unflsubst.
              destruct x0; sp.
        }

        { unflsubst in comp; allsimpl.
          allrw @fold_get_utokens_step_seq_bterms.
          allrw @fold_get_utokens_step_seq_ncan.
          csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          - SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            repeat (destruct bs; allsimpl; ginv).
            allrw @fold_get_utokens_step_seq_bterm.
            destruct b as [l t]; allsimpl.
            allrw @fold_get_utokens_step_seq_arg1.
            allunfold @nobnd.
            destruct l; allsimpl; ginv.
            autorewrite with slow in *.

            exists (mk_eapply (mk_ntseq f) t).
            unflsubst; simpl; autorewrite with slow in *; fold_terms.
            allrw disjoint_app_r; repnd.
            dands; eauto 3 with slow.

            introv nrut' eqdoms' disj'.
            unflsubst; simpl; autorewrite with slow in *.
            csunf; simpl.
            eexists; dands; eauto.
            unflsubst; simpl; autorewrite with slow in *.
            eauto 3 with slow.

          - SSCase "NEApply".
            apply compute_step_eapply_success in comp; exrepnd; subst.
            allunfold @nobnd.
            destruct bs; allsimpl; ginv.
            allrw @fold_get_utokens_step_seq_bterm.
            destruct b as [vs t]; allsimpl.
            allrw @fold_get_utokens_step_seq_arg1.
            destruct vs; allsimpl; ginv.
            autorewrite with slow in *.
            allrw disjoint_app_r; repnd.

            repndors; exrepnd; subst; allsimpl.

            + apply compute_step_eapply2_success in comp1; repnd.
              destruct bs; allsimpl; ginv; autorewrite with slow in *.
              repndors; exrepnd; subst; ginv;[]; allsimpl.

              allrw @nt_wf_eapply_iff; exrepnd; ginv; allsimpl.
              allrw @nt_wf_sterm_iff.
              pose proof (wf2 n) as seq; repnd; clear wf2.

              exists (f0 n).
              unflsubst.
              eapply lsubst_aux_equal_mk_nat in comp4; eauto;[]; subst; allsimpl; GC.
              boolvar; try omega;[].
              allrw @Znat.Nat2Z.id.
              unfold oatoms.
              autorewrite with slow in *.
              rw @lsubst_aux_trivial_cl_term2; auto;[].
              try (rewrite seq).
              try (rewrite seq1).
              dands; eauto 3 with slow.

              * introv nrut' eqdoms' disj'.
                unflsubst; simpl.
                csunf; simpl.
                dcwf h;[].
                unfold compute_step_eapply2; simpl; boolvar; try omega;[]; GC.
                allrw @Znat.Nat2Z.id.
                eexists; dands; eauto.
                unflsubst.
                rw @lsubst_aux_trivial_cl_term2; auto.

            + eapply isexc_lsubst_aux_nr_ut_sub in comp0; eauto;[].
              allrw @nt_wf_eapply_iff; exrepnd; ginv; allsimpl.
              allrw @nt_wf_sterm_iff; autorewrite with slow in *.
              apply wf_isexc_implies in comp0; auto;[].
              exrepnd; subst; allsimpl; autorewrite with slow in *.
              exists (mk_exception a e); simpl; autorewrite with slow in *.
              unflsubst; simpl; autorewrite with slow in *.
              allrw disjoint_app_r.
              allrw subvars_app_l; repnd.
              allrw @oeqset_oappl_cons.
              dands; eauto 3 with slow;[].

              introv nrut' eqdoms' diff'.
              allrw disjoint_app_r; repnd.
              unflsubst; simpl; autorewrite with slow in *.
              csunf; simpl.
              dcwf h;[].
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow in *; eauto 3 with slow.

            + allrw @nt_wf_eapply_iff; exrepnd; ginv; allsimpl.
              allrw @nt_wf_sterm_iff; autorewrite with slow in *.
              pose proof (ind b b []) as h; clear ind; repeat (autodimp h hyp); eauto 3 with slow.
              pose proof (h x sub) as ih; clear h; repeat (autodimp ih hyp); eauto 3 with slow.
              { unflsubst; auto. }
              { eapply nr_ut_sub_change_term;[| |exact nrut]; simpl; autorewrite with slow; auto. }
              exrepnd;[].

              exists (mk_eapply (mk_ntseq f) w); simpl; autorewrite with slow.
              unflsubst; simpl; autorewrite with slow.
              unfold oatoms.
              allrw @oeqset_oappl_cons; autorewrite with slow.
              unflsubst in ih1.
              dands; repeat (apply osubset_oapp_left); eauto 3 with slow.
              { prove_alpha_eq3. }

              introv nrut' eqdoms' disj'.
              unflsubst; simpl; autorewrite with slow in *.
              eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto;[].
              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow;[].
              pose proof (ih0 sub') as h'; clear ih0.
              repeat (autodimp h' hyp); eauto 3 with slow.
              { eapply nr_ut_sub_change_term;[| |exact nrut']; simpl; autorewrite with slow; auto. }
              exrepnd.
              unflsubst in h'1.
              rw h'1.
              eexists; dands; eauto.
              unflsubst; simpl; autorewrite with slow.
              unflsubst in h'0.
              prove_alpha_eq3.

          - SSCase "NFix".
            autorewrite with slow in *.
            apply compute_step_fix_success in comp; repnd; subst.
            destruct bs; allsimpl; ginv.
            apply nt_wf_NFix in wf; exrepnd; subst; allunfold @nobnd; ginv.

            exists (mk_apply (mk_ntseq f) (mk_fix (mk_ntseq f))).
            unflsubst; simpl.
            autorewrite with slow.
            allrw @oeqset_oappl_cons; autorewrite with slow.
            dands; repeat (apply osubset_oapp_left); eauto 3 with slow.

            introv nrut' eqdoms' disj'.
            unflsubst; simpl.
            csunf; simpl.
            eexists; dands; eauto.

          - SSCase "NCbv".
            autorewrite with slow in *.
            apply nt_wf_NCbv in wf; exrepnd; allunfold @nobnd; ginv.
            unfold apply_bterm; simpl.
            repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

            exists (subst b v (mk_ntseq f)).
            allsimpl; autorewrite with slow in *.

            dands; eauto 3 with slow.

            + pose proof (combine_sub_nest b (sub_filter sub [v]) [(v, mk_ntseq f)]) as aeq1.
              rw @lsubst_sub_shallow_cl_sub in aeq1; eauto 3 with slow.
              pose proof (combine_sub_nest b [(v,mk_ntseq f)] sub) as aeq2.
              allrw @fold_subst.
              eapply alpha_eq_trans;[clear aeq2|apply alpha_eq_sym;exact aeq2].
              eapply alpha_eq_trans;[exact aeq1|clear aeq1].
              apply alpha_eq_lsubst_if_ext_eq; auto.
              unfold ext_alpha_eq_subs; simpl; introv i.
              rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
              boolvar; simpl; boolvar; simpl; tcsp; GC.
              remember (sub_find sub v0) as sf; destruct sf; simpl; tcsp.

            + eapply disjoint_eqset_r;[apply eqset_sym; apply get_utokens_subst|].
              boolvar; allrw disjoint_app_r; dands; eauto 3 with slow.

            + eapply subvars_eqvars;[|apply eqvars_sym;apply eqvars_free_vars_disjoint].
              allsimpl.
              apply subvars_app_l; dands; auto.
              boolvar; simpl; auto.

            + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_subst|].
              boolvar; simpl; autorewrite with slow; auto.

            + introv nrut' eqdoms' disj'.
              unflsubst; simpl.
              csunf; simpl.
              unfold apply_bterm; simpl.
              eexists; dands; eauto.
              repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).

              pose proof (combine_sub_nest b (sub_filter sub' [v]) [(v, mk_ntseq f)]) as aeq1.
              rw @lsubst_sub_shallow_cl_sub in aeq1; eauto 3 with slow;[].
              pose proof (combine_sub_nest b [(v,mk_ntseq f)] sub') as aeq2.
              allrw @fold_subst.
              eapply alpha_eq_trans;[clear aeq2|apply alpha_eq_sym;exact aeq2].
              eapply alpha_eq_trans;[exact aeq1|clear aeq1].
              apply alpha_eq_lsubst_if_ext_eq; auto.
              unfold ext_alpha_eq_subs; simpl; introv i.
              rw @sub_find_app; rw @sub_find_sub_filter_eq; allrw memvar_cons.
              boolvar; simpl; boolvar; simpl; tcsp; GC.
              remember (sub_find sub' v0) as sf; destruct sf; simpl; tcsp.

          - SSCase "NTryCatch".
            allsimpl; autorewrite with slow in *.
            allrw @nt_wf_NTryCatch; exrepnd; allunfold @nobnd; ginv.
            allsimpl; autorewrite with slow in *.
            exists (mk_atom_eq b b (mk_ntseq f) mk_bot).
            unflsubst; simpl; autorewrite with slow in *.
            allrw @sub_find_sub_filter_eq.
            allrw memvar_singleton; boolvar; tcsp;[]; fold_terms.
            allrw subvars_app_l.
            allrw disjoint_app_r; repnd.
            allrw @oeqset_oappl_cons.
            dands; repeat (apply osubset_oapp_left); dands; eauto 4 with slow.

            introv nrut' eqdoms' disj'.
            unflsubst; simpl; autorewrite with slow in *.
            csunf; simpl.
            unflsubst; simpl; autorewrite with slow in *.
            allrw @sub_find_sub_filter_eq.
            allrw memvar_singleton; boolvar; tcsp;[]; fold_terms.
            eexists; dands; eauto 3 with slow.

          - SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst.
            allrw @nt_wf_NCanTest; exrepnd; allunfold @nobnd; ginv; allsimpl.
            autorewrite with slow in *.
            allrw disjoint_app_r; repnd.

            exists t3.
            unflsubst.
            dands; eauto 3 with slow.

            introv nrut' eqdoms' disj'.
            allrw disjoint_app_r.
            unflsubst; simpl; autorewrite with slow in *.
            csunf; simpl.
            eexists; dands; eauto.
            unflsubst; auto.
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
                  eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                  simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r; eauto with slow.

                + allrw remove_nvars_nil_l; allrw app_nil_r.
                  eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                  simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

                + autorewrite with slow.
                  eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                  apply subset_app; dands; eauto 3 with slow.
                  unfold get_utokens_sub; simpl; boolvar; simpl;
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

              exists (mk_eapply (mk_nseq f) t).
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

                * eapply disjoint_eqset_r;[apply eqset_sym;apply get_utokens_subst|].
                  allrw disjoint_app_r; dands; eauto 3 with slow.
                  boolvar; eauto 3 with slow.

                * eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                  simpl; allrw subvars_app_l; dands; eauto 3 with slow.
                  boolvar; simpl; autorewrite with slow; eauto 3 with slow.

                * autorewrite with slow.
                  eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                  apply subset_app; dands; eauto 3 with slow.
                  unfold get_utokens_sub; simpl; boolvar; simpl;
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

              + allunfold @mk_nseq; destruct bts; allsimpl; ginv; allsimpl; fold_terms.
                eapply lsubst_aux_equal_mk_nat in comp4;[|eauto]; subst; allsimpl.
                exists (@mk_nat o (f n)); simpl.
                unflsubst; simpl; fold_terms.
                dands; eauto 3 with slow.
                introv nrut' eqdoms diff'.
                unflsubst; simpl; fold_terms.
                csunf; simpl; dcwf h; simpl; boolvar; try omega;[].
                rw Znat.Nat2Z.id.
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
                { eapply nr_ut_sub_change_term;[| |exact nrut']; simpl;
                  autorewrite with slow; eauto 3 with slow. }
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

            dands; eauto 3 with slow.

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
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r;
                allrw subset_app; dands; eauto with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                apply subset_app; dands; eauto 3 with slow.
                unfold get_utokens_sub; simpl; boolvar; simpl;
                autorewrite with slow; eauto 3 with slow.

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
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r;
                allrw subset_app; dands; eauto with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                apply subset_app; dands; eauto 3 with slow.
                unfold get_utokens_sub; simpl; boolvar; simpl;
                autorewrite with slow; eauto 3 with slow.

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
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r;
                allrw subset_app; dands; eauto with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                apply subset_app; dands; eauto 3 with slow.
                unfold get_utokens_sub; simpl; boolvar; simpl;
                autorewrite with slow; eauto 3 with slow.

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
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r;
                allrw subset_app; dands; eauto with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                apply subset_app; dands; eauto 3 with slow.
                unfold get_utokens_sub; simpl; boolvar; simpl;
                autorewrite with slow; eauto 3 with slow.

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
                eapply subset_eqset_l;[apply eqset_sym; apply get_utokens_lsubst|].
                simpl; boolvar; unfold get_utokens_sub; simpl; allrw app_nil_r;
                allrw subset_app; dands; eauto 3 with slow.

              + allrw remove_nvars_nil_l; allrw app_nil_r.
                eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
                simpl; boolvar; simpl; allrw app_nil_r; eauto with slow.

              + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lsubst|].
                apply subset_app; dands; eauto 3 with slow.
                unfold get_utokens_sub; simpl; boolvar; simpl;
                autorewrite with slow; eauto 3 with slow.

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

            - exists (@mk_uni o n).
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
              dands; eauto 3 with slow.

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
            introv nrut' eqdoms disj'.
            exists (@mk_axiom o); allsimpl.
            rw (@cl_lsubst_trivial o mk_axiom); simpl; dands; eauto 3 with slow.
            unflsubst.
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
                  dands; boolvar; subst; eauto 3 with slow; try unflsubst;allsimpl;[|].

                  { allrw disjoint_singleton_r.
                    apply sub_find_some in epk1.
                    rw @in_get_utokens_sub in disj0; destruct disj0.
                    eexists; eexists; dands; eauto; simpl; auto. }

                  { introv nrut' eqdoms diff'; unflsubst; simpl; fold_terms.
                    allrw @sub_filter_nil_r; allsimpl.

                    pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v) as h.
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
              { eapply nr_ut_sub_change_term;[|idtac|eauto];
                allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
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
              dands; autorewrite with slow; eauto 4 with slow.

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
              { eapply nr_ut_sub_change_term;[|idtac|eauto];
                allsimpl; allrw remove_nvars_nil_l; eauto with slow. }
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
            try (complete (remember (canonical_form_test_for c can2) as cft; destruct cft; eauto 3 with slow));
            [].

            introv nrut' eqdoms diff'.
            unflsubst; simpl; csunf; simpl.
            allrw @sub_filter_nil_r.
            eexists; dands; eauto.
            unflsubst.
            remember (canonical_form_test_for c can2) as cft; destruct cft; auto.
          }

        * SSCase "NCan".
          unflsubst in comp; allsimpl.

          allrw @fold_get_utokens_step_seq_bterms_seq.
          allrw @fold_get_utokens_step_seq_ncan_seq.
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
          allrw @fold_get_utokens_step_seq_bterms_seq.
          allrw @fold_get_utokens_step_seq_ncan_seq.
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

            dands; eauto 4 with slow; fold_terms.

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
            rw @get_utokens_pushdown_fresh.
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
            apply (in_nr_ut_sub _ _ _ (mk_fresh n (mk_var v))) in sf; auto.
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
              pose proof (sub_find_some_eq_doms_nr_ut_sub sub sub' v (mk_fresh n (mk_var v))) as h.
              repeat (autodimp h hyp).
              rw comp1 in h; exrepnd.
              rw h0.
              csunf; simpl; fold_terms.
              eexists; dands; eauto.
              unflsubst; simpl; allrw; auto.
            }

        - apply (isnoncan_like_lsubst_aux_nr_ut_implies _ _ (oterm (NCan NFresh) [bterm [n] t])) in comp1;
          [|apply nr_ut_sub_sub_filter_disj; auto; simpl;
            rw app_nil_r; rw disjoint_singleton_l; rw in_remove_nvar;
            complete sp].
          repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
          repeat (rw <- @cl_lsubst_lsubst_aux in comp2; eauto 3 with slow).
          remember (get_fresh_atom (lsubst t (sub_filter sub [n]))) as a'.
          unfold subst in comp2.

          pose proof (cl_lsubst_app t (sub_filter sub [n]) [(n,mk_utoken a')]) as h.
          repeat (autodimp h hyp); eauto 3 with slow; rw <- h in comp2; clear h.

          pose proof (ind t t [n]) as h.
          repeat (autodimp h hyp); eauto 3 with slow.

          pose proof (get_fresh_atom_prop (lsubst t (sub_filter sub [n]))) as fap.
          rw <- Heqa' in fap.

          pose proof (h x (sub_filter sub [n] ++ [(n, mk_utoken a')])) as k; clear h.
          repeat (autodimp k hyp); eauto 3 with slow.

          { apply implies_nr_ut_sub_app; eauto with slow.
            - apply (nr_ut_sub_sub_filter_change_term_disj _ _ (mk_fresh n t)); allsimpl; tcsp; allrw app_nil_r; auto.
              { apply disjoint_singleton_l; rw in_remove_nvars; simpl; sp. }
              { rw subvars_prop; introv i; rw in_app_iff; rw in_remove_nvars; simpl.
                destruct (deq_nvar x0 n); tcsp.
                left; sp. }
          }

          { rw @get_utokens_sub_app; rw @get_utokens_sub_cons; rw @get_utokens_sub_nil; rw app_nil_r; simpl.
            rw disjoint_app_l; rw disjoint_singleton_l; dands; eauto 3 with slow.
            - apply (subset_disjoint _ _ (get_utokens_sub sub)); eauto 3 with slow.
              apply get_utokens_sub_filter_subset.
            - intro i; destruct fap.
              unflsubst.
              apply get_utokens_lsubst_aux; auto.
              rw in_app_iff; sp.
          }

          exrepnd.
          exists (mk_fresh n w); dands; allsimpl;
          autorewrite with slow; eauto 3 with slow.

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
            allrw @get_utokens_lsubst; allrw in_app_iff; allrw not_over_or; repnd.
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
            remember (get_fresh_atom (lsubst_aux t (sub_filter sub' [n]))) as a''.
            unfold subst; repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
            rw <- @cl_lsubst_app; eauto with slow.

            pose proof (get_fresh_atom_prop (lsubst_aux t (sub_filter sub' [n]))) as fap'.
            rw <- Heqa'' in fap'; repnd.
            repeat (rw <- @cl_lsubst_lsubst_aux in fap'; eauto 3 with slow).

            pose proof (k0 (sub_filter sub' [n] ++ [(n, mk_utoken a'')])) as h.
            repeat (autodimp h hyp).

            { apply implies_nr_ut_sub_app; eauto with slow.
              - apply (nr_ut_sub_sub_filter_change_term_disj _ _ (mk_fresh n t)); allsimpl; tcsp; allrw app_nil_r; auto.
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
                unflsubst.
                apply get_utokens_lsubst_aux; eauto 3 with slow.
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
              allrw @get_utokens_lsubst; allrw in_app_iff; allrw not_over_or; repnd.
              repndors; tcsp.
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
      autorewrite with slow; eauto with slow.

      { pose proof (alpha_eq_lsubst_aux_mk_instance rhs vars bs sub) as h.
        repeat (autodimp h hyp); eauto with slow. }

      { eapply subset_disjoint_r;[|apply get_utokens_mk_instance]; auto.
        eapply subset_disjoint_r;[exact disj|].
        autorewrite with slow.
        unfold correct_abs in correct; repnd.
        dup correct as c.
        apply no_utokens_implies_get_utokens_so_nil in c.
        rw c; simpl.
        apply subset_flat_map2; introv i; destruct x; simpl; eauto 3 with slow. }

      { eapply subvars_trans;[apply subvars_free_vars_mk_instance|]; auto.
        unfold correct_abs in correct; sp. }

      { eapply subset_trans;[apply get_utokens_mk_instance|]; auto.
        unfold correct_abs in correct; repnd.
        dup correct as c.
        apply no_utokens_implies_get_utokens_so_nil in c.
        rw c; simpl.
        apply subset_flat_map2; introv i; destruct x; simpl; eauto 3 with slow. }

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
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv wf comp.
  pose proof (compute_step_subst_utoken lib t u []) as h.
  autorewrite with slow in *.
  repeat (autodimp h hyp); exrepnd; autorewrite with slow in *.
  apply alphaeq_preserves_utokens in h1; rw h1; auto.
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


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
