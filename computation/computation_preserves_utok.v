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


Require Export computation4.
Require Export computation10.


Fixpoint sub2utok {o} (t : @NTerm o) (s : @Sub o) : utok_sub :=
  match s with
  | [] => []
  | (v,oterm (Can (NUTok a)) []) :: l =>
    if in_dec deq_nvar v (free_vars t) then
      (a,mk_var v) :: sub2utok t l
    else sub2utok t l
  | _ :: l => sub2utok t l
  end.

Lemma sub_find_some_implies_utok_sub_find_sub2utok_some {o} :
  forall lib (sub : @Sub o) v a t,
    nr_ut_sub lib t sub
    -> LIn v (free_vars t)
    -> sub_find sub v = Some (mk_utoken a)
    -> utok_sub_find (sub2utok (vterm v) sub) a = Some (mk_var v).
Proof.
  induction sub; introv nrut i h; simpl in *; ginv;[].
  repnd; boolvar; ginv; simpl in *; boolvar; tcsp;[].
  destruct a; auto.

  - eapply IHsub; eauto; inversion nrut.

  - eapply IHsub; eauto; inversion nrut.

  - destruct o0; auto; try (complete (eapply IHsub; eauto; inversion nrut));[].
    destruct c; auto; try (complete (eapply IHsub; eauto; inversion nrut));[].
    destruct l; simpl; auto; try (complete (eapply IHsub; eauto; inversion nrut));[].

    inversion nrut; subst; clear nrut.
    eapply IHsub;[eauto| |]; auto.
    rw <- @fold_subst.
    rw @isprogram_lsubst2; simpl; tcsp;[|introv xx; repndors; subst; ginv; tcsp; eauto 2 with slow].
    rw in_remove_nvars; simpl; tcsp.
Qed.

Definition ren_utok_op {o} (op : @Opid o) (a b : get_patom_set o) : Opid :=
  match get_utok op with
  | Some a' =>

    if get_patom_deq o a a'
    then Can (NUTok b)
    else op

  | _ => op
  end.

(* replaces [a] by [b] *)
Fixpoint ren_utok {o} (t : @NTerm o) (a b : get_patom_set o) : NTerm :=
  match t with
  | vterm v => t
  | sterm f => t
  | oterm op bs => oterm (ren_utok_op op a b) (map (fun bt => ren_utok_b bt a b) bs)
  end
with ren_utok_b {o} (bt : @BTerm o) a b : BTerm :=
       match bt with
       | bterm vs t => bterm vs (ren_utok t a b)
       end.

Lemma not_in_get_utokens_lib_implies_not_in_get_utokens_o {o} :
  forall lib a (op : @Opid o) bs,
    !LIn a (get_utokens_lib lib (oterm op bs))
    -> !LIn a (get_utokens_o op).
Proof.
  introv ni i; destruct ni; apply in_app_iff; simpl; allrw in_app_iff; tcsp.
Qed.
Hint Resolve not_in_get_utokens_lib_implies_not_in_get_utokens_o : slow.

Lemma not_in_get_utokens_implies_not_in_get_utokens_o {o} :
  forall a (op : @Opid o) bs,
    !LIn a (get_utokens (oterm op bs))
    -> !LIn a (get_utokens_o op).
Proof.
  introv ni i; destruct ni; apply in_app_iff; simpl; allrw in_app_iff; tcsp.
Qed.
Hint Resolve not_in_get_utokens_implies_not_in_get_utokens_o : slow.

Lemma not_in_get_utokens_o_implies_ren_utok_op_same {o} :
  forall a b (op : @Opid o),
    !LIn a (get_utokens_o op)
    -> ren_utok_op op a b = op.
Proof.
  introv ni.
  destruct op; simpl in *; tcsp.
  destruct c; simpl in *; tcsp.
  allrw not_over_or; repnd; GC.
  unfold ren_utok_op; simpl; boolvar; tcsp.
Qed.

Hint Rewrite @lsubst_aux_nil : slow.

Lemma not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib {o} :
  forall a lib op (bs : list (@BTerm o)) l t,
    !LIn a (get_utokens_lib lib (oterm op bs))
    -> LIn (bterm l t) bs
    -> !LIn a (get_utokens_lib lib t).
Proof.
  introv ni ibs i; destruct ni; unfold get_utokens_lib in *.
  allsimpl; allrw in_app_iff; repndors; tcsp.
  left; right.
  apply lin_flat_map; eexists; dands; eauto.
Qed.
Hint Resolve not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib : slow.

Lemma not_in_get_utokens_oterm_implies_not_in_get_utokens {o} :
  forall a op (bs : list (@BTerm o)) l t,
    !LIn a (get_utokens (oterm op bs))
    -> LIn (bterm l t) bs
    -> !LIn a (get_utokens t).
Proof.
  introv ni ibs i; destruct ni; unfold get_utokens_lib in *.
  allsimpl; allrw in_app_iff; repndors; tcsp.
  right.
  apply lin_flat_map; eexists; dands; eauto.
Qed.
Hint Resolve not_in_get_utokens_oterm_implies_not_in_get_utokens : slow.

Lemma not_in_get_utokens_lib_implies_ren_utok_same {o} :
  forall a b lib (t : @NTerm o),
    !LIn a (get_utokens_lib lib t)
    -> ren_utok t a b = t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv ni; tcsp.
  Case "oterm".
  simpl.
  rewrite not_in_get_utokens_o_implies_ren_utok_op_same; eauto 2 with slow.
  f_equal.
  apply eq_map_l; introv i.
  destruct x; simpl; f_equal.
  eapply ind;[eauto| |]; eauto 2 with slow.
Qed.

Lemma not_in_get_utokens_implies_ren_utok_same {o} :
  forall a b (t : @NTerm o),
    !LIn a (get_utokens t)
    -> ren_utok t a b = t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv ni; tcsp.
  Case "oterm".
  simpl.
  rewrite not_in_get_utokens_o_implies_ren_utok_op_same; eauto 2 with slow.
  f_equal.
  apply eq_map_l; introv i.
  destruct x; simpl; f_equal.
  eapply ind;[eauto| |]; eauto 2 with slow.
Qed.

Lemma ren_utok_utoken_renames {o} :
  forall (a b : get_patom_set o),
    ren_utok (mk_utoken a) a b = mk_utoken b.
Proof.
  introv; simpl; unfold ren_utok_op; simpl; boolvar; tcsp.
Qed.
Hint Rewrite @ren_utok_utoken_renames : slow.

Lemma ren_utok_lsubst_aux {o} :
  forall a b v (t : @NTerm o),
    !LIn a (get_utokens t)
    -> ren_utok (lsubst_aux t [(v, mk_utoken a)]) a b
       = lsubst_aux t [(v, mk_utoken b)].
Proof.
  nterm_ind1s t as [x|f ind|op bs ind] Case; introv ni; allsimpl; tcsp.

  - Case "vterm".
    boolvar; tcsp; GC; autorewrite with slow; auto.

  - Case "oterm".
    rewrite not_in_get_utokens_o_implies_ren_utok_op_same; eauto 2 with slow.
    f_equal.
    rewrite map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    boolvar; autorewrite with slow.

    + rewrite not_in_get_utokens_implies_ren_utok_same; eauto 2 with slow.

    + erewrite ind;[|eauto| |]; eauto 2 with slow.
Qed.

Lemma not_in_get_utokens_lib_implies_not_in_get_utokens {o} :
  forall (lib : library) (t : @NTerm o) (a : get_patom_set o),
    !LIn a (get_utokens_lib lib t)
    -> !LIn a (get_utokens t).
Proof.
  introv ni i; destruct ni; eauto 2 with slow.
Qed.
Hint Resolve not_in_get_utokens_lib_implies_not_in_get_utokens : slow.

Lemma eq_free_vars_lsubst_aux_utoken {o} :
  forall (t : @NTerm o) v a b,
    free_vars (lsubst_aux t [(v, mk_utoken a)])
    = free_vars (lsubst_aux t [(v, mk_utoken b)]).
Proof.
  introv.
  repeat (rewrite cl_lsubst_aux_trivial2; eauto 2 with slow).
Qed.

Lemma eq_maybe_new_var_lsubst_aux_utoken {o} :
  forall n l (t : @NTerm o) v a b,
    maybe_new_var n l (lsubst_aux t [(v, mk_utoken a)])
    = maybe_new_var n l (lsubst_aux t [(v, mk_utoken b)]).
Proof.
  introv; unfold maybe_new_var; boolvar; auto.
  unfold newvar.
  f_equal; apply eq_free_vars_lsubst_aux_utoken.
Qed.
Hint Resolve eq_maybe_new_var_lsubst_aux_utoken : slow.

Lemma not_in_get_utokens_subst_aux_lib_implies_not_in_get_utokens_lib {o} :
  forall lib a (t : @NTerm o) v u,
    !LIn a (get_utokens_lib lib (subst_aux t v u))
    -> !LIn a (get_utokens_lib lib t).
Proof.
  introv ni i; destruct ni.
  apply get_utokens_lib_lsubst_aux; apply in_app_iff; tcsp.
Qed.
Hint Resolve not_in_get_utokens_subst_aux_lib_implies_not_in_get_utokens_lib : slow.

Lemma implies_get_utokens_lib_subst_aux {o} :
  forall a a' v lib (t : @NTerm o),
    !LIn a (get_utokens_lib lib t)
    -> !LIn a' (get_utokens_lib lib (subst_aux t v (mk_utoken a)))
    -> !LIn a (get_utokens_lib lib (subst_aux t v (mk_utoken a'))).
Proof.
  introv ni1 ni2 i.
  apply get_utokens_lib_lsubst_aux in i; allrw in_app_iff.
  allrw not_over_or; repnd.
  simpl in *.
  repndors; tcsp;[].
  boolvar; simpl in *; repndors; subst; tcsp.
  destruct ni0.
  apply get_utokens_lsubst_aux; simpl; boolvar; tcsp; GC.
  unfold get_utokens_sub; simpl; apply in_app_iff; simpl; tcsp.
Qed.
Hint Resolve implies_get_utokens_lib_subst_aux : slow.

Lemma implies_get_utokens_lib_subst_aux2 {o} :
  forall a a' v lib (t : @NTerm o),
    !LIn a (get_utokens_lib lib t)
    -> a <> a'
    -> !LIn a (get_utokens_lib lib (subst_aux t v (mk_utoken a'))).
Proof.
  introv ni d i.
  apply get_utokens_lib_lsubst_aux in i; allrw in_app_iff.
  allrw not_over_or; repnd.
  simpl in *.
  repndors; tcsp;[].
  boolvar; simpl in *; repndors; subst; tcsp.
Qed.
Hint Resolve implies_get_utokens_lib_subst_aux2 : slow.

Lemma not_in_get_utokens_subst_aux_implies_or {o} :
  forall a a' lib v (t : @NTerm o),
    !LIn a' (get_utokens_lib lib (subst_aux t v (mk_utoken a)))
    -> LIn v (free_vars t)
    -> a <> a'.
Proof.
  introv ni i x; subst.
  destruct ni; apply get_utokens_lib_lsubst_aux; simpl; boolvar; tcsp.
  unfold get_utokens_sub; simpl; apply in_app_iff; simpl; tcsp.
Qed.

Definition no_repeats_utok_sub {o} (sub : @Sub o) :=
  forall (v1 v2 : NVar) (t1 t2 : NTerm),
    sub_find sub v1 = Some t1
    -> sub_find sub v2 = Some t2
    -> v1 <> v2
    -> {a1 : get_patom_set o
        & {a2 : get_patom_set o
        & t1 = mk_utoken a1
        # t2 = mk_utoken a2
        # a1 <> a2}}.

Definition utok_ren {o} := list (get_patom_set o * get_patom_set o).

Fixpoint subs2utok_ren {o} (sub1 sub2 : @Sub o) : utok_ren :=
  match sub1, sub2 with
  | (v,oterm (Can (NUTok a)) []) :: l, (w,oterm (Can (NUTok b)) []) :: k =>
    (a,b) :: subs2utok_ren l k
  | _, _ => []
  end.

Fixpoint utok_ren_find {o} (ren : @utok_ren o) (a : get_patom_set o) : option (get_patom_set o) :=
  match ren with
  | nil => None
  | (x,y) :: l =>
    if get_patom_deq o a x
    then Some y
    else utok_ren_find l a
  end.

Definition ren_utoks_op {o} (ren : utok_ren) (op : @Opid o) : Opid :=
  match get_utok op with
  | Some a =>

    match utok_ren_find ren a with
    | Some b => Can (NUTok b)
    | None => op
    end

  | _ => op
  end.

Fixpoint ren_utoks {o} (ren : @utok_ren o) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => t
  | sterm f => t
  | oterm op bs => oterm (ren_utoks_op ren op) (map (fun bt => ren_utoks_b ren bt) bs)
  end
with ren_utoks_b {o} ren (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (ren_utoks ren t)
       end.

Lemma sub_find_some_is_utok_sub_implies {o} :
  forall (sub : @Sub o) v t,
    sub_find sub v = Some t
    -> is_utok_sub sub
    -> is_utok t.
Proof.
  introv sf iu.
  apply sub_find_some in sf.
  apply iu in sf; auto.
Qed.

Lemma sub_find_some_implies_in_dom_sub {o} :
  forall (sub : @Sub o) v t,
    sub_find sub v = Some t
    -> LIn v (dom_sub sub).
Proof.
  introv sf.
  apply sub_find_some in sf.
  apply in_dom_sub in sf; auto.
Qed.
Hint Resolve sub_find_some_implies_in_dom_sub : slow.

Lemma no_repeats_utok_sub_cons {o} :
  forall v t (sub : @Sub o),
    !LIn v  (dom_sub sub)
    -> no_repeats_utok_sub ((v, t) :: sub)
       <=> no_repeats_utok_sub sub
           # forall w u,
               v <> w
               -> sub_find sub w = Some u
               -> {a1 : get_patom_set o
                   & {a2 : get_patom_set o
                   & t = mk_utoken a1
                   # u = mk_utoken a2
                   # a1 <> a2}}.
Proof.
  introv ni; unfold no_repeats_utok_sub; split; intro h; simpl in *.

  - dands.

    + introv h1 h2 d.
      apply (h v1 v2); boolvar; tcsp.

      * apply sub_find_some_implies_in_dom_sub in h1; tcsp.

      * apply sub_find_some_implies_in_dom_sub in h2; tcsp.

    + introv d sf.
      apply (h v w); boolvar; tcsp.

  - repnd; introv h1 h2 d.
    boolvar; ginv; tcsp.

    + pose proof (h v1 t1) as q; repeat (autodimp q hyp).
      exrepnd; subst; eexists; eexists; dands; eauto.

    + pose proof (h v2 t2) as q; repeat (autodimp q hyp).

    + apply (h0 v1 v2 t1 t2); auto.
Qed.

Lemma no_repeats_utok_sub_snoc {o} :
  forall v t (sub : @Sub o),
    !LIn v (dom_sub sub)
    -> no_repeats_utok_sub (snoc sub (v,t))
       <=> no_repeats_utok_sub sub
           # forall w u,
               v <> w
               -> sub_find sub w = Some u
               -> {a1 : get_patom_set o
                   & {a2 : get_patom_set o
                   & t = mk_utoken a1
                   # u = mk_utoken a2
                   # a1 <> a2}}.
Proof.
  introv ni; unfold no_repeats_utok_sub; split; intro h; simpl in *.

  - dands.

    + introv h1 h2 d.
      apply (h v1 v2); boolvar; tcsp;
        allrw @sub_find_snoc; allrw; auto.

    + introv d sf.
      apply (h v w); boolvar; tcsp; allrw @sub_find_snoc; allrw; auto.
      rewrite sub_find_none_if; auto.
      boolvar; auto.

  - repnd; introv h1 h2 d.
    allrw @sub_find_snoc.

    remember (sub_find sub v1) as sf1; symmetry in Heqsf1; destruct sf1;
      remember (sub_find sub v2) as sf2; symmetry in Heqsf2; destruct sf2;
        ginv; tcsp; boolvar; tcsp.

    + apply (h0 v1 v2 t1 t2); auto.

    + pose proof (h v1 t1) as q; repeat (autodimp q hyp).
      exrepnd; subst; eexists; eexists; dands; eauto; ginv.

    + pose proof (h v2 t2) as q; repeat (autodimp q hyp).
      exrepnd; subst; eexists; eexists; dands; eauto; ginv.
Qed.

Lemma implies_utok_ren_find_subst2utok_ren_some {o} :
  forall (sub1 sub2 : @Sub o) v a b,
    no_repeats (dom_sub sub1)
    -> dom_sub sub1 = dom_sub sub2
    -> sub_find sub1 v = Some (mk_utoken a)
    -> sub_find sub2 v = Some (mk_utoken b)
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> no_repeats_utok_sub sub1
    -> no_repeats_utok_sub sub2
    -> utok_ren_find (subs2utok_ren sub1 sub2) a = Some b.
Proof.
  induction sub1; introv norep eqdoms sf1 sf2 isu1 isu2 norep1 norep2; repnd; simpl in *; ginv;[].
  boolvar; ginv; simpl in *;[|].

  - destruct sub2; simpl in *; repnd; ginv;[].
    boolvar; simpl in *; ginv; tcsp; simpl in *;[|].

    + inversion eqdoms as [eqdoms1]; clear eqdoms.
      boolvar; tcsp.

    + inversion eqdoms as [eqdoms1]; clear eqdoms; subst.
      allrw @is_utok_sub_cons; repnd.
      apply is_utok_implies in isu0; exrepnd; subst; simpl in *.
      boolvar; tcsp.

  - destruct sub2; simpl in *; repnd; ginv;[].
    boolvar; simpl in *; ginv; tcsp; simpl in *;[|].

    + inversion eqdoms as [eqdoms1]; clear eqdoms.
      boolvar; tcsp.

    + inversion eqdoms as [eqdoms1]; clear eqdoms; subst.
      allrw @is_utok_sub_cons; repnd.
      apply is_utok_implies in isu0; exrepnd; subst; simpl in *.
      apply is_utok_implies in isu3; exrepnd; subst; simpl in *.
      boolvar; subst; tcsp.

      * pose proof (norep1 p0 v (mk_utoken a2) (mk_utoken a2)) as q.
        simpl in q; boolvar; tcsp;[].
        repeat (autodimp q hyp).
        exrepnd; ginv; tcsp.

      * allrw no_repeats_cons; repnd.
        apply no_repeats_utok_sub_cons in norep1; auto; repnd;[].
        apply no_repeats_utok_sub_cons in norep2; auto; repnd; allrw <-; auto;[].
        eapply IHsub1; eauto.
Qed.

Lemma eq_dom_sub_sub_find_some_implies {o} :
  forall (sub1 sub2 : @Sub o) v t,
    dom_sub sub1 = dom_sub sub2
    -> sub_find sub1 v = Some t
    -> {u : NTerm & sub_find sub2 v = Some u}.
Proof.
  introv eqdoms sf.
  apply in_dom_sub_exists.
  allrw <-; eauto 2 with slow.
Qed.

Definition dom_utok_ren {o} (ren : @utok_ren o) : list (get_patom_set o) :=
  map fst ren.

Lemma not_in_dom_utok_ren_implies_utok_ren_find_none {o} :
  forall (ren : @utok_ren o) a,
    !LIn a (dom_utok_ren ren)
    -> utok_ren_find ren a = None.
Proof.
  induction ren; simpl in *; introv h; tcsp.
  repnd; simpl in *; allrw not_over_or; repnd.
  boolvar; tcsp.
Qed.

Lemma not_in_get_utokens_o_implies_ren_utoks_op_same {o} :
  forall (op : @Opid o) ren,
    disjoint (get_utokens_o op) (dom_utok_ren ren)
    -> ren_utoks_op ren op = op.
Proof.
  introv disj.
  unfold ren_utoks_op.
  remember (get_utok op) as guo.
  destruct guo; symmetry in Heqguo; auto.
  apply get_utok_some in Heqguo; subst; simpl in *.
  allrw disjoint_singleton_l.
  rewrite not_in_dom_utok_ren_implies_utok_ren_find_none; auto.
Qed.

Lemma dom_utok_ren_subs2utok_ren {o} :
  forall (sub1 sub2 : @Sub o),
    length sub1 = length sub2
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> dom_utok_ren (subs2utok_ren sub1 sub2) = get_utokens_sub sub1.
Proof.
  induction sub1; simpl in *; introv eqlen isu1 isu2; ginv.
  repnd.
  destruct sub2; repnd; simpl in *; ginv.
  allrw @is_utok_sub_cons; repnd.
  apply is_utok_implies in isu0.
  apply is_utok_implies in isu3.
  exrepnd; subst; simpl in *.
  rewrite get_utokens_sub_cons; simpl.
  f_equal; apply IHsub1; auto.
Qed.

Lemma eq_dom_implies_eq_length {o} :
  forall (sub1 sub2 : @Sub o),
    dom_sub sub1 = dom_sub sub2
    -> length sub1 = length sub2.
Proof.
  induction sub1; simpl in *; destruct sub2; introv h; simpl in *; ginv; tcsp.
  repnd; simpl in *; ginv.
  inversion h; subst.
  f_equal; apply IHsub1; auto.
Qed.
Hint Resolve eq_dom_implies_eq_length : slow.

Lemma disjoint_get_utokens_lib_oterm_left_implies_disjoint_get_utokens_o_left {o} :
  forall lib op bs (sub : @Sub o),
    disjoint (get_utokens_lib lib (oterm op bs)) (get_utokens_sub sub)
    -> disjoint (get_utokens_o op) (get_utokens_sub sub).
Proof.
  introv d i j.
  apply disjoint_sym in d; apply d in j.
  rw in_app_iff in j; simpl in j; allrw in_app_iff; allrw not_over_or; repnd; tcsp.
Qed.
Hint Resolve disjoint_get_utokens_lib_oterm_left_implies_disjoint_get_utokens_o_left : slow.

Lemma disjoin_flat_map_get_utokens_b_left_implies_disjoint_get_utokens_left {o} :
  forall bs (ren : @utok_ren o) l t,
    disjoint (flat_map get_utokens_b bs) (dom_utok_ren ren)
    -> LIn (bterm l t) bs
    -> disjoint (get_utokens t) (dom_utok_ren ren).
Proof.
  introv d i a b.
  apply disjoint_sym in d; apply d in b.
  destruct b; apply lin_flat_map.
  eexists; dands; eauto.
Qed.
Hint Resolve disjoin_flat_map_get_utokens_b_left_implies_disjoint_get_utokens_left : slow.

Lemma not_in_get_utokens_implies_ren_utoks_same {o} :
  forall ren (t : @NTerm o),
    disjoint (get_utokens t) (dom_utok_ren ren)
    -> ren_utoks ren t = t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv d; tcsp.
  Case "oterm".
  simpl in *.
  allrw disjoint_app_l; repnd.
  rewrite not_in_get_utokens_o_implies_ren_utoks_op_same; eauto 2 with slow.
  f_equal.
  apply eq_map_l; introv i.
  destruct x; simpl; f_equal.
  eapply ind;[eauto| |]; eauto 2 with slow.
Qed.

Lemma disjoint_get_utokens_lib_oterm_left_implies_disjoint_get_utokens_lib_left {o} :
  forall lib op bs (sub : @Sub o) vs t,
    disjoint (get_utokens_lib lib (oterm op bs)) (get_utokens_sub sub)
    -> LIn (bterm vs t) bs
    -> disjoint (get_utokens_lib lib t) (get_utokens_sub sub).
Proof.
  introv d i a b.
  apply disjoint_sym in d; apply d in b.
  allrw in_app_iff; allrw not_over_or; repnd.
  repndors; tcsp.
  destruct b0; apply lin_flat_map.
  eexists; dands; eauto.
Qed.
Hint Resolve disjoint_get_utokens_lib_oterm_left_implies_disjoint_get_utokens_lib_left : slow.

Lemma ren_utoks_lsubst_aux_sub_filter {o} :
  forall lib (t : @NTerm o) l sub1 sub2,
    no_repeats (dom_sub sub1)
    -> dom_sub sub1 = dom_sub sub2
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> no_repeats_utok_sub sub1
    -> no_repeats_utok_sub sub2
    -> disjoint (get_utokens_lib lib t) (get_utokens_sub sub1)
    -> disjoint (get_utokens_lib lib t) (get_utokens_sub sub2)
    -> ren_utoks (subs2utok_ren sub1 sub2) (lsubst_aux t (sub_filter sub1 l))
       = lsubst_aux t (sub_filter sub2 l).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
    introv norep eqdoms iu1 iu2 norep1 norep2 disj1 disj2; tcsp; simpl in *.

  - Case "vterm".
    clear disj1 disj2.
    allrw @sub_find_sub_filter_eq.

    boolvar; simpl; auto.

    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1;
      remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2;
        simpl in *; tcsp.

    + applydup @sub_find_some_is_utok_sub_implies in Heqsf1 as isu1; auto.
      applydup @sub_find_some_is_utok_sub_implies in Heqsf2 as isu2; auto.
      apply is_utok_implies in isu1.
      apply is_utok_implies in isu2.
      exrepnd; subst; simpl in *.
      unfold ren_utoks_op; simpl.
      erewrite implies_utok_ren_find_subst2utok_ren_some; eauto; auto.

    + eapply eq_dom_sub_sub_find_some_implies in Heqsf1 as w;[|eauto].
      exrepnd.
      rewrite w0 in Heqsf2; ginv.

    + eapply eq_dom_sub_sub_find_some_implies in Heqsf2 as w;[|symmetry; eauto].
      exrepnd.
      rewrite w0 in Heqsf1; ginv.

  - Case "oterm".
    rewrite not_in_get_utokens_o_implies_ren_utoks_op_same;
      [|rewrite dom_utok_ren_subs2utok_ren; eauto 2 with slow].
    f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [vs t]; simpl in *.
    f_equal.
    allrw <- @sub_filter_app_r.
    eapply ind; eauto 3 with slow.
Qed.

Lemma implies_is_utok_sub_filter {o} :
  forall (sub : @Sub o) l,
    is_utok_sub sub
    -> is_utok_sub (sub_filter sub l).
Proof.
  introv isu i.
  apply in_sub_filter in i; repnd.
  apply isu in i0; auto.
Qed.
Hint Resolve implies_is_utok_sub_filter : slow.

Lemma lsubst_aux_eq_vterm_is_utok_sub_implies {o} :
  forall (t : @NTerm o) (sub : Substitution) (v : NVar),
    is_utok_sub sub
    -> lsubst_aux t sub = vterm v
    -> t = vterm v.
Proof.
  introv isu e.
  apply @lsubst_aux_eq_vterm_implies in e.
  repndors; exrepnd; subst; auto.
  apply sub_find_some_is_utok_sub_implies in e1; auto.
  apply is_utok_implies in e1; exrepnd; ginv.
Qed.

Lemma is_utok_sub_implies_cl_sub {o} :
  forall (sub : @Sub o), is_utok_sub sub -> cl_sub sub.
Proof.
  introv isu i.
  apply isu in i.
  apply is_utok_implies in i; exrepnd; subst; eauto 2 with slow.
Qed.
Hint Resolve is_utok_sub_implies_cl_sub : slow.

Lemma eq_maybe_new_var_lsubst_aux_sub_filter_is_utok_subs {o} :
  forall n (t : @NTerm o) sub1 sub2 l k,
    dom_sub sub1 = dom_sub sub2
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> maybe_new_var n l (lsubst_aux t (sub_filter sub1 k))
       = maybe_new_var n l (lsubst_aux t (sub_filter sub2 k)).
Proof.
  introv eqdoms isu1 isu2; unfold maybe_new_var; boolvar; auto.
  unfold newvar.
  f_equal.
  repeat (rewrite cl_lsubst_aux_trivial2; eauto 3 with slow).
  allrw <- @dom_sub_sub_filter.
  allrw; auto.
Qed.
Hint Resolve eq_maybe_new_var_lsubst_aux_sub_filter_is_utok_subs : slow.

Lemma isnoncan_like_lsubst_aux_is_utok_sub_implies {o} :
  forall (t : @NTerm o) sub,
    is_utok_sub sub
    -> isnoncan_like (lsubst_aux t sub)
    -> isnoncan_like t.
Proof.
  introv isu isn.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; tcsp.
  apply sub_find_some in Heqsf.
  apply isu in Heqsf.
  apply is_utok_implies in Heqsf; exrepnd; subst.
  unfold isnoncan_like in isn; simpl in *; tcsp.
Qed.

Lemma dom_sub_sub_keep {o} :
  forall (sub : @Sub o) l,
    dom_sub (sub_keep sub l) = lKeep deq_nvar l (dom_sub sub).
Proof.
  induction sub; introv; simpl; auto; repnd.
  boolvar; simpl in *; tcsp.
  f_equal; tcsp.
Qed.

Lemma in_lkeep_iff :
  forall {A} (deq : Deq A) keep l a,
    LIn a (lKeep deq keep l) <=> LIn a keep # LIn a l.
Proof.
  induction l; introv; simpl; split; intro h; repnd; tcsp; boolvar;
    simpl in *; repndors; subst; tcsp;
      try (complete (apply IHl in h; repnd; tcsp)).

  - right; apply IHl; tcsp.

  - apply IHl; tcsp.
Qed.

Lemma implies_no_repeats_lKeep :
  forall {A} (deq : Deq A) keep l,
    no_repeats l
    -> no_repeats (lKeep deq keep l).
Proof.
  induction l; introv norep; simpl in *; auto.
  boolvar; allrw no_repeats_cons; repnd; tcsp.
  dands; tcsp.
  rw @in_lkeep_iff; intro w; repnd; tcsp.
Qed.
Hint Resolve implies_no_repeats_lKeep : list.

Hint Rewrite remove_nvars_nil_r : list.

Lemma implies_no_repeats :
  forall l1 l2,
    no_repeats l2
    -> no_repeats (remove_nvars l1 l2).
Proof.
  induction l2; introv norep; simpl in *; autorewrite with slow list in *; auto.
  rewrite remove_nvars_cons_r; boolvar; allrw no_repeats_cons; repnd; tcsp.
  dands; tcsp.
  intro i; apply in_remove_nvars in i; tcsp.
Qed.
Hint Resolve implies_no_repeats : list.

Hint Resolve disjoint_remove_nvars : list.

Lemma lKeep_app_r :
  forall {A} (deq : Deq A) (l : list A) l1 l2,
    lKeep deq l (l1 ++ l2) = lKeep deq l l1 ++ lKeep deq l l2.
Proof.
  induction l1; simpl; introv; auto.
  boolvar; simpl in *; tcsp.
  f_equal; tcsp.
Qed.

Lemma implies_is_utok_sub {o} :
  forall l (sub : @Sub o),
    is_utok_sub sub
    -> is_utok_sub (sub_keep sub l).
Proof.
  introv isu i.
  apply in_sub_keep in i; repnd.
  apply isu in i0; auto.
Qed.
Hint Resolve implies_is_utok_sub : slow.

Lemma implies_is_utok_sub_app {o} :
  forall (sub1 sub2 : @Sub o),
    is_utok_sub sub1
    -> is_utok_sub sub2
    -> is_utok_sub (sub1 ++ sub2).
Proof.
  introv isu1 isu2 i; apply in_app_iff in i;
    repndors;[apply isu1 in i|apply isu2 in i]; auto.
Qed.
Hint Resolve implies_is_utok_sub_app : slow.

Lemma sub_keep_app_l {o} :
  forall (sub1 sub2 : @Sub o) l,
    sub_keep (sub1 ++ sub2) l = sub_keep sub1 l ++ sub_keep sub2 l.
Proof.
  induction sub1; introv; simpl; auto.
  repnd; simpl in *; boolvar; simpl in *; tcsp.
  f_equal; tcsp.
Qed.

Lemma implies_not_repeats_utok_sub_sub_keep {o} :
  forall (sub : @Sub o) l,
    no_repeats_utok_sub sub
    -> no_repeats_utok_sub (sub_keep sub l).
Proof.
  introv norep sf1 sf2 d.
  allrw @sub_find_sub_keep_some; repnd.
  eapply norep; eauto.
Qed.
Hint Resolve implies_not_repeats_utok_sub_sub_keep : slow.

Lemma implies_no_repeats_utok_sub_sub_filter {o} :
  forall (sub : @Sub o) l,
    no_repeats_utok_sub sub
    -> no_repeats_utok_sub (sub_filter sub l).
Proof.
  introv norep sf1 sf2 d.
  allrw @sub_find_sub_filter_eq.
  boolvar; ginv.
  eapply norep; eauto.
Qed.
Hint Resolve implies_no_repeats_utok_sub_sub_filter : slow.

Lemma not_in_get_utokens_lib_lsubst_aux_sub_find_some_implies_not_in_get_utokens {o} :
  forall lib a (t : @NTerm o) sub v u,
    !LIn a (get_utokens_lib lib (lsubst_aux t sub))
    -> sub_find sub v = Some u
    -> LIn v (free_vars t)
    -> !LIn a (get_utokens u).
Proof.
  introv ni sf i j; destruct ni.
  apply in_app_iff; left.
  apply get_utokens_lsubst_aux; apply in_app_iff.
  right.
  apply in_get_utokens_sub.
  exists v u; dands; auto.
  apply in_sub_keep_first; dands; auto.
Qed.

Lemma implies_disjoint_get_utokens_sub_sub_keep_sub_filter_r {o} :
  forall (sub : @Sub o) l l1 l2,
    disjoint l (get_utokens_sub sub)
    -> disjoint l (get_utokens_sub (sub_keep (sub_filter sub l1) l2)).
Proof.
  introv d i j; apply d in i; clear d; destruct i.
  allrw @in_get_utokens_sub; exrepnd.
  apply in_sub_keep in j0; repnd.
  apply in_sub_filter in j2; repnd.
  eexists; eexists; dands; eauto.
Qed.
Hint Resolve implies_disjoint_get_utokens_sub_sub_keep_sub_filter_r : slow.

Lemma not_in_get_utokens_lib_lsubst_aux_implies {o} :
  forall a lib (t : @NTerm o) sub,
    !LIn a (get_utokens_lib lib (lsubst_aux t sub))
    -> !LIn a (get_utokens_lib lib t).
Proof.
  introv ni i; destruct ni; allrw in_app_iff; repndors; tcsp.
  left.
  apply get_utokens_lsubst_aux; apply in_app_iff; tcsp.
Qed.
Hint Resolve not_in_get_utokens_lib_lsubst_aux_implies : slow.

Lemma bound_vars_ren_utoks {o} :
  forall (t : @NTerm o) ren,
    bound_vars (ren_utoks ren t) = bound_vars t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; simpl in *; tcsp.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; f_equal.
  eapply ind; eauto 2 with slow.
Qed.
Hint Rewrite @bound_vars_ren_utoks : slow.

Lemma free_vars_ren_utoks {o} :
  forall (t : @NTerm o) ren,
    free_vars (ren_utoks ren t) = free_vars t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; simpl in *; tcsp.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; f_equal.
  eapply ind; eauto 2 with slow.
Qed.
Hint Rewrite @free_vars_ren_utoks : slow.

Lemma all_vars_ren_utoks {o} :
  forall (t : @NTerm o) ren,
    all_vars (ren_utoks ren t) = all_vars t.
Proof.
  introv.
  unfold all_vars; autorewrite with slow; auto.
Qed.
Hint Rewrite @all_vars_ren_utoks : slow.

Lemma lsubst_aux_var_ren_ren_utoks {o} :
  forall (t : @NTerm o) ren l1 l2,
    lsubst_aux (ren_utoks ren t) (var_ren l1 l2)
    = ren_utoks ren (lsubst_aux t (var_ren l1 l2)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; simpl in *; tcsp.

  - Case "vterm".
    remember (sub_find (var_ren l1 l2) v) as sf; symmetry in Heqsf; destruct sf; tcsp.
    apply sub_find_varsub in Heqsf; exrepnd; subst; simpl; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i; destruct x; simpl; f_equal.
    pose proof (@sub_filter_var_ren_implies o l1 l2 l) as q; exrepnd; allrw.
    eapply ind; eauto 2 with slow.
Qed.

Lemma change_bvars_alpha_ren_utoks {o} :
  forall (t : @NTerm o) l ren,
    change_bvars_alpha l (ren_utoks ren t) = ren_utoks ren (change_bvars_alpha l t).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; simpl in *; tcsp.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  erewrite ind; eauto 2 with slow.
  autorewrite with slow.
  f_equal.
  rewrite lsubst_aux_var_ren_ren_utoks; auto.
Qed.

Lemma get_utok_ren_utoks_op {o} :
  forall op (ren : @utok_ren o),
    get_utok (ren_utoks_op ren op)
    = match get_utok op with
      | Some a =>
        match utok_ren_find ren a with
        | Some b => Some b
        | None => Some a
        end
      | None => None
      end.
Proof.
  introv; destruct op; simpl; auto.
  destruct c; simpl; auto.
  unfold ren_utoks_op; simpl.
  remember (utok_ren_find ren g) as x; symmetry in Heqx; destruct x; simpl; auto.
Qed.

Lemma no_repeats_snoc :
  forall {T} (x : T) (l : list T),
    no_repeats (snoc l x) <=> no_repeats l # ! LIn x l.
Proof.
  induction l; simpl; split; intro h; repnd; tcsp.

  - inversion h as [|? ? ni norep]; clear h; subst.
    allrw in_snoc; allrw not_over_or; repnd.
    apply IHl in norep; repnd; dands; tcsp.

  - allrw not_over_or; repnd.
    inversion h0 as [|? ? ni norep]; clear h0; subst.
    constructor; auto.

    + rw in_snoc; tcsp.

    + apply IHl; tcsp.
Qed.

Lemma implies_no_repeats_snoc :
  forall {T} (x : T) (l : list T),
    no_repeats l
    -> ! LIn x l
    -> no_repeats (snoc l x).
Proof.
  introv norep ni; apply no_repeats_snoc; tcsp.
Qed.
Hint Resolve implies_no_repeats_snoc : slow.

Lemma is_utok_sub_snoc {o} :
  forall  (v : NVar) (t : NTerm) (sub : @Sub o),
    is_utok_sub (snoc sub (v, t)) <=> is_utok t # is_utok_sub sub.
Proof.
  introv; split; intro h; tcsp; repnd; dands.

  - pose proof (h v) as q.
    apply q; rw in_snoc; tcsp.

  - introv i; eapply h; apply in_snoc; left; eauto.

  - introv i; apply in_snoc in i; repndors; ginv; tcsp.
    eapply h; eauto.
Qed.

Lemma implies_is_utok_sub_snoc {o} :
  forall  (v : NVar) (t : NTerm) (sub : @Sub o),
    is_utok t
    -> is_utok_sub sub
    -> is_utok_sub (snoc sub (v, t)).
Proof.
  introv i j; apply is_utok_sub_snoc; auto.
Qed.
Hint Resolve implies_is_utok_sub_snoc : slow.

Lemma is_utok_mk_utoken {o} :
  forall (a : get_patom_set o), is_utok (mk_utoken a).
Proof.
  introv.
  simpl; auto.
Qed.
Hint Resolve is_utok_mk_utoken : slow.

Lemma no_repeats_utok_sub_snoc_if_not_in_get_utokens_sub {o} :
  forall (sub : @Sub o) v a,
    !LIn v (dom_sub sub)
    -> no_repeats_utok_sub sub
    -> !LIn a (get_utokens_sub sub)
    -> is_utok_sub sub
    -> no_repeats_utok_sub (snoc sub (v, mk_utoken a)).
Proof.
  introv niv norep nia isu.
  apply no_repeats_utok_sub_snoc; dands; auto.
  introv d sf.
  applydup @sub_find_some_is_utok_sub_implies in sf; auto.
  apply is_utok_implies in sf0; exrepnd; subst; simpl in *.
  eexists; eexists; dands; eauto.
  intro xx; subst.
  apply sub_find_some in sf.
  destruct nia; apply in_get_utokens_sub.
  eexists; eexists; dands; eauto.
  simpl; auto.
Qed.
Hint Resolve no_repeats_utok_sub_snoc_if_not_in_get_utokens_sub : slow.

Lemma eq_preserves_not_in :
  forall {T} (v : T) l1 l2,
    l1 = l2
    -> !LIn v l1
    -> !LIn v l2.
Proof.
  introv h q; subst; tcsp.
Qed.
Hint Resolve eq_preserves_not_in : slow.

Lemma subs2utok_ren_snoc {o} :
  forall (sub1 sub2 : @Sub o) v a b,
    is_utok_sub sub1
    -> is_utok_sub sub2
    -> dom_sub sub1 = dom_sub sub2
    -> subs2utok_ren (snoc sub1 (v,mk_utoken a)) (snoc sub2 (v,mk_utoken b))
       = snoc (subs2utok_ren sub1 sub2) (a,b).
Proof.
  induction sub1; introv isut1 isut2 eqdoms; simpl in *; destruct sub2; simpl in *; ginv.

  repnd.
  allrw @is_utok_sub_cons; repnd.
  apply is_utok_implies in isut3.
  apply is_utok_implies in isut0.
  exrepnd; subst; simpl in *.
  f_equal.
  cpx.
Qed.

Definition ran_utok_ren {o} (ren : @utok_ren o) : list (get_patom_set o) :=
  map snd ren.

Lemma utok_ren_find_snoc_last {o} :
  forall (ren : @utok_ren o) a b,
    !LIn a (dom_utok_ren ren)
    -> utok_ren_find (snoc ren (a, b)) a = Some b.
Proof.
  induction ren; simpl; introv ni; simpl in *; tcsp; boolvar; tcsp.
  allrw not_over_or; repnd.
  simpl in *.
  boolvar; subst; tcsp.
Qed.

Lemma utok_ren_find_snoc_not_last {o} :
  forall (ren : @utok_ren o) a b c,
    a <> c
    -> utok_ren_find (snoc ren (a, b)) c = utok_ren_find ren c.
Proof.
  induction ren; simpl; introv ni; simpl in *; tcsp; boolvar; tcsp.
  repnd; boolvar; subst; tcsp.
Qed.

Lemma utok_ren_find_some_implies_in_ran {o} :
  forall (ren : @utok_ren o) a b,
    utok_ren_find ren a = Some b
    -> LIn b (ran_utok_ren ren).
Proof.
  induction ren; introv find; simpl in *; tcsp.
  repnd; simpl in *; boolvar; ginv; tcsp.
  right.
  eapply IHren; eauto.
Qed.

Lemma get_utok_some_implies_get_utokens_o_eq {o} :
  forall (op : @Opid o) a,
    get_utok op = Some a
    -> get_utokens_o op = [a].
Proof.
  introv e; destruct op; simpl in *; tcsp.
  destruct c; simpl in *; tcsp.
  ginv; auto.
Qed.

Lemma subst_utokens_aux_ren_utoks_snoc_single {o} :
  forall (t : @NTerm o) a b v ren,
    !LIn v (bound_vars t)
    -> !LIn a (dom_utok_ren ren)
    -> !LIn b (ran_utok_ren ren)
    -> !LIn b (get_utokens t)
    -> subst_utokens_aux (ren_utoks (snoc ren (a, b)) t) [(b, mk_var v)]
       = ren_utoks ren (subst_utokens_aux t [(a, mk_var v)]).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
    introv niv nia nib1 nib2; try (complete (simpl in *; auto)).

  Case "oterm".

  allrw @subst_utokens_aux_oterm.
  remember subst_utokens_aux as sua.
  simpl.
  subst.
  allrw @subst_utokens_aux_oterm.
  rewrite get_utok_ren_utoks_op.
  allrw map_map; unfold compose.
  remember (get_utok op) as guo; destruct guo; symmetry in Heqguo.

  - unfold subst_utok; simpl.
    boolvar; subst; simpl.

    + rewrite utok_ren_find_snoc_last; auto.
      boolvar; subst; GC; tcsp.

    + unfold ren_utoks_op; simpl.
      allrw; simpl.
      rewrite utok_ren_find_snoc_not_last; auto.
      remember (utok_ren_find ren g) as find; symmetry in Heqfind.
      destruct find; simpl.

      * boolvar; subst; tcsp.

        {
          apply utok_ren_find_some_implies_in_ran in Heqfind; tcsp.
        }

        {
          f_equal.
          allrw map_map; unfold compose.
          apply eq_maps; introv i.
          destruct x; simpl; f_equal.
          eapply ind; eauto; eauto 2 with slow.
          simpl in *.
          allrw lin_flat_map.
          introv j; destruct niv.
          eexists; dands; eauto.
          simpl; apply in_app_iff; tcsp.
        }

      * boolvar; subst; tcsp.

        {
          simpl in *.
          allrw in_app_iff; allrw not_over_or; repnd.
          apply get_utok_some_implies_get_utokens_o_eq in Heqguo.
          rewrite Heqguo in *; simpl in *; allrw not_over_or; tcsp.
        }

        {
          f_equal.
          allrw map_map; unfold compose.
          apply eq_maps; introv i.
          destruct x; simpl; f_equal.
          eapply ind; eauto; eauto 2 with slow.
          simpl in *.
          allrw lin_flat_map.
          introv j; destruct niv.
          eexists; dands; eauto.
          simpl; apply in_app_iff; tcsp.
        }

  - simpl.
    unfold ren_utoks_op; allrw; simpl.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl; f_equal.
    eapply ind; eauto; eauto 2 with slow.
    simpl in *.
    allrw lin_flat_map.
    introv j; destruct niv.
    eexists; dands; eauto.
    simpl; apply in_app_iff; tcsp.
Qed.

Lemma ran_utok_ren_subs2utok_ren {o} :
  forall (sub1 sub2 : @Sub o),
    length sub1 = length sub2
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> ran_utok_ren (subs2utok_ren sub1 sub2) = get_utokens_sub sub2.
Proof.
  induction sub1; simpl in *; introv eqlen isu1 isu2; ginv;
    destruct sub2; simpl in *; tcsp; repnd.
  allrw @is_utok_sub_cons; repnd.
  apply is_utok_implies in isu0.
  apply is_utok_implies in isu3.
  exrepnd; subst; simpl in *.
  rewrite get_utokens_sub_cons; simpl.
  f_equal; apply IHsub1; auto.
Qed.

Lemma subst_utokens_aux_ren_utoks_subs2utok_ren_snoc_single {o} :
  forall (t : @NTerm o) a b v sub1 sub2,
    dom_sub sub1 = dom_sub sub2
    -> !LIn v (bound_vars t)
    -> !LIn a (get_utokens_sub sub1)
    -> !LIn b (get_utokens_sub sub2)
    -> !LIn b (get_utokens t)
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> subst_utokens_aux
         (ren_utoks
            (subs2utok_ren (snoc sub1 (v,mk_utoken a)) (snoc sub2 (v,mk_utoken b)))
            t)
         [(b, mk_var v)] =
       ren_utoks
         (subs2utok_ren sub1 sub2)
         (subst_utokens_aux t [(a,mk_var v)]).
Proof.
  introv eqdoms nibv nibt niasub1 nibsub2 isu1 isu2.

  rewrite subs2utok_ren_snoc; auto;[].
  remember (subs2utok_ren sub1 sub2) as ren; symmetry in Heqren.
  apply subst_utokens_aux_ren_utoks_snoc_single; auto.

  - subst.
    rewrite dom_utok_ren_subs2utok_ren; auto; eauto 2 with slow.

  - subst.
    rewrite ran_utok_ren_subs2utok_ren; auto; eauto 2 with slow.
Qed.

Lemma implies_oshallow_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    osize t = O1
    -> oshallow_sub sub
    -> oshallow_sub ((v,t) :: sub).
Proof.
  introv h q i.
  simpl in *; repndors; subst; tcsp.
Qed.
Hint Resolve implies_oshallow_sub_cons : slow.

Lemma oshallow_sub_nil {o} : @oshallow_sub o [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve oshallow_sub_nil : slow.

Lemma osize_utoken {o} :
  forall (a : get_patom_set o), osize (mk_utoken a) = O1.
Proof.
  tcsp.
Qed.
Hint Resolve osize_utoken : slow.

Lemma bound_vars_ren_utok {o} :
  forall (t : @NTerm o) a b,
    bound_vars (ren_utok t a b) = bound_vars t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; auto.
  Case "oterm".
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @bound_vars_ren_utok : slow.

Lemma free_vars_ren_utok {o} :
  forall (t : @NTerm o) a b,
    free_vars (ren_utok t a b) = free_vars t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; auto.
  Case "oterm".
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @free_vars_ren_utok : slow.

Lemma all_vars_ren_utok {o} :
  forall (t : @NTerm o) a b,
    all_vars (ren_utok t a b) = all_vars t.
Proof.
  introv.
  unfold all_vars.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @all_vars_ren_utok : slow.

Lemma lsubst_aux_ren_utok_all_vars {o} :
  forall (t : @NTerm o) a b sub,
    allvars_sub sub
    -> lsubst_aux (ren_utok t a b) sub = ren_utok (lsubst_aux t sub) a b.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv asub; simpl in *; auto.

  - Case "vterm".
    remember (sub_find sub v) as q; destruct q; symmetry in Heqq; simpl in *; tcsp.
    apply sub_find_allvars in Heqq; auto.
    exrepnd; subst; simpl in *; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    eapply ind; eauto 3 with slow.
Qed.

Lemma change_bvars_alpha_ren_utok {o} :
  forall (t : @NTerm o) a b l,
    change_bvars_alpha l (ren_utok t a b) = ren_utok (change_bvars_alpha l t) a b.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; auto.
  Case "oterm".
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  erewrite ind;[|eauto].
  autorewrite with slow.
  f_equal.
  rewrite lsubst_aux_ren_utok_all_vars; eauto 3 with slow.
Qed.

Lemma ren_utok_oterm {o} :
  forall (op : @Opid o) bs a b,
    ren_utok (oterm op bs) a b
    = oterm (ren_utok_op op a b) (map (fun bt => ren_utok_b bt a b) bs).
Proof.
  tcsp.
Qed.

Lemma bterm_not_in_bound_vars_oterm_implies {o} :
  forall v (op : @Opid o) bs l t,
    !LIn v (bound_vars (oterm op bs))
    -> LIn (bterm l t) bs
    -> !LIn v (bound_vars t).
Proof.
  introv ni i xx.
  simpl in *.
  allrw lin_flat_map.
  destruct ni.
  eexists; dands; eauto.
  simpl.
  allrw in_app_iff; tcsp.
Qed.
Hint Resolve bterm_not_in_bound_vars_oterm_implies : slow.

Lemma subst_utokens_aux_ren_utok3 {o} :
  forall (t : @NTerm o) v a b a' b' x,
    x <> a
    -> x <> b
    -> x <> a'
    -> x <> b'
    -> b <> b'
    -> !LIn x (get_utokens t)
    -> (!LIn b' (get_utokens t) [+] b' = a [+] b' = a')
    -> !LIn v (bound_vars t)
    -> subst_utokens_aux (ren_utok (ren_utok (ren_utok t a' x) a b) x b') [(b', mk_var v)]
       = ren_utok (subst_utokens_aux t [(a', mk_var v)]) a b.
Proof.
  nterm_ind t as [z|f|op bs ind] Case;
    introv dxa dxb dxa' dxb' dbb' nixt nib't nivt; tcsp.

  Case "oterm".
  allrw @ren_utok_oterm.
  allrw @subst_utokens_aux_oterm.
  simpl.

  unfold ren_utok_op; simpl.

  remember (get_utok op) as guo; destruct guo; symmetry in Heqguo;[|].

  - boolvar; subst;[|].

    + simpl.
      boolvar; tcsp;[].
      simpl.
      boolvar; tcsp; GC;[].
      simpl.

      allrw map_map; unfold compose.
      unfold subst_utok; simpl.
      boolvar; tcsp.

    + allrw.
      boolvar; subst; tcsp;[|].

      * simpl; boolvar; tcsp;[].
        simpl.
        allrw map_map; unfold compose.
        unfold subst_utok; simpl.
        boolvar; tcsp; simpl.
        unfold ren_utok_op; simpl; boolvar; tcsp; GC.

        f_equal.
        allrw map_map; unfold compose.
        apply eq_maps; introv i.
        destruct x0 as [l t]; simpl.

        f_equal.
        eapply ind; eauto 3 with slow; repndors; tcsp; eauto 3 with slow.

      * allrw.
        boolvar; subst; tcsp;[|].

        {
          apply not_in_get_utokens_implies_not_in_get_utokens_o in nixt.
          apply get_utok_some_implies_get_utokens_o_eq in Heqguo.
          rewrite Heqguo in *; simpl in *; allrw not_over_or; tcsp.
        }

        {
          allrw.
          allrw map_map; unfold compose.
          unfold subst_utok; simpl.
          boolvar; subst; tcsp; GC;[|].

          - repndors; try (complete (subst; tcsp)).

            apply not_in_get_utokens_implies_not_in_get_utokens_o in nib't.
            apply get_utok_some_implies_get_utokens_o_eq in Heqguo.
            rewrite Heqguo in *; simpl in *; allrw not_over_or; tcsp.

          - simpl.
            unfold ren_utok_op; simpl.
            boolvar; tcsp;[]; GC.

            f_equal.
            allrw map_map; unfold compose.
            apply eq_maps; introv i.
            destruct x0 as [l t]; simpl.

            f_equal.
            eapply ind; eauto 3 with slow; repndors; eauto 3 with slow.
        }

  - allrw.
    simpl.
    allrw map_map; unfold compose.
    unfold ren_utok_op.
    allrw.

    f_equal.
    apply eq_maps; introv i.
    destruct x0 as [l t]; simpl.

    f_equal.
    eapply ind; eauto 3 with slow; repndors; eauto 3 with slow.
Qed.

Lemma get_utokens_change_bvars_alpha {o} :
  forall (t : @NTerm o) l,
    get_utokens (change_bvars_alpha l t) = get_utokens t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl; tcsp.
  Case "oterm".
  f_equal.
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [vs t]; simpl.
  rewrite get_utokens_lsubst_aux_allvars_sub; eauto 2 with slow.
Qed.
Hint Rewrite @get_utokens_change_bvars_alpha : slow.

Lemma subst_utokens_ren_utok3 {o} :
  forall (t : @NTerm o) v a b a' b' x,
    x <> a
    -> x <> b
    -> x <> a'
    -> x <> b'
    -> b <> b'
    -> !LIn x (get_utokens t)
    -> (!LIn b' (get_utokens t) [+] b' = a [+] b' = a')
    -> subst_utokens (ren_utok (ren_utok (ren_utok t a' x) a b) x b') [(b', mk_var v)]
       = ren_utok (subst_utokens t [(a', mk_var v)]) a b.
Proof.
  introv dxa dxb dxa' dxb' dbb' nixt nib't.
  unfold subst_utokens; simpl; autorewrite with slow.
  destruct (dec_disjointv (bound_vars t) [v]) as [d|d].

  - allrw disjoint_singleton_r.
    apply subst_utokens_aux_ren_utok3; auto.

  - allrw disjoint_singleton_r.
    repeat (rewrite change_bvars_alpha_ren_utok).
    apply subst_utokens_aux_ren_utok3; auto; autorewrite with slow; auto.

    pose proof (change_bvars_alpha_spec t [v]) as q; simpl in q; repnd.
    allrw disjoint_singleton_l; auto.
Qed.

Lemma compute_step_fresh_bs_nil {o} :
  forall lib ncan (t : @NTerm o) v vs u bs comp a w,
    compute_step_fresh lib ncan t v vs u bs comp a = csuccess w
    -> bs = [] /\ vs = [] /\ ncan = NFresh.
Proof.
  introv c.
  apply compute_step_fresh_success in c; exrepnd; subst; allsimpl; auto.
Qed.

Lemma memvar_nil : forall v, memvar v [] = false.
Proof.
  tcsp.
Qed.
Hint Rewrite memvar_nil : slow.

Fixpoint ren_utok_sub {o} (sub : @Sub o) a b :=
  match sub with
  | [] => []
  | (v,t) :: sub => (v,ren_utok t a b) :: ren_utok_sub sub a b
  end.

Lemma sub_find_ren_utok_sub {o} :
  forall (sub : @Sub o) a b v,
    sub_find (ren_utok_sub sub a b) v
    = match sub_find sub v with
      | Some t => Some (ren_utok t a b)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; tcsp.
  repnd; simpl; boolvar; tcsp.
Qed.

Lemma sub_filter_ren_utok {o} :
  forall (sub : @Sub o) a b l,
    sub_filter (ren_utok_sub sub a b) l
    = ren_utok_sub (sub_filter sub l) a b.
Proof.
  induction sub; introv; simpl; tcsp.
  repnd; simpl; boolvar; tcsp.
  simpl; f_equal; tcsp.
Qed.

Lemma ren_utok_lsubst_aux_gen {o} :
  forall (t : @NTerm o) sub a b,
    ren_utok (lsubst_aux t sub) a b
    = lsubst_aux (ren_utok t a b) (ren_utok_sub sub a b).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl; tcsp.

  - Case "vterm".
    rewrite sub_find_ren_utok_sub.
    destruct (sub_find sub v); auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    f_equal.
    rewrite sub_filter_ren_utok.
    eapply ind; eauto.
Qed.

Lemma flat_map_free_vars_range_ren_utok_sub {o} :
  forall (sub : @Sub o) a b,
    flat_map free_vars (range (ren_utok_sub sub a b))
    = flat_map free_vars (range sub).
Proof.
  induction sub; introv; simpl; tcsp.
  repnd; simpl.
  autorewrite with slow.
  rewrite IHsub; auto.
Qed.
Hint Rewrite @flat_map_free_vars_range_ren_utok_sub : slow.

Lemma ren_utok_lsubst_gen {o} :
  forall (t : @NTerm o) sub a b,
    ren_utok (lsubst t sub) a b
    = lsubst (ren_utok t a b) (ren_utok_sub sub a b).
Proof.
  introv.
  unfold lsubst; simpl.
  autorewrite with slow.
  boolvar.

  - apply ren_utok_lsubst_aux_gen.

  - rewrite ren_utok_lsubst_aux_gen.
    rewrite change_bvars_alpha_ren_utok; auto.
Qed.

Lemma ren_utok_subst_gen {o} :
  forall (t : @NTerm o) v u a b,
    ren_utok (subst t v u) a b
    = subst (ren_utok t a b) v (ren_utok u a b).
Proof.
  introv.
  unfold subst.
  rewrite ren_utok_lsubst_gen; simpl; auto.
Qed.

Lemma ren_utok_op_same {o} :
  forall (a b : @get_patom_set o),
    ren_utok_op (Can (NUTok a)) a b = Can (NUTok b).
Proof.
  introv.
  unfold ren_utok_op; simpl; boolvar; tcsp.
Qed.
Hint Rewrite @ren_utok_op_same : slow.

Lemma compute_step_subst_utoken2 {o} :
  forall lib (t u : @NTerm o) v a b,
    nt_wf t
    -> !LIn a (get_utokens_lib lib t)
    -> !LIn b (get_utokens_lib lib t)
    -> compute_step lib (subst_aux t v (mk_utoken a)) = csuccess u
    -> compute_step lib (subst_aux t v (mk_utoken b)) = csuccess (ren_utok u a b).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
    introv wf nia nib comp; tcsp.

  - Case "vterm".
    simpl in *.

    unfold subst_aux in *; simpl in *; boolvar; simpl.

    + csunf comp; simpl in *; ginv.
      csunf; simpl.
      unfold ren_utok_op; simpl; boolvar; tcsp.

    + csunf comp; simpl in *; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    csunf; simpl.
    unfold subst_aux; simpl; auto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl in *; auto.
      unfold subst_aux; simpl.
      allrw map_map; unfold compose.

      f_equal; f_equal.

      { rewrite not_in_get_utokens_o_implies_ren_utok_op_same; auto.
        apply not_in_get_utokens_lib_implies_not_in_get_utokens_o in nia; auto. }

      { apply eq_maps; introv i.
        destruct x as [l t]; simpl.
        f_equal.
        boolvar; simpl; autorewrite with slow.

        - erewrite not_in_get_utokens_lib_implies_ren_utok_same; eauto.
          eapply not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib; eauto.

        - rewrite ren_utok_lsubst_aux; auto.
          eapply not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib in nia;eauto.
          apply not_in_get_utokens_lib_implies_not_in_get_utokens in nia; auto.
      }

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b0 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[| |].

        - allsimpl.
          unfold subst_aux in *; simpl in *; boolvar; simpl in *; ginv.
          apply compute_step_ncan_vterm_success in comp.
          repndors; exrepnd; subst; tcsp;[| | | |].

          + simpl in *.
            unfold ren_utok_op; simpl.
            boolvar; tcsp; GC.
            destruct bs; simpl in *; tcsp.

          + repeat (destruct bs; simpl in *; tcsp).
            destruct b1 as [l t1]; ginv.
            simpl in *; autorewrite with slow.
            boolvar; simpl; csunf; simpl; tcsp; autorewrite with slow.

            * unfold apply_bterm; simpl; allrw @fold_subst.
              rewrite ren_utok_subst_gen.
              simpl; autorewrite with slow.

              assert (!LIn a (get_utokens t1)) as niat1 by (eauto 4 with slow).
              rewrite not_in_get_utokens_implies_ren_utok_same; auto.

            * unfold apply_bterm; simpl.
              rewrite ren_utok_subst_gen.
              rewrite ren_utok_lsubst_aux_gen.
              simpl; autorewrite with slow.

              assert (!LIn a (get_utokens t1)) as niat1 by (eauto 4 with slow).
              rewrite not_in_get_utokens_implies_ren_utok_same; auto.

          + repeat (destruct bs; simpl in *; tcsp).
            destruct b1 as [l t1]; ginv; simpl in *.
            destruct b2 as [k t2]; ginv; simpl in *.
            unfold nobnd in *; ginv.
            simpl in *; autorewrite with slow.
            boolvar; simpl; csunf; simpl; tcsp; autorewrite with slow.

            * unfold ren_utok_op; simpl.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.

              assert (!LIn a (get_utokens t1)) as niat1 by (eauto 4 with slow).
              rewrite not_in_get_utokens_implies_ren_utok_same; auto.

            * unfold ren_utok_op; simpl.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.

              assert (!LIn a (get_utokens t1)) as niat1 by (eauto 4 with slow).
              rewrite not_in_get_utokens_implies_ren_utok_same; auto.

          + allrw @nt_wf_NCompOp; exrepnd.
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *; ginv.
            simpl in *.
            repndors; exrepnd; subst; simpl in *; ginv; repndors; exrepnd; subst; ginv.

            * match goal with
              | [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eqn
              end.
              apply lsubst_aux_utoken_eq_utoken_implies_or in eqn; simpl in *.
              repndors; exrepnd; subst; simpl in *;[|allrw not_over_or; tcsp].

              boolvar; simpl in *.

              { csunf; simpl.
                dcwf h; simpl.
                unfold compute_step_comp; simpl; boolvar; tcsp.
                rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.

                assert (!LIn a (get_utokens t3)) as niat1 by (eauto 5 with slow).
                rewrite not_in_get_utokens_implies_ren_utok_same; auto. }

              { csunf; simpl.
                dcwf h; simpl. }

            * match goal with
              | [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eqn
              end.
              apply lsubst_aux_pk2term_eq_utoken_implies_or in eqn; simpl in *.
              repndors; exrepnd; subst; simpl in *.

              { boolvar; simpl in *; ginv.
                destruct pk; simpl in *; ginv; tcsp. }

              { csunf; simpl.
                rewrite lsubst_aux_pk2term.
                dcwf h; simpl.

                assert (!LIn a (get_utokens t4)) as niat1 by (eauto 6 with slow).

                destruct pk; simpl; tcsp; unfold compute_step_comp; simpl; boolvar; ginv; tcsp.

                - rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
                  rewrite not_in_get_utokens_implies_ren_utok_same; auto.

                - simpl in *.
                  allrw not_over_or; tcsp.

                - rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
                  rewrite not_in_get_utokens_implies_ren_utok_same; auto.

                - rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
                  rewrite not_in_get_utokens_implies_ren_utok_same; auto.
              }

            * autorewrite with slow in *.
              apply isnoncan_like_lsubst_aux_is_utok_sub_implies in comp2; eauto 3 with slow.
              unfold mk_utoken; rewrite compute_step_ncompop_ncanlike2; eauto 3 with slow.
              simpl.

              pose proof (ind t2 t2 []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
              pose proof (q x0 x a b) as w; clear q.
              fold_terms.

              unfold nobnd in *.

              assert (!LIn a (get_utokens_lib lib t2)) as ni1 by (eauto 5 with slow).
              assert (!LIn b (get_utokens_lib lib t2)) as ni2 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t3)) as ni3 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t4)) as ni4 by (eauto 5 with slow).

              repeat (autodimp w hyp).
              allrw; auto.
              unfold ren_utok_op; simpl; auto.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3); eauto 2 with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4); eauto 2 with slow.

            * apply (isexc_lsubst_aux_nr_ut_sub lib _ _ (vterm x)) in comp0; eauto 3 with slow.
              apply isexc_implies2 in comp0.
              exrepnd; subst.
              apply nt_wf_Exc in wf3; exrepnd; subst; simpl in *.
              csunf; simpl; dcwf h.

              unfold nobnd in *.
              assert (!LIn a (get_utokens_lib lib a0)) as ni1 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib b0)) as ni2 by (eauto 5 with slow).

              unfold ren_utok_op; simpl; auto.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0); eauto 2 with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.

          + allrw @nt_wf_NCanTest; exrepnd.
            unfold nobnd in *; ginv; simpl in *.

            csunf; simpl.
            repndors; repnd; subst; simpl.

            * assert (!LIn a (get_utokens_lib lib t3)) as ni1 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3); eauto 2 with slow.

            * remember (canonical_form_test_for x0 (NUTok b)) as cft; destruct cft.

              { destruct x0; simpl in *; ginv; tcsp. }

              assert (!LIn a (get_utokens_lib lib t4)) as ni1 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4); eauto 2 with slow.

        - csunf comp; simpl in comp.
          dopid_noncan ncan SSCase; allsimpl; ginv;[| | | | |].

          + apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            unfold nobnd in *; ginv.
            repeat (destruct bs; allsimpl; ginv).
            destruct b0 as [la ta]; ginv.
            simpl.

            csunf; simpl.
            unfold ren_utok_op; simpl.

            assert (!LIn a (get_utokens_lib lib ta)) as ni1 by (eauto 5 with slow).
            rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
            rewrite (not_in_get_utokens_implies_ren_utok_same _ _ ta); eauto 2 with slow.

          + apply nt_wf_eapply_iff in wf; exrepnd; ginv; simpl in *.

            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
            unfold nobnd in *; ginv.

            repndors; exrepnd; subst.

            * apply compute_step_eapply2_success in comp1.
              exrepnd; GC.
              repndors; exrepnd; ginv;[].

              apply (lsubst_aux_equal_mk_nat lib _ _ _ (sterm f0)) in comp4; eauto 3 with slow.
              subst; simpl in *.
              csunf; simpl.
              unfold compute_step_eapply; simpl; boolvar; try omega.
              autorewrite with slow.
              rewrite Nat2Z.id.
              rewrite not_in_get_utokens_implies_ren_utok_same; auto.
              rw @nt_wf_sterm_iff in wf2.
              pose proof (wf2 n) as q; clear wf2; repnd.
              rewrite q; simpl; tcsp.

            * apply (isexc_lsubst_aux_nr_ut_sub lib _ _ (sterm f)) in comp0; eauto 3 with slow.
              apply isexc_implies2 in comp0; exrepnd; subst.
              apply nt_wf_Exc in wf1; exrepnd; subst; simpl in *.
              csunf; simpl.
              unfold compute_step_eapply; simpl.

              unfold nobnd in *.

              assert (!LIn a (get_utokens_lib lib a0)) as ni1 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0); eauto 2 with slow.

              assert (!LIn a (get_utokens_lib lib b0)) as ni2 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.

            * apply isnoncan_like_lsubst_aux_is_utok_sub_implies in comp3; eauto 3 with slow.
              unfold subst_aux; simpl.
              fold_terms; unfold mk_eapply.
              rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.

              pose proof (ind b0 b0 []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
              pose proof (q x v a b) as w; clear q.
              fold_terms.

              unfold mk_eapply in *.
              unfold nobnd in *.

              assert (!LIn a (get_utokens_lib lib b0)) as ni1 by (eauto 5 with slow).
              assert (!LIn b (get_utokens_lib lib b0)) as ni2 by (eauto 5 with slow).

              unfold subst_aux in *.
              repeat (autodimp w hyp).
              allrw; auto.

          + apply nt_wf_NFix in wf; exrepnd; subst; simpl in *.
            destruct bs; simpl in *; ginv.

          + apply nt_wf_NCbv in wf; exrepnd; subst; simpl in *.
            repeat (destruct bs; simpl in *; ginv).
            destruct b1; simpl in *.
            unfold nobnd in *; ginv.
            csunf; simpl.
            unfold apply_bterm; simpl.
            autorewrite with slow.
            boolvar; simpl; autorewrite with slow.

            * assert (!LIn a (get_utokens_lib lib b0)) as ni1 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.

            * assert (!LIn a (get_utokens_lib lib b0)) as ni1 by (eauto 5 with slow).
              rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow.
              rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.

          + apply nt_wf_NTryCatch in wf; exrepnd; subst.
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *; ginv.
            csunf; simpl.
            unfold ren_utok_op; simpl.

            assert (!LIn a (get_utokens_lib lib b0)) as ni1 by (eauto 5 with slow).
            rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
            rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.

          + apply nt_wf_NCanTest in wf; exrepnd; subst.
            repeat (destruct bs; simpl in *; ginv).
            unfold nobnd in *; ginv.
            csunf; simpl.

            assert (!LIn a (get_utokens_lib lib t3)) as ni1 by (eauto 5 with slow).
            rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow.
            rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3); eauto 2 with slow.

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

            }

          + SSCase "NCan".

          + SSCase "Exc".

          + SSCase "Abs".

      }

      applydup @compute_step_preserves_utokens in comp as pres; eauto 3 with slow;
        [|allrw @fold_subst_aux; repeat (apply subst_aux_preserves_wf; eauto 2 with slow)].

      csunf comp; allsimpl.
      unfold subst_aux in *; simpl in *.
      allrw memvar_cons.

      dup comp as eqn.
      apply compute_step_fresh_bs_nil in eqn.
      repnd.
      repeat (destruct bs; allsimpl; ginv); autorewrite with slow in *;[].

      allrw @nt_wf_fresh.

      destruct (deq_nvar v n) as [d|d]; subst; autorewrite with slow in *.

      {
        apply compute_step_fresh_success in comp; exrepnd; subst; allsimpl; GC.
        repndors; exrepnd; subst; simpl.

        - csunf; simpl.
          boolvar.
          unfold ren_utok_op; simpl; auto.

        - fold (mk_fresh n t) in *.
          rewrite compute_step_fresh_if_isvalue_like; auto.
          rewrite not_in_get_utokens_implies_ren_utok_same; auto.
          rewrite get_utokens_pushdown_fresh.
          apply not_in_get_utokens_lib_implies_not_in_get_utokens in nia.
          simpl in *; autorewrite with slow in *; auto.

        - fold (mk_fresh n t) in *.
          rewrite computation2.compute_step_fresh_if_isnoncan_like; auto.
          simpl.
          allrw; simpl.
          rewrite not_in_get_utokens_implies_ren_utok_same; auto.
          simpl in *; autorewrite with slow in *; auto.
          introv i.
          apply get_utokens_subst_utokens_subset in i; simpl in *.
          unfold get_utokens_utok_ren in *; simpl in *; autorewrite with slow in *.
          apply in_remove in i; repnd.

          applydup @compute_step_preserves_utokens in comp2;
            [|apply nt_wf_subst; eauto 2 with slow].
          pose proof (comp0 a) as w; autodimp w hyp; eauto 3 with slow.
          apply get_utokens_lib_subst in w; simpl in *.
          apply in_app_iff in w; repndors; tcsp.
          boolvar; simpl in *; tcsp.
      }

      destruct (in_deq _ deq_nvar v (free_vars t)) as [d1|d1].

      {
        apply compute_step_fresh_success in comp; exrepnd; subst; allsimpl; GC.

        repndors; exrepnd; subst; simpl in *.

        {
          csunf; simpl; autorewrite with slow in *.
          apply lsubst_aux_eq_vterm_is_utok_sub_implies in comp0; eauto 3 with slow;[].
          subst; simpl in *.
          boolvar; tcsp.
        }

        {
          csunf; simpl in *; autorewrite with slow in *.
          apply isvalue_like_lsubst_aux_implies in comp0.
          fold_terms; autorewrite with slow in *.
          repndors; exrepnd;[|].

          - unfold isvalue_like in comp0; repndors.

            + apply iscan_implies in comp0; repndors; exrepnd; subst; simpl in *; auto.
              rewrite not_in_get_utokens_o_implies_ren_utok_op_same; auto;
                [|apply not_in_get_utokens_lib_implies_not_in_get_utokens_o in nia; auto].
              f_equal; f_equal.

              unfold mk_fresh_bterms.
              allrw map_map; unfold compose.
              apply eq_maps; introv i.
              destruct x as [l t]; simpl; f_equal.
              unfold ren_utok_op; simpl; fold_terms.
              boolvar; autorewrite with slow in *.

              * erewrite not_in_get_utokens_lib_implies_ren_utok_same; auto.
                eapply not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib; eauto.

              * f_equal; eauto 2 with slow.
                rewrite ren_utok_lsubst_aux; eauto 3 with slow.

            + apply isexc_implies2 in comp0; exrepnd; subst; simpl in *.
              unfold ren_utok_op; simpl.
              f_equal; f_equal.

              unfold mk_fresh_bterms.
              allrw map_map; unfold compose.
              apply eq_maps; introv i.
              destruct x as [vs t]; simpl; f_equal.
              unfold ren_utok_op; simpl; fold_terms.
              boolvar; autorewrite with slow in *.

              * erewrite not_in_get_utokens_lib_implies_ren_utok_same; auto.
                eapply not_in_get_utokens_lib_oterm_implies_not_in_get_utokens_lib; eauto.

              * f_equal; eauto 2 with slow.
                rewrite ren_utok_lsubst_aux; eauto 3 with slow.

          - subst; simpl in *; boolvar; simpl in *; tcsp.
            unfold ren_utok_op; simpl; boolvar; tcsp.
        }

        {
          unfold ren_utok_op; simpl; fold_terms.
          autorewrite with slow in *; GC.
          applydup @isnoncan_like_lsubst_aux_is_utok_sub_implies in comp1; eauto 3 with slow;[].

          fold_terms; rewrite @computation2.compute_step_fresh_if_isnoncan_like;
            autorewrite with slow in *; eauto 2 with slow;[].

          pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t [(v,mk_utoken a)])) as propa.
          pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t [(v,mk_utoken b)])) as propb.

          remember (get_fresh_atom lib (lsubst_aux t [(v,mk_utoken a)])) as a'.
          remember (get_fresh_atom lib (lsubst_aux t [(v,mk_utoken b)])) as b'.
          simpl.

          pose proof (fresh_atom o (a :: b :: a' :: b' :: get_utokens_lib lib t)) as xx; exrepnd.

          unfsubst in comp2.
          unfsubst.

          pose proof (ind t (lsubst_aux t [(v, mk_utoken a)]) [n]) as q.
          repeat (autodimp q hyp);[rewrite simple_osize_lsubst_aux; eauto 3 with slow|].
          pose proof (q x n a' x0) as h; clear q.
          repeat (autodimp h hyp).

          {
            apply lsubst_aux_preserves_wf; simpl; tcsp.
            introv xx; repndors; tcsp; ginv; eauto 2 with slow.
          }

          {
            introv i.
            apply get_utokens_lib_lsubst_aux in i; simpl in *.
            allrw not_over_or; repnd.
            apply in_app_iff in i; repndors; tcsp.
            boolvar; simpl in *; repndors; tcsp.
          }

          pose proof (cl_lsubst_aux_swap t [(v, mk_utoken a)] [(n, mk_utoken x0)]) as w.
          repeat (autodimp w hyp); simpl; eauto 3 with slow.
          rewrite w in h; clear w.

          pose proof (ind t (lsubst_aux t [(n, mk_utoken x0)]) [n]) as q.
          repeat (autodimp q hyp);[rewrite simple_osize_lsubst_aux; eauto 3 with slow|].
          pose proof (q (ren_utok x a' x0) v a b) as z; clear q.
          repeat (autodimp z hyp).

          {
            apply lsubst_aux_preserves_wf; simpl; tcsp.
            introv xx; repndors; tcsp; ginv; eauto 2 with slow.
          }

          {
            introv i.
            apply get_utokens_lib_lsubst_aux in i; simpl in *.
            destruct nia.
            apply in_app_iff in i; repndors; tcsp.
            boolvar; simpl in *; repndors; tcsp.
            allrw not_over_or; repnd; tcsp.
          }

          {
            introv i.
            apply get_utokens_lib_lsubst_aux in i; simpl in *.
            destruct nib.
            apply in_app_iff in i; repndors; tcsp.
            boolvar; simpl in *; repndors; tcsp.
            allrw not_over_or; repnd; tcsp.
          }

          clear h.

          pose proof (cl_lsubst_aux_swap t [(n, mk_utoken x0)] [(v, mk_utoken b)]) as w.
          repeat (autodimp w hyp); simpl; eauto 3 with slow.
          rewrite w in z; clear w.

          pose proof (ind t (lsubst_aux t [(v, mk_utoken b)]) [n]) as q.
          repeat (autodimp q hyp);[rewrite simple_osize_lsubst_aux; eauto 3 with slow|].
          pose proof (q (ren_utok (ren_utok x a' x0) a b) n x0 b') as h; clear q.
          repeat (autodimp h hyp).

          {
            apply lsubst_aux_preserves_wf; simpl; tcsp.
            introv xx; repndors; tcsp; ginv; eauto 2 with slow.
          }

          {
            introv i.
            apply get_utokens_lib_lsubst_aux in i; simpl in *.
            allrw not_over_or; repnd; tcsp.
            apply in_app_iff in i; repndors; tcsp.
            boolvar; simpl in *; repndors; tcsp.
          }

          clear z.

          rewrite h.

          simpl.

          f_equal; f_equal.
          simpl in *.
          allrw not_over_or; repnd.

          applydup @compute_step_preserves_utokens in comp2; eauto 3 with slow;
            [|allrw @fold_subst_aux; repeat (apply subst_aux_preserves_wf; eauto 2 with slow)].

          apply subst_utokens_ren_utok3; auto.

          {
            introv xx; subst b.
            destruct propb.
            apply get_utokens_lib_lsubst_aux.
            simpl; boolvar; tcsp;[].
            unfold get_utokens_sub; simpl.
            apply in_app_iff; simpl; tcsp.
          }

          {
            introv i.
            eapply get_utokens_subset_get_utokens_lib in i.
            apply comp3 in i; clear comp3.
            apply get_utokens_lib_lsubst_aux in i; simpl in i.
            apply in_app_iff in i; repndors;[|boolvar; simpl in *; tcsp].
            apply get_utokens_lib_lsubst_aux in i; simpl in i.
            apply in_app_iff in i; repndors; tcsp.
            boolvar; simpl in *; tcsp.
          }

          {
            destruct (in_deq _ (get_patom_deq o) b' (get_utokens x)) as [d2|d2]; tcsp.
            pose proof (comp3 b') as w; clear comp3; autodimp w hyp; eauto 2 with slow.
            apply get_utokens_lib_lsubst_aux in w; simpl in w.
            apply in_app_iff in w; repndors;[|boolvar; simpl in *; tcsp].
            apply get_utokens_lib_lsubst_aux in w; simpl in w.
            apply in_app_iff in w; repndors; tcsp.
            - destruct propb.
              apply get_utokens_lib_lsubst_aux; apply in_app_iff; tcsp.
            - boolvar; tcsp; simpl in *; tcsp.
          }
        }
      }

      {
        rewrite (lsubst_aux_trivial_cl_term t _);[|allrw disjoint_singleton_r; auto].
        rewrite (lsubst_aux_trivial_cl_term t _) in comp;[|allrw disjoint_singleton_r; auto].
        rewrite (lsubst_aux_trivial_cl_term t _) in pres;[|allrw disjoint_singleton_r; auto].
        fold_terms; rewrite @get_utokens_lib_mk_fresh in *.
        assert (!LIn a (get_utokens u)) as ni.
        { intro i; eapply get_utokens_subset_get_utokens_lib in i; apply pres in i; tcsp. }
        rewrite not_in_get_utokens_implies_ren_utok_same; auto.
        csunf; allsimpl; tcsp.
      }

    + SCase "Exc".

      admit.

    + SCase "Abs".

      admit.

Qed.

Lemma compute_step_subst_utoken2 {o} :
  forall lib (t u : @NTerm o) sub1 sub2,
    no_repeats (dom_sub sub1)
    -> dom_sub sub1 = dom_sub sub2
    -> is_utok_sub sub1
    -> is_utok_sub sub2
    -> no_repeats_utok_sub sub1
    -> no_repeats_utok_sub sub2
    -> disjoint (get_utokens_lib lib t) (get_utokens_sub sub1)
    -> disjoint (get_utokens_lib lib t) (get_utokens_sub sub2)
    -> compute_step lib (lsubst_aux t sub1) = csuccess u
    -> compute_step lib (lsubst_aux t sub2) = csuccess (ren_utoks (subs2utok_ren sub1 sub2) u).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case;
    introv norep eqdoms iu1 iu2 norep1 norep2 disj1 disj2 comp; tcsp.

  - Case "vterm".
    simpl in *.

    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1;
      remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2.

    + applydup @sub_find_some_is_utok_sub_implies in Heqsf1 as isu1; auto.
      applydup @sub_find_some_is_utok_sub_implies in Heqsf2 as isu2; auto.
      apply is_utok_implies in isu1.
      apply is_utok_implies in isu2.
      exrepnd; subst; simpl in *.
      csunf comp; simpl in comp; ginv.
      csunf; simpl.
      unfold ren_utoks_op; simpl.
      erewrite implies_utok_ren_find_subst2utok_ren_some; eauto; auto.

    + eapply eq_dom_sub_sub_find_some_implies in Heqsf1 as w;[|eauto].
      exrepnd.
      rewrite w0 in Heqsf2; ginv.

    + eapply eq_dom_sub_sub_find_some_implies in Heqsf2 as w;[|symmetry; eauto].
      exrepnd.
      rewrite w0 in Heqsf1; ginv.

    + csunf comp; simpl in *; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl in *; auto.
      unfold subst_aux; simpl.
      allrw map_map; unfold compose.

      f_equal; f_equal.

      { rewrite not_in_get_utokens_o_implies_ren_utoks_op_same; auto.
        rewrite dom_utok_ren_subs2utok_ren; eauto 2 with slow. }

      { apply eq_maps; introv i.
        destruct x as [l t]; simpl.
        f_equal.
        erewrite ren_utoks_lsubst_aux_sub_filter; eauto 3 with slow. }

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).


      (* XXXXXXXXXXXXXXXXXXXXXXX *)


      Focus 2.


      (* XXXXXXXXXXXXXXXXXXXXXXX *)


      csunf comp; allsimpl.
      autorewrite with slow in *.
      apply compute_step_fresh_success in comp; exrepnd; subst; allsimpl.
      repeat (destruct bs; allsimpl; ginv); autorewrite with slow in *.

      repndors; exrepnd; subst; simpl in *.

      {
        csunf; simpl; autorewrite with slow in *.
        applydup @lsubst_aux_eq_vterm_is_utok_sub_implies in comp0; eauto 2 with slow;[].
        subst; simpl in *.
        autorewrite with slow in *.
        boolvar; simpl in *; GC; auto.
      }

      {
        csunf; simpl in *; autorewrite with slow in *.
        apply isvalue_like_lsubst_aux_implies in comp0.
        fold_terms; autorewrite with slow in *.
        repndors; exrepnd;[|].

        - unfold isvalue_like in comp0; repndors.

          + apply iscan_implies in comp0; repndors; exrepnd; subst; simpl in *; auto.
            rewrite not_in_get_utokens_o_implies_ren_utoks_op_same; eauto 2 with slow;
              try (complete (rewrite dom_utok_ren_subs2utok_ren; eauto 2 with slow)).
            f_equal; f_equal.

            unfold mk_fresh_bterms.
            allrw map_map; unfold compose.
            apply eq_maps; introv i.
            destruct x as [l t]; simpl; f_equal.
            unfold ren_utok_op; simpl; fold_terms.
            boolvar; autorewrite with slow in *.
            unfold ren_utoks_op; simpl; fold_terms.
            f_equal; eauto 2 with slow;
              allrw <- @sub_filter_app_r; eauto 2 with slow.
            erewrite ren_utoks_lsubst_aux_sub_filter; eauto 3 with slow.

          + apply isexc_implies2 in comp0; exrepnd; subst; simpl in *.
            unfold ren_utok_op; simpl.
            f_equal; f_equal.

            unfold mk_fresh_bterms.
            allrw map_map; unfold compose.
            apply eq_maps; introv i.
            destruct x as [vs t]; simpl; f_equal.
            unfold ren_utoks_op; simpl; fold_terms.
            f_equal; eauto 2 with slow;
              allrw <- @sub_filter_app_r; eauto 2 with slow.
            erewrite ren_utoks_lsubst_aux_sub_filter; eauto 3 with slow.

        - subst; simpl in *; boolvar; simpl in *; tcsp.
          allrw @sub_find_sub_filter_eq; autorewrite with slow in *.
          boolvar; ginv;[].

          dup comp1 as sf.
          eapply eq_dom_sub_sub_find_some_implies in sf;[|eauto];[].
          exrepnd; allrw.

          applydup @sub_find_some_is_utok_sub_implies in comp1; auto.
          applydup @sub_find_some_is_utok_sub_implies in sf0; auto.
          apply is_utok_implies in comp2.
          apply is_utok_implies in sf1.
          exrepnd; subst; simpl in *.

          unfold ren_utoks_op; simpl.
          erewrite implies_utok_ren_find_subst2utok_ren_some; eauto.
      }

      {
        unfold ren_utoks_op; simpl; fold_terms.
        autorewrite with slow in *; GC.
        applydup @isnoncan_like_lsubst_aux_is_utok_sub_implies in comp1; eauto 2 with slow;[].

        fold_terms; rewrite @computation2.compute_step_fresh_if_isnoncan_like; autorewrite with slow in *; eauto 2 with slow;[].

        pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t (sub_filter sub1 [n]))) as propa.
        pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t (sub_filter sub2 [n]))) as propb.

        remember (get_fresh_atom lib (lsubst_aux t (sub_filter sub1 [n]))) as a'.
        remember (get_fresh_atom lib (lsubst_aux t (sub_filter sub2 [n]))) as b'.
        simpl.

        unfsubst in comp2.
        unfsubst.

        rewrite <- cl_lsubst_aux_app in comp2; eauto 3 with slow;[].
        rewrite <- cl_lsubst_aux_app; eauto 3 with slow;[].

        pose proof (simple_lsubst_aux_trim t (sub_filter sub1 [n] ++ [(n, mk_utoken a')])) as w.
        autodimp w hyp.
        { introv i; apply in_app_iff in i; simpl in i; repndors; ginv; simpl in *; tcsp.
          allrw @in_sub_filter; repnd.
          apply iu1 in i0; apply is_utok_implies in i0; exrepnd; subst; simpl in *; auto. }

        pose proof (simple_lsubst_aux_trim t (sub_filter sub2 [n] ++ [(n, mk_utoken b')])) as z.
        autodimp z hyp.
        { introv i; apply in_app_iff in i; simpl in i; repndors; ginv; simpl in *; tcsp.
          allrw @in_sub_filter; repnd.
          apply iu2 in i0; apply is_utok_implies in i0; exrepnd; subst; simpl in *; auto. }

        pose proof (ind t t [n]) as q; repeat (autodimp q hyp); eauto 2 with slow; clear ind.
        pose proof (q x
                      (sub_keep (sub_filter sub1 [n] ++ [(n, mk_utoken a')]) (free_vars t))
                      (sub_keep (sub_filter sub2 [n] ++ [(n, mk_utoken b')]) (free_vars t))) as h; clear q.
        allrw @dom_sub_sub_keep.
        allrw @dom_sub_app; simpl in *.
        allrw <- @dom_sub_sub_filter.
        repeat (autodimp h hyp); eauto 3 with slow list.

        {
          apply implies_no_repeats_lKeep.
          apply no_repeats_app; dands; eauto 3 with slow list.
        }

        { allrw; auto. }

        {
          apply implies_is_utok_sub.
          apply implies_is_utok_sub_app; eauto 3 with slow.
        }

        {
          apply implies_is_utok_sub.
          apply implies_is_utok_sub_app; eauto 3 with slow.
        }

        {
          rewrite sub_keep_app_l; simpl; boolvar; autorewrite with slow; eauto 3 with slow;[].
          allrw <- snoc_as_append.
          apply no_repeats_utok_sub_snoc; dands; eauto 3 with slow.
          - rw @dom_sub_sub_keep.
            rw <- @dom_sub_sub_filter.
            intro i; apply in_lkeep_iff in i; repnd.
            apply in_remove_nvars in i; simpl in i; repnd; tcsp.
          - introv d sf.
            apply sub_find_sub_keep_some in sf; repnd.
            eapply not_in_get_utokens_lib_lsubst_aux_sub_find_some_implies_not_in_get_utokens in propa;[|eauto|]; auto.
            rw @sub_find_sub_filter_eq in sf0; autorewrite with slow in *.
            boolvar; tcsp.
            apply sub_find_some_is_utok_sub_implies in sf0; auto.
            apply is_utok_implies in sf0; exrepnd; subst u; simpl in *.
            allrw not_over_or; repnd; GC.
            eexists; eexists; dands; eauto.
        }

        {
          rewrite sub_keep_app_l; simpl; boolvar; autorewrite with slow; eauto 3 with slow;[].
          allrw <- snoc_as_append.
          apply no_repeats_utok_sub_snoc; dands; eauto 3 with slow.
          - rw @dom_sub_sub_keep.
            rw <- @dom_sub_sub_filter.
            intro i; apply in_lkeep_iff in i; repnd.
            apply in_remove_nvars in i; simpl in i; repnd; tcsp.
          - introv d sf.
            apply sub_find_sub_keep_some in sf; repnd.
            eapply not_in_get_utokens_lib_lsubst_aux_sub_find_some_implies_not_in_get_utokens in propb;[|eauto|]; auto.
            rw @sub_find_sub_filter_eq in sf0; autorewrite with slow in *.
            boolvar; tcsp.
            apply sub_find_some_is_utok_sub_implies in sf0; auto.
            apply is_utok_implies in sf0; exrepnd; subst u; simpl in *.
            allrw not_over_or; repnd; GC.
            eexists; eexists; dands; eauto.
        }

        {
          rw @sub_keep_app_l; simpl.
          rw @get_utokens_sub_app.
          apply disjoint_app_r; dands; eauto 2 with slow.
          boolvar; autorewrite with slow; auto.
          unfold get_utokens_sub; simpl; apply disjoint_singleton_r; eauto 3 with slow.
        }

        {
          rw @sub_keep_app_l; simpl.
          rw @get_utokens_sub_app.
          apply disjoint_app_r; dands; eauto 2 with slow.
          boolvar; autorewrite with slow; auto.
          unfold get_utokens_sub; simpl; apply disjoint_singleton_r; eauto 3 with slow.
        }

        { allrw <-; auto. }

        rewrite <- z in h.
        rewrite h; simpl.

        clear w z h.

        f_equal; f_equal.

        unfold subst_utokens; simpl; autorewrite with slow.
        rewrite change_bvars_alpha_ren_utoks.

        boolvar; allrw disjoint_singleton_r.

        - repeat (rewrite sub_keep_app_l).
          simpl.
          boolvar.

          + repeat (rewrite <- snoc_as_append).
            rewrite subst_utokens_aux_ren_utoks_subs2utok_ren_snoc_single; auto.

            * remember (subst_utokens_aux x [(a', mk_var n)]) as u; symmetry in Hequ.

              SearchAbout compute_step get_utokens_sub.

      }

XXXXXXXXXXX

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));
          [ | | ].

        { allsimpl.
          allrw @sub_filter_nil_r.
          remember (sub_find sub x) as sf; symmetry in Heqsf; destruct sf;
          [|csunf comp; allsimpl; ginv].

          applydup @sub_find_some in Heqsf.
          eapply in_nr_ut_sub in Heqsf0; eauto; exrepnd; subst.
          apply compute_step_ncan_vterm_success in comp.
          repndors; exrepnd; subst.

          - exists (@mk_axiom o); allsimpl.
            dands; eauto 3 with slow.

            { apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; auto. }

            introv nrut' eqdoms disj'.
            dands; eauto 3 with slow.
            simpl; allrw @sub_filter_nil_r.
            pose proof (sub_find_some_eq_doms_nr_ut_sub lib sub sub' x (oterm (NCan NParallel) (bterm [] (vterm x) :: bs))) as h; repeat (autodimp h hyp).
            rw Heqsf in h; exrepnd; rw h0.
            csunf; simpl.
            unfold compute_step_parallel; auto.

          - destruct bs; allsimpl; cpx; GC.
            exists (@mk_apply o (mk_var x) (mk_fix (mk_var x))).
            simpl; allrw @sub_filter_nil_r; allrw; dands; eauto 3 with slow.
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

            exists (lsubst_aux t [(x0, mk_var x)]).
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

              * eapply subset_disjoint_r;[eauto|].
                unfold get_utokens_lib.
                allrw; simpl; auto.

              * apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                allrw; auto.

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
              dands; eauto 3 with slow;[|].

              {
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                autorewrite with slow; eauto 3 with slow.
              }

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

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

              {
                unfold get_utokens_lib; simpl; autorewrite with slow.
                repeat (apply implies_subset_app); eauto 4 with slow.
              }

              introv nrut' eqdoms' disj'.
              unflsubst; simpl; autorewrite with slow in *.
              eapply isnoncan_like_lsubst_aux_nr_ut_implies in comp3; eauto;[].
              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow;[].
              pose proof (ih0 sub') as h'; clear ih0.
              repeat (autodimp h' hyp); eauto 3 with slow.

              { eapply nr_ut_sub_change_term;[| |exact nrut']; simpl; autorewrite with slow; auto. }

              {
                eapply subset_disjoint_r;[eauto|].
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
                eauto 3 with slow.
              }

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

            + eapply disjoint_eqset_r;[apply eqset_sym; apply get_utokens_lib_subst|].
              eapply subset_disjoint_r;[eauto|].
              boolvar; simpl; autorewrite with slow;
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl; eauto 3 with slow.

            + eapply subvars_eqvars;[|apply eqvars_sym;apply eqvars_free_vars_disjoint].
              allsimpl.
              apply subvars_app_l; dands; auto.
              boolvar; simpl; auto.

            + eapply subset_eqset_l;[apply eqset_sym;apply get_utokens_lib_subst|].
              boolvar; simpl; autorewrite with slow; auto;
                apply subset_get_utokens_implies_subset_get_utokens_lib; simpl;
                  autorewrite with slow; eauto 3 with slow.

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

            {
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              autorewrite with slow; eauto 3 with slow.
            }

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

            {
              apply subset_get_utokens_implies_subset_get_utokens_lib; simpl.
              autorewrite with slow; eauto 3 with slow.
            }

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
