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

Lemma iscan_lsubst_aux_utoken {o} :
  forall (t : @NTerm o) v a,
    iscan (lsubst_aux t [(v, mk_utoken a)])
    -> iscan t [+] t = mk_var v.
Proof.
  introv isc.
  destruct t as [x|f|op bs ind]; simpl in *; tcsp.
  boolvar; tcsp.
Qed.

Lemma iscan_lsubst_aux_change_utoken {o} :
  forall (t : @NTerm o) v a b,
    iscan (lsubst_aux t [(v, mk_utoken a)])
    -> iscan (lsubst_aux t [(v, mk_utoken b)]).
Proof.
  introv isc.
  destruct t as [x|f|op bs ind]; simpl in *; tcsp.
  boolvar; tcsp.
Qed.
Hint Resolve iscan_lsubst_aux_change_utoken : slow.

Hint Rewrite Nat2Z.id : slow.

Lemma lsubst_aux_eq_can_nil_implies {o} :
  forall (t : @NTerm o) v a can,
    lsubst_aux t [(v, mk_utoken a)] = oterm (Can can) []
    -> t = oterm (Can can) [] [+] (t = mk_var v # can = NUTok a).
Proof.
  introv equ; destruct t as [x|f|op bs]; simpl in *; ginv; tcsp.

  - boolvar; unfold mk_utoken in *; ginv; tcsp.

  - inversion equ; subst; clear equ.
    repeat (destruct bs; simpl in *; ginv).
Qed.

Lemma find_entry_implies_get_utokens_subset {o} :
  forall lib abs (bs : list (@BTerm o)) oa vars rhs correct,
    find_entry lib abs bs = Some (lib_abs oa vars rhs correct)
    -> subset (get_utokens_so rhs) (get_utokens_library lib).
Proof.
  induction lib; introv find; simpl in *; ginv.
  destruct a; tcsp.

  - apply IHlib in find; eauto 3 with slow.

  - boolvar; ginv.

    + inversion find; subst; simpl; eauto 3 with slow.

    + simpl.
      apply IHlib in find; eauto 3 with slow.
Qed.

Lemma free_vars_sosub_mk_abs_subst_ren_utok {o} :
  forall vars (bs : list (@BTerm o)) a b,
    free_vars_sosub (mk_abs_subst vars (map (fun x => ren_utok_b x a b) bs))
    = free_vars_sosub (mk_abs_subst vars bs).
Proof.
  induction vars; introv; simpl; auto.
  destruct a; simpl.
  destruct bs; simpl; auto.
  destruct b0; simpl.
  boolvar; simpl; auto.
  autorewrite with slow.
  f_equal.
  apply IHvars.
Qed.
Hint Rewrite @free_vars_sosub_mk_abs_subst_ren_utok : slow.

Lemma bound_vars_sosub_mk_abs_subst_ren_utok {o} :
  forall vars (bs : list (@BTerm o)) a b,
    bound_vars_sosub (mk_abs_subst vars (map (fun x => ren_utok_b x a b) bs))
    = bound_vars_sosub (mk_abs_subst vars bs).
Proof.
  induction vars; introv; simpl; auto.
  destruct a; simpl.
  destruct bs; simpl; auto.
  destruct b0; simpl.
  boolvar; simpl; auto.
  autorewrite with slow.
  f_equal.
  apply IHvars.
Qed.
Hint Rewrite @bound_vars_sosub_mk_abs_subst_ren_utok : slow.

Lemma sosub_find_mk_abs_subst_ren_utok {o} :
  forall vars (bs : list (@BTerm o)) a b v n,
    sosub_find (mk_abs_subst vars (map (fun x => ren_utok_b x a b) bs)) (v, n)
    = match sosub_find (mk_abs_subst vars bs) (v,n) with
      | Some (sosk vs u) => Some (sosk vs (ren_utok u a b))
      | None => None
      end.
Proof.
  induction vars; introv; simpl; auto.
  destruct a; simpl.
  destruct bs; simpl; auto.
  destruct b0; simpl.
  boolvar; subst; simpl; tcsp.
  boolvar; subst; simpl; tcsp.
Qed.

Lemma ren_utok_sub_combine {o} :
  forall l (ts : list (@NTerm o)) a b,
    ren_utok_sub (combine l ts) a b = combine l (map (fun t => ren_utok t a b) ts).
Proof.
  induction l; introv; simpl; auto.
  destruct ts; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma ren_utok_apply_list {o} :
  forall ts (t : @NTerm o) a b,
    ren_utok (apply_list t ts) a b
    = apply_list (ren_utok t a b) (map (fun x => ren_utok x a b) ts).
Proof.
  induction ts; introv; simpl; auto.
  apply IHts.
Qed.

Definition ren_utok_sosub_kind {o} (sk : @sosub_kind o) a b :=
  match sk with
  | sosk l t => sosk l (ren_utok t a b)
  end.

Fixpoint ren_utok_sosub {o} (s : @SOSub o) a b :=
  match s with
  | [] => []
  | (v,sk) :: l => (v, ren_utok_sosub_kind sk a b) :: ren_utok_sosub l a b
  end.

Lemma sosub_find_ren_utok_sosub {o} :
  forall (sub : @SOSub o) a b v n,
    sosub_find (ren_utok_sosub sub a b) (v, n)
    = match sosub_find sub (v,n) with
      | Some (sosk vs u) => Some (sosk vs (ren_utok u a b))
      | None => None
      end.
Proof.
  induction sub; introv; simpl; auto.
  destruct a; simpl;[].
  destruct s; simpl;[].
  boolvar; subst; simpl; tcsp.
Qed.

Lemma sosub_filter_ren_utok_sosub {o} :
  forall (sub : @SOSub o) a b l,
    sosub_filter (ren_utok_sosub sub a b) l
    = ren_utok_sosub (sosub_filter sub l) a b.
Proof.
  induction sub; introv; simpl; tcsp.
  destruct a; simpl.
  destruct s; simpl.
  boolvar; simpl; tcsp.
  f_equal; apply IHsub.
Qed.

Lemma ren_utok_sosub_aux_mk_abs_subst {o} :
  forall (t : @SOTerm o) sub a b,
    !LIn a (get_utokens_so t)
    -> ren_utok (sosub_aux sub t) a b
       = sosub_aux (ren_utok_sosub sub a b) t.
Proof.
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv niat; simpl in *; auto.

  - Case "sovar".
    rewrite sosub_find_ren_utok_sosub.

    remember (sosub_find sub (v, length ts)) as find.
    symmetry in Heqfind; destruct find; simpl.

    + destruct s; simpl.
      rewrite ren_utok_lsubst_aux_gen.
      rewrite ren_utok_sub_combine.
      allrw map_map; unfold compose.
      f_equal.
      f_equal.
      apply eq_maps; introv i.
      apply ind; auto.
      introv j.
      destruct niat; apply lin_flat_map.
      eexists; dands; eauto.

    + rewrite ren_utok_apply_list; simpl.
      f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      apply ind; auto.
      introv j.
      destruct niat; apply lin_flat_map.
      eexists; dands; eauto.

  - Case "soterm".
    allrw in_app_iff.
    allrw not_over_or; repnd.
    rewrite not_in_get_utokens_o_implies_ren_utok_op_same; auto.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl; f_equal.
    rewrite sosub_filter_ren_utok_sosub.
    eapply ind; eauto.

    introv j.
    destruct niat; apply lin_flat_map.
    eexists; dands; eauto.
Qed.

Lemma ren_utok_sosub_mk_abs_subst {o} :
  forall vars (bs : list (@BTerm o)) a b,
    ren_utok_sosub (mk_abs_subst vars bs) a b
    = mk_abs_subst vars (map (fun x : BTerm => ren_utok_b x a b) bs).
Proof.
  induction vars; introv; simpl; auto.
  destruct a; simpl.
  destruct bs; simpl; auto.
  destruct b0; simpl.
  boolvar; simpl; tcsp.
  f_equal; apply IHvars.
Qed.

Lemma ren_utok_sub_var_ren {o} :
  forall l1 l2 a b, @ren_utok_sub o (var_ren l1 l2) a b = var_ren l1 l2.
Proof.
  induction l1; introv; simpl; auto.
  destruct l2; simpl; tcsp.
  fold (@var_ren o l1 l2).
  rewrite IHl1; tcsp.
Qed.
Hint Rewrite @ren_utok_sub_var_ren : slow.

Lemma ren_utok_sosub_sosub_change_bvars_alpha {o} :
  forall vs (sub : @SOSub o) a b,
    ren_utok_sosub (sosub_change_bvars_alpha vs sub) a b
    = sosub_change_bvars_alpha vs (ren_utok_sosub sub a b).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; simpl.
  rewrite IHsub; f_equal; f_equal.
  destruct s; simpl.
  unfold sk_change_bvars_alpha.
  simpl.

  rewrite change_bvars_alpha_ren_utok; autorewrite with slow.
  f_equal.
  rewrite ren_utok_lsubst_aux_gen.
  f_equal.
  autorewrite with slow; auto.
Qed.

Lemma allvars_ren_utok {o} :
  forall (t : @NTerm o) a b,
    allvars (ren_utok t a b) = allvars t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; auto.
  Case "oterm".
  allrw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @allvars_ren_utok : slow.

Lemma allvars_range_sosub_ren_utok_sosub {o} :
  forall (sub : @SOSub o) a b,
    allvars_range_sosub (ren_utok_sosub sub a b)
    = allvars_range_sosub sub.
Proof.
  introv.
  unfold allvars_range_sosub.
  induction sub; introv; simpl; tcsp.
  repnd; simpl.
  rewrite IHsub.
  f_equal.
  destruct a0; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @allvars_range_sosub_ren_utok_sosub : slow.

Lemma get_utokens_so_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) l ren,
    get_utokens_so (fo_change_bvars_alpha l ren t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind|f|op bs ind] Case; introv; simpl; auto.

  - Case "sovar".
    boolvar; subst; simpl; auto.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    apply ind; auto.

  - Case "soterm".
    f_equal.
    allrw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x as [vs t]; simpl; simpl.
    eapply ind; eauto.
Qed.
Hint Rewrite @get_utokens_so_fo_change_bvars_alpha : slow.

Lemma ren_utok_mk_instance {o} :
  forall vars bs (t : @SOTerm o) a b,
    !LIn a (get_utokens_so t)
    -> ren_utok (mk_instance vars bs t) a b
       = mk_instance vars (map (fun x => ren_utok_b x a b) bs) t.
Proof.
  introv niat; unfold mk_instance.
  unfold sosub; simpl; autorewrite with slow.

  boolvar.

  - rewrite ren_utok_sosub_aux_mk_abs_subst; auto.
    rewrite ren_utok_sosub_mk_abs_subst; auto.

  - rewrite ren_utok_sosub_aux_mk_abs_subst; auto.
    rewrite ren_utok_sosub_sosub_change_bvars_alpha.
    rewrite ren_utok_sosub_mk_abs_subst.
    f_equal.
    f_equal.
    f_equal.
    rewrite <- ren_utok_sosub_mk_abs_subst.
    autorewrite with slow; auto.

  - rewrite ren_utok_sosub_aux_mk_abs_subst; auto; autorewrite with slow; auto.
    rewrite <- ren_utok_sosub_mk_abs_subst.
    auto.

  - rewrite ren_utok_sosub_aux_mk_abs_subst; auto; autorewrite with slow; auto.
    rewrite ren_utok_sosub_sosub_change_bvars_alpha.
    rewrite ren_utok_sosub_mk_abs_subst.
    f_equal.
    f_equal.
    f_equal.
    rewrite <- ren_utok_sosub_mk_abs_subst.
    autorewrite with slow; auto.
Qed.

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

              csunf comp; simpl in comp.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; ginv.

              - repeat (destruct bs; simpl in *; ginv).
                repeat (destruct bts; simpl in *; ginv).
                destruct b1 as [l1 t1].
                destruct b2 as [l2 t2].
                simpl in *; ginv.
                csunf; simpl.
                unfold apply_bterm; simpl; autorewrite with slow.

                assert (!LIn a (get_utokens_lib lib t1)) as ni1 by (eauto 5 with slow).
                assert (!LIn a (get_utokens_lib lib t2)) as ni2 by (eauto 5 with slow).
                rewrite ren_utok_subst_gen; simpl; autorewrite with slow.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1); eauto 2 with slow.
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2); eauto 2 with slow.

                boolvar; simpl; autorewrite with slow; tcsp.

              - repeat (destruct bs; simpl in *; ginv).
                repeat (destruct bts; simpl in *; ginv).
                destruct b0 as [l1 t1].
                simpl in *; ginv.
                csunf; simpl.

                unfold ren_utok_op; simpl.

                assert (!LIn a (get_utokens_lib lib t1)) as ni1 by (eauto 5 with slow).
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1); eauto 2 with slow.

              - repeat (destruct bs; simpl in *; ginv).
                repeat (destruct bts; simpl in *; ginv).
                destruct b0 as [l1 t1].
                simpl in *; ginv.
                csunf; simpl.

                unfold ren_utok_op; simpl.

                assert (!LIn a (get_utokens_lib lib t1)) as ni1 by (eauto 5 with slow).
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1); eauto 2 with slow.
            }

            {
              SSSCase "NEApply".

              apply nt_wf_eapply_iff in wf; exrepnd.
              repeat (destruct bs; simpl in *; ginv).

              csunf comp; simpl in comp.
              apply compute_step_eapply_success in comp.
              exrepnd.
              unfold nobnd in *.
              repeat (destruct l; simpl in comp0; ginv).

              repndors; exrepnd; subst; ginv.

              - apply compute_step_eapply2_success in comp1; exrepnd; GC.
                repndors; exrepnd; subst; tcsp.

                + repeat (destruct bts; simpl in *; ginv).
                  destruct b2 as [l2 t2]; ginv.
                  unfold mk_lam in *; ginv.
                  unfold subst_aux; simpl; autorewrite with slow.
                  fold_terms; unfold mk_eapply in *.
                  rewrite compute_step_eapply_lam_iscan; eauto 2 with slow.
                  unfold apply_bterm; simpl.

                  unfold nobnd, mk_lam in *.

                  assert (!LIn a (get_utokens_lib lib t2)) as ni1 by (eauto 5 with slow).
                  assert (!LIn a (get_utokens_lib lib b0)) as ni2 by (eauto 5 with slow).
                  rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow.
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2); eauto 2 with slow.
                  boolvar; simpl; autorewrite with slow; tcsp.

                + repeat (destruct bts; simpl in *; ginv).
                  unfold mk_nseq in *; ginv.
                  apply (lsubst_aux_equal_mk_nat lib _ _ _ (mk_nseq f)) in comp4; eauto 3 with slow.
                  subst; simpl in *; GC.
                  csunf; simpl.
                  unfold compute_step_eapply; simpl.
                  boolvar; try omega.
                  autorewrite with slow.
                  unfold ren_utok_op; simpl; auto.

                + repeat (destruct bts; simpl in *; ginv).
                  unfold mk_choice_seq in *; ginv.
                  apply (lsubst_aux_equal_mk_nat lib _ _ _ (mk_choice_seq name)) in comp4; eauto 3 with slow.
                  subst; simpl in *; GC.
                  csunf; simpl.
                  unfold compute_step_eapply; simpl.
                  boolvar; try omega.
                  autorewrite with slow.
                  allrw; auto.

                  rewrite not_in_get_utokens_implies_ren_utok_same; auto.
                  rw in_app_iff in nia; rw not_over_or in nia; repnd.

                  pose proof (find_cs_value_at_implies_disjoint_get_utokens_lib lib name n v0 [a]) as w.
                  allrw disjoint_singleton_l.
                  repeat (autodimp w hyp).
                  rw in_app_iff in w; rw not_over_or in w; repnd; tcsp.

                + repeat (destruct bts; simpl in *; ginv).

              - assert (!LIn a (get_utokens_lib lib b0)) as ni1 by (eauto 5 with slow).

                apply (isexc_lsubst_aux_nr_ut_sub lib _ _ b0) in comp0; eauto 3 with slow;[].
                apply isexc_implies2 in comp0; exrepnd; subst.
                unfold subst_aux; simpl.
                fold_terms; unfold mk_eapply.
                apply nt_wf_Exc in wf1; exrepnd; subst; simpl in *.
                rewrite compute_step_eapply_iscan_isexc; eauto 3 with slow.

                {
                  unfold ren_utok_op; simpl.

                  unfold nobnd in *.

                  assert (!LIn a (get_utokens_lib lib a0)) as ni2 by (eauto 5 with slow).
                  assert (!LIn a (get_utokens_lib lib b0)) as ni3 by (eauto 5 with slow).
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0); eauto 2 with slow.
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0); eauto 2 with slow.
                }

                {
                  eapply eapply_wf_def_len_implies;[|eauto].
                  allrw map_map;unfold compose.
                  apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.
                }

              - apply isnoncan_like_lsubst_aux_is_utok_sub_implies in comp3; eauto 3 with slow.
                unfold subst_aux; simpl.
                fold_terms; unfold mk_eapply.
                rewrite compute_step_eapply_iscan_isnoncan_like; eauto 3 with slow.

                {
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

                  unfold ren_utok_op at 1; simpl.

                  rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
                  rewrite map_map; unfold compose.

                  f_equal; f_equal; f_equal; f_equal; f_equal.
                  apply eq_maps; introv i.
                  destruct x0 as [l t]; simpl; f_equal.
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].

                  boolvar; simpl; autorewrite with slow; tcsp.
                }

                {
                  eapply eapply_wf_def_len_implies;[|eauto].
                  allrw map_map;unfold compose.
                  apply eq_maps; introv i; destruct x0; unfold num_bvars; simpl; auto.
                }
            }

            {
              SSSCase "NFix".

              csunf comp; simpl in comp.
              apply compute_step_fix_success in comp; repnd; subst.
              repeat (destruct bs; simpl in *; ginv).

              csunf; simpl.
              unfold ren_utok_op at 1; simpl.
              fold_terms.

              rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
              rewrite map_map; unfold compose.

              f_equal; f_equal.

              - f_equal.
                apply eq_maps; introv i.
                destruct x as [l t]; simpl; f_equal.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.

              - unfold ren_utok_op, subst_aux; simpl; fold_terms.
                f_equal; f_equal.
                apply eq_maps; introv i.
                destruct x as [l t]; simpl; f_equal.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NSpread".

              csunf comp; simpl in comp.
              apply compute_step_spread_success in comp; exrepnd; subst; simpl in *.

              repeat (destruct bts; simpl in *; ginv).
              repeat (destruct bs; simpl in *; ginv).

              destruct b1 as [l1 t1].
              destruct b2 as [l2 t2].
              destruct b3 as [l3 t3].
              ginv; simpl in *.

              csunf; simpl.
              unfold apply_bterm; simpl.
              repeat (rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow).
              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

              assert (!LIn a (get_utokens_lib lib t1)) as ni1 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t2)) as ni2 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t3)) as ni3 by (eauto 5 with slow).

              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 4 with slow].
              boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NDsup".

              csunf comp; simpl in comp.
              apply compute_step_dsup_success in comp; exrepnd; subst; simpl in *.

              repeat (destruct bts; simpl in *; ginv).
              repeat (destruct bs; simpl in *; ginv).

              destruct b1 as [l1 t1].
              destruct b2 as [l2 t2].
              destruct b3 as [l3 t3].
              ginv; simpl in *.

              csunf; simpl.
              unfold apply_bterm; simpl.
              repeat (rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow).
              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

              assert (!LIn a (get_utokens_lib lib t1)) as ni1 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t2)) as ni2 by (eauto 5 with slow).
              assert (!LIn a (get_utokens_lib lib t3)) as ni3 by (eauto 5 with slow).

              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 4 with slow].
              boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NDecide".

              csunf comp; simpl in comp.
              apply compute_step_decide_success in comp; exrepnd; subst; simpl in *.

              repeat (destruct bts; simpl in *; ginv).
              repeat (destruct bs; simpl in *; ginv).

              destruct b0 as [l0 t0].
              destruct b1 as [la ta].
              destruct b2 as [lb tb].
              ginv; simpl in *.

              csunf; simpl.
              repndors; repnd; subst; simpl in *.

              - unfold apply_bterm; simpl.
                repeat (rewrite ren_utok_subst_gen; simpl; autorewrite with slow).
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

                assert (!LIn a (get_utokens_lib lib t0)) as ni1 by (eauto 5 with slow).
                assert (!LIn a (get_utokens_lib lib ta)) as ni2 by (eauto 5 with slow).

                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t0);[|eauto 4 with slow].
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ ta);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.

              - unfold apply_bterm; simpl.
                repeat (rewrite ren_utok_subst_gen; simpl; autorewrite with slow).
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

                assert (!LIn a (get_utokens_lib lib t0)) as ni1 by (eauto 5 with slow).
                assert (!LIn a (get_utokens_lib lib tb)) as ni2 by (eauto 5 with slow).

                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t0);[|eauto 4 with slow].
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ tb);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NCbv".

              allrw @nt_wf_NCbv; exrepnd.
              unfold nobnd in *.
              repeat (destruct bs; simpl in *; ginv).

              csunf comp; simpl in comp; ginv.
              csunf; simpl.
              unfold apply_bterm; simpl.

              repeat (rewrite ren_utok_lsubst_gen; simpl; autorewrite with slow).
              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 4 with slow].
              rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
              allrw map_map; unfold compose.

              f_equal; f_equal.

              - boolvar; simpl; autorewrite with slow; tcsp.

              - f_equal; f_equal; f_equal.
                apply eq_maps; introv i.
                destruct x; simpl; f_equal.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ n);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NSleep".

              csunf comp; simpl in comp.
              apply compute_step_sleep_success in comp; exrepnd; subst; simpl in *.
              repeat (destruct bs; simpl in *; ginv).
              repeat (destruct bts; simpl in *; ginv).
            }

            {
              SSSCase "NTUni".

              csunf comp; simpl in comp.
              apply compute_step_tuni_success in comp; exrepnd; subst.
              repeat (destruct bs; simpl in *; ginv).
              repeat (destruct bts; simpl in *; ginv).

              csunf; simpl.
              unfold compute_step_tuni; simpl; boolvar; try omega.
              unfold ren_utok_op; simpl; autorewrite with slow; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; simpl in comp.
              apply compute_step_minus_success in comp; exrepnd; subst; simpl in *.
              repeat (destruct bs; simpl in *; ginv).
              repeat (destruct bts; simpl in *; ginv).
            }

            {
              SSSCase "NFresh".

              csunf comp; simpl in comp; ginv.
            }

            {
              SSSCase "NTryCatch".

              allrw @nt_wf_NTryCatch; exrepnd; subst.
              unfold nobnd in *.
              repeat (destruct bs; simpl in *; ginv).

              csunf comp; simpl in comp; ginv.
              csunf; simpl.
              unfold ren_utok_op at 1; simpl.
              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 4 with slow].
              rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
              unfold ren_utok_op; simpl.

              unfold mk_atom_eq, nobnd.
              f_equal; f_equal; f_equal; f_equal; f_equal; f_equal; f_equal.
              allrw map_map; unfold compose; simpl.
              apply eq_maps; introv i.
              destruct x as [l t]; simpl; f_equal.

              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
              boolvar; simpl; autorewrite with slow; tcsp.
            }

            {
              SSSCase "NParallel".

              csunf comp; simpl in *.
              unfold compute_step_parallel in comp; ginv.

              csunf; simpl.
              unfold compute_step_parallel; auto.
            }

            {
              SSSCase "NCompOp".

              allrw @nt_wf_NCompOp; exrepnd; subst.
              unfold nobnd in *; ginv.

              unfold subst_aux in comp; simpl in comp.
              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; subst.

              - unfold nobnd in *; ginv.

                inversion comp2; clear comp2; subst.

                match goal with
                | [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eqsub
                end.

                apply compute_step_compop_success_can_can in comp1.
                exrepnd; unfold nobnd in *; ginv.
                repeat (destruct bts; simpl in *; ginv).

                apply lsubst_aux_eq_can_nil_implies in eqsub; repndors; exrepnd; subst; simpl in *.

                + csunf; simpl.
                  dcwf h; simpl; GC.
                  unfold compute_step_comp; simpl.
                  allrw; simpl.
                  boolvar; simpl; autorewrite with slow; tcsp.

                  * repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                    rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 5 with slow].
                    auto.

                  * repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                    rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4);[|eauto 6 with slow].
                    auto.

                + csunf; simpl.
                  dcwf h; simpl; GC.

                + csunf; simpl.
                  dcwf h; simpl; GC.
                  unfold compute_step_comp; simpl; allrw; simpl.

                  boolvar; simpl; autorewrite with slow; tcsp.

                  * repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                    rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 5 with slow].
                    auto.

                  * repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                    rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4);[|eauto 6 with slow].
                    auto.

                + csunf; simpl.
                  dcwf h; simpl; GC;[].
                  boolvar; simpl; subst; tcsp;[|].

                  * unfold compute_step_comp; simpl; allrw; simpl.
                    boolvar; tcsp; subst; ginv; tcsp.

                    {
                      repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                      rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 5 with slow].
                      auto.
                    }

                    {
                      apply get_param_from_cop_pka in comp3; subst.
                      simpl in *; allrw not_over_or; tcsp.
                    }

                  * ginv; simpl in *; tcsp.
                    unfold compute_step_comp; simpl; allrw; simpl.
                    boolvar; tcsp; subst; ginv; tcsp.

                    {
                      apply get_param_from_cop_pka in comp3; subst.
                      simpl in *; allrw not_over_or; tcsp.
                    }

                    {
                      repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                      rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4);[|eauto 6 with slow].
                      auto.
                    }

              - repeat (destruct bs' as [|? bs']; simpl in *; ginv).

                apply isnoncan_like_lsubst_aux_is_utok_sub_implies in comp3; eauto 3 with slow.
                unfold subst_aux; simpl.

                rewrite compute_step_ncompop_ncanlike2;[|eauto 3 with slow];[].

                dcwf h;[].

                pose proof (ind t2 t2 []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
                pose proof (q t' v a b) as w; clear q.

                repeat (autodimp w hyp);[eauto 3 with slow|eauto 3 with slow|];[].
                unfold subst_aux in *.
                allrw; auto.

                unfold ren_utok_op at 1; simpl.

                rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
                allrw map_map; unfold compose.

                f_equal; f_equal; f_equal; f_equal; f_equal.

                {
                  apply eq_maps; introv i; destruct x as [l t]; simpl; f_equal.
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
                  boolvar; simpl; autorewrite with slow; tcsp.
                }

                {
                  f_equal.
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 5 with slow].
                  boolvar; simpl; autorewrite with slow; tcsp.
                }

                {
                  f_equal.
                  repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                  rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4);[|eauto 6 with slow].
                  boolvar; simpl; autorewrite with slow; tcsp.
                }

              - repeat (destruct bs' as [|? bs']; simpl in *; ginv).
                unfold nobnd in *; ginv.
                apply (isexc_lsubst_aux_nr_ut_sub lib _ _ t2) in comp1;[|eauto 4 with slow];[].
                apply isexc_implies2 in comp1; exrepnd; subst; simpl.
                apply nt_wf_Exc in wf3; exrepnd; subst; simpl in *.
                csunf; simpl; dcwf h; simpl.
                unfold ren_utok_op; simpl.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                unfold nobnd in *.
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0);[|eauto 5 with slow].
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 6 with slow].
                auto.
            }

            {
              SSSCase "NArithOp".

              allrw @nt_wf_NArithOp; exrepnd; subst.
              unfold nobnd in *; ginv.

              unfold subst_aux in comp; simpl in comp.
              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; subst.

              - unfold nobnd in *; ginv.

                inversion comp2; clear comp2; subst.

                match goal with
                | [ H : lsubst_aux _ _ = _ |- _ ] => rename H into eqsub
                end.

                apply compute_step_arithop_success_can_can in comp1.
                exrepnd; unfold nobnd in *; ginv.
                repeat (destruct bts; simpl in *; ginv).

                apply lsubst_aux_eq_can_nil_implies in eqsub; repndors; exrepnd; subst; simpl in *.

                + csunf; simpl.
                  dcwf h; simpl; GC.
                  allrw; simpl.
                  boolvar; simpl; autorewrite with slow; tcsp.

                + csunf; simpl.
                  dcwf h; simpl; GC.

              - repeat (destruct bs' as [|? bs']; simpl in *; ginv).

                apply isnoncan_like_lsubst_aux_is_utok_sub_implies in comp3; eauto 3 with slow.
                unfold subst_aux; simpl.

                rewrite compute_step_narithop_ncanlike2;[|eauto 3 with slow];[].

                dcwf h;[].

                pose proof (ind t2 t2 []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
                pose proof (q t' v a b) as w; clear q.

                repeat (autodimp w hyp);[eauto 3 with slow|eauto 3 with slow|];[].
                unfold subst_aux in *.
                allrw; auto.

                unfold ren_utok_op at 1; simpl.

                rewrite not_in_get_utokens_o_implies_ren_utok_op_same;[|eauto 3 with slow].
                allrw map_map; unfold compose.

                f_equal; f_equal; f_equal; f_equal; f_equal.

                apply eq_maps; introv i; destruct x as [l t]; simpl; f_equal.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
                boolvar; simpl; autorewrite with slow; tcsp.

              - repeat (destruct bs' as [|? bs']; simpl in *; ginv).
                unfold nobnd in *; ginv.
                apply (isexc_lsubst_aux_nr_ut_sub lib _ _ t2) in comp1;[|eauto 4 with slow];[].
                apply isexc_implies2 in comp1; exrepnd; subst; simpl.
                apply nt_wf_Exc in wf1; exrepnd; subst; simpl in *.
                csunf; simpl; dcwf h; simpl.
                unfold ren_utok_op; simpl.
                repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                unfold nobnd in *.
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a1);[|eauto 5 with slow].
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 6 with slow].
                auto.
            }

            {
              SSSCase "NCanTest".

              apply nt_wf_NCanTest in wf; exrepnd; ginv.
              repeat (destruct bs; simpl in *; ginv).
              unfold nobnd in *; ginv.

              csunf comp; simpl in comp.
              csunf; simpl.

              destruct (canonical_form_test_for c can2); ginv.

              - repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2);[|eauto 5 with slow].
                auto.

              - repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
                rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 5 with slow].
                auto.
            }

          + SSCase "NCan".

            csunf comp; simpl in comp.
            match goal with
            | [ H : context[on_success ?x] |- _ ] => remember x as c
            end.
            symmetry in Heqc; destruct c; simpl in *; ginv.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
            pose proof (q n v a b) as w; clear q.

            applydup @nt_wf_oterm_fst in wf.

            repeat (autodimp w hyp);[eauto 3 with slow|eauto 3 with slow|];[].
            unfold subst_aux in *; simpl in *.

            csunf; simpl.
            allrw; auto; simpl.

            unfold ren_utok_op at 1; simpl.

            allrw map_map; unfold compose.

            f_equal; f_equal; f_equal.

            apply eq_maps; introv i; destruct x as [l t]; simpl; f_equal.
            repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
            rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
            boolvar; simpl; autorewrite with slow; tcsp.

          + SSCase "Exc".

            csunf comp; simpl in comp.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst.

            * repeat (destruct bs; simpl in *; ginv).
              repeat (destruct bts; simpl in *; ginv).
              destruct b1 as [l1 t1]; simpl in *; ginv.
              destruct b2 as [l2 t2]; simpl in *; ginv.
              destruct b3 as [l3 t3]; simpl in *; ginv.
              destruct b4 as [l4 t4]; simpl in *; ginv.

              csunf; simpl.
              unfold ren_utok_op; simpl.
              repeat (rewrite ren_utok_subst_gen; simpl; autorewrite with slow).
              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t1);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t2);[|eauto 5 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t3);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t4);[|eauto 5 with slow].

              boolvar; simpl; autorewrite with slow; tcsp.

            * csunf; simpl.
              rewrite compute_step_catch_if_diff; auto;[].
              unfold ren_utok_op; simpl.

              applydup @nt_wf_oterm_fst in wf.
              apply nt_wf_Exc in wf0; exrepnd; subst; simpl in *.
              unfold nobnd in *.

              repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).

              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0);[|eauto 4 with slow].
              rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 5 with slow].
              auto.

          + SSCase "Abs".

            csunf comp; simpl in comp.
            match goal with
            | [ H : context[on_success ?x] |- _ ] => remember x as c
            end.
            symmetry in Heqc; destruct c; simpl in *; ginv.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; repeat (autodimp q hyp); eauto 2 with slow;[]; clear ind.
            pose proof (q n v a b) as w; clear q.

            applydup @nt_wf_oterm_fst in wf.

            repeat (autodimp w hyp);[eauto 3 with slow|eauto 3 with slow|];[].
            unfold subst_aux in *; simpl in *.

            csunf; simpl.
            allrw; auto; simpl.

            unfold ren_utok_op at 1; simpl.

            allrw map_map; unfold compose.

            f_equal; f_equal; f_equal.

            apply eq_maps; introv i; destruct x as [l t]; simpl; f_equal.
            repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
            rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
            boolvar; simpl; autorewrite with slow; tcsp.
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

      apply nt_wf_Exc in wf; exrepnd; subst.
      unfold nobnd in *.
      csunf comp; simpl in comp; ginv.
      unfold subst_aux; simpl.
      unfold ren_utok_op; simpl.

      repeat (rewrite ren_utok_lsubst_aux_gen; simpl; autorewrite with slow).
      rewrite (not_in_get_utokens_implies_ren_utok_same _ _ a0);[|eauto 4 with slow].
      rewrite (not_in_get_utokens_implies_ren_utok_same _ _ b0);[|eauto 4 with slow].
      auto.

    + SCase "Abs".

      csunf comp; simpl in comp.
      apply compute_step_lib_success in comp; exrepnd; subst.

      csunf; simpl.

      pose proof (found_entry_change_bs
                    abs oa2 vars rhs lib
                    (map (fun t => lsubst_bterm_aux t [(v, mk_utoken a)]) bs)
                    correct
                    (map (fun t => lsubst_bterm_aux t [(v, mk_utoken b)]) bs)) as q.
      allrw map_map; unfold compose in q.
      repeat (autodimp q hyp).
      { apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

      apply found_entry_implies_compute_step_lib_success in q.
      rewrite q; clear q.

      f_equal.
      unfold found_entry in comp0.

      apply find_entry_implies_get_utokens_subset in comp0.

      assert (!LIn a (get_utokens_so rhs)) as nia1.
      {
        introv i; apply comp0 in i.
        rw in_app_iff in nia; rw not_over_or in nia; tcsp.
      }

      assert (!LIn b (get_utokens_so rhs)) as nib1.
      {
        introv i; apply comp0 in i.
        rw in_app_iff in nib; rw not_over_or in nib; tcsp.
      }

      rewrite ren_utok_mk_instance; auto.
      f_equal.
      allrw map_map; unfold compose.
      apply eq_maps; introv i.
      destruct x as [l t]; simpl; f_equal.
      rewrite ren_utok_lsubst_aux_gen.
      rewrite (not_in_get_utokens_implies_ren_utok_same _ _ t);[|eauto 4 with slow].
      boolvar; simpl; autorewrite with slow; tcsp.
Qed.
