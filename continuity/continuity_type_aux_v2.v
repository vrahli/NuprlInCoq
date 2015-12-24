(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export csubst2.
Require Export continuity_defs.
Require Export alphaeq3.
Require Export list.  (* Why?? *)


Ltac gen_newvar :=
  match goal with
    | [ |- context[newvarlst ?l] ] => remember (newvarlst l)
    | [ |- context[newvar ?x] ] => remember (newvar x)
  end.

Lemma oneswapvar_eq1 :
  forall a b, oneswapvar a b a = b.
Proof.
  introv.
  unfold oneswapvar; boolvar; sp.
Qed.

Lemma oneswapvar_neq :
  forall a b v, v <> a -> v <> b -> oneswapvar a b v = v.
Proof.
  introv ni1 ni2.
  unfold oneswapvar; boolvar; sp.
Qed.

Lemma newvar_prop2 {p} :
  forall v (t : @NTerm p), LIn v (free_vars t) -> newvar t <> v.
Proof.
  introv i e; subst.
  apply newvar_prop in i; sp.
Qed.
Hint Resolve newvar_prop2 : slow.


Definition agree_upto_b_type_v2 {o} vi (b f g T : @NTerm o) : NTerm :=
  mk_isect
    (mk_set
       mk_int
       vi
       (mk_member (absolute_value (mk_var vi)) (mk_natk_aux vi b)))
    vi
    (mk_equality
       (mk_apply f (mk_var vi))
       (mk_apply g (mk_var vi))
       T).

Definition int2int {o} := @mk_fun o mk_int mk_int.
Definition int2T {o} (T : @NTerm o) := @mk_fun o mk_int T.

Definition continuous_type_aux_aux_v2 {o} vb vg vi vf (F f T : @NTerm o) :=
  mk_product
    mk_tnat
    vb
    (mk_isect
       (int2T T)
       vg
       (mk_isect
          (agree_upto_b_type_v2
             vi
             (mk_var vb)
             f
             (mk_var vg)
             T)
          vf
          (mk_equality
             (mk_apply F f)
             (mk_apply F (mk_var vg))
             mk_int))).

Definition allvars_op {o} (t : @NTerm o) := all_vars t.
Lemma all_vars_eq_op {o} :
  forall (t : @NTerm o), free_vars t ++ bound_vars t = allvars_op t.
Proof.
  sp.
Qed.
Opaque allvars_op.

Ltac dis_deq_nvar :=
  match goal with
    | [ H : !(?v1 = ?v2) |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : !(?v2 = ?v1) |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : ?v1 <> ?v2 |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : ?v2 <> ?v1 |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
  end.

Ltac nvo :=
  match goal with
    | [ H : context[!(_ [+] _)] |- _ ] => trw_h not_over_or H
    | [ |- context[!(_ [+] _)] ] => trw not_over_or
  end.

Lemma sub_find_trivial1 {o} :
  forall v1 v2 (t : @NTerm o),
    sub_find (if deq_nvar v1 v2 then [] else [(v1, t)]) v2 = None.
Proof.
  introv.
  boolvar; simpl; boolvar; tcsp.
Qed.

Lemma alphaeq_continuous_type_aux_aux_v2 {o} :
  forall vb1 vb2 vg1 vg2 vi1 vi2 vf1 vf2 (F f T : @NTerm o),
    closed F
    -> closed f
    -> closed T

    -> vi1 <> vb1
    -> vi1 <> vg1
    -> vg1 <> vb1
    -> vf1 <> vg1

    -> vi2 <> vb2
    -> vi2 <> vg2
    -> vg2 <> vb2
    -> vf2 <> vg2

    -> alphaeq
         (continuous_type_aux_aux_v2 vb1 vg1 vi1 vf1 F f T)
         (continuous_type_aux_aux_v2 vb2 vg2 vi2 vf2 F f T).
Proof.
  introv clF clf clT;
  introv ni1 ni2 ni3 ni4 ni5 ni6 ni7 ni8.

  apply alphaeq_eq.
  unfold continuous_type_aux_aux_v2, mk_product.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                :: (newvar T)
                                :: (@newvar o mk_void)
                                :: (@newvar o (mk_less_than (mk_var vi1) (vterm vb1)))
                                :: (@newvar o (mk_less_than (mk_var vi2) (vterm vb2)))
                                :: (allvars_op
        (oterm (Can NIsect)
           [bterm [] (int2T T),
           bterm [vg1]
             (oterm (Can NIsect)
                [bterm []
                   (agree_upto_b_type_v2 vi1 (vterm vb1) f (vterm vg1) T),
                bterm [vf1]
                  (oterm (Can NEquality)
                     [bterm [] (oterm (NCan NApply) [bterm [] F, bterm [] f]),
                     bterm []
                       (oterm (NCan NApply)
                          [bterm [] F, bterm [] (vterm vg1)]),
                     bterm [] (oterm (Can NInt) [])])])]) ++
      allvars_op
        (oterm (Can NIsect)
           [bterm [] (int2T T),
           bterm [vg2]
             (oterm (Can NIsect)
                [bterm []
                   (agree_upto_b_type_v2 vi2 (vterm vb2) f (vterm vg2) T),
                bterm [vf2]
                  (oterm (Can NEquality)
                     [bterm [] (oterm (NCan NApply) [bterm [] F, bterm [] f]),
                     bterm []
                       (oterm (NCan NApply)
                          [bterm [] F, bterm [] (vterm vg2)]),
                     bterm [] (oterm (Can NInt) [])])])])))) as fv.
  exrepnd.
  allsimpl.
  rw in_app_iff in fv0.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v]); simpl; auto;[|].
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; allrw in_app_iff; sp. }

  allrw @sub_filter_nil_r.
  allrw memvar_singleton.

  pose proof (newvar_prop T) as nv1.
  remember (newvar T) as v1; clear Heqv1.
  pose proof (@newvar_prop o mk_void) as nv2.
  remember (newvar mk_void) as v2; clear Heqv2.
  pose proof (@newvar_prop o (mk_less_than (mk_var vi1) (vterm vb1))) as nv3.
  remember (newvar (mk_less_than (mk_var vi1) (vterm vb1))) as v3; clear Heqv3.
  pose proof (@newvar_prop o (mk_less_than (mk_var vi2) (vterm vb2))) as nv4.
  remember (newvar (mk_less_than (mk_var vi2) (vterm vb2))) as v4; clear Heqv4.
  allsimpl; allrw not_over_or; repnd.

  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[]).

  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                :: v1 :: v2 :: v3 :: v4 :: v
                                :: (allvars_op
        (mk_isect
           (mk_isect
              (mk_set mk_int vi1
                 (mk_member (absolute_value (mk_var vi1))
                    (mk_set mk_int vi1
                       (mk_product
                          (mk_function (mk_less_than (mk_var vi1) mk_zero) v2
                             mk_void) v3
                          (mk_less_than (mk_var vi1) (mk_var v)))))) vi1
              (mk_equality (mk_apply f (mk_var vi1))
                 (mk_apply (mk_var vg1) (mk_var vi1)) T)) vf1
           (mk_equality (mk_apply F f) (mk_apply F (mk_var vg1)) mk_int)) ++
      allvars_op
        (mk_isect
           (mk_isect
              (mk_set mk_int vi2
                 (mk_member (absolute_value (mk_var vi2))
                    (mk_set mk_int vi2
                       (mk_product
                          (mk_function (mk_less_than (mk_var vi2) mk_zero) v2
                             mk_void) v4
                          (mk_less_than (mk_var vi2) (mk_var v)))))) vi2
              (mk_equality (mk_apply f (mk_var vi2))
                 (mk_apply (mk_var vg2) (mk_var vi2)) T)) vf2
           (mk_equality (mk_apply F f) (mk_apply F (mk_var vg2)) mk_int))))) as fvs.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v0]); simpl; auto;[|].
  { unfold all_vars; allrw @all_vars_eq_op.
    fold_terms.
    apply disjoint_singleton_l; allrw in_app_iff; sp. }

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_eq.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[]).

  repeat prove_alpha_eq4.

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                  :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                  :: allvars_op
                          (mk_member (absolute_value (mk_var vi2))
                             (mk_set mk_int vi2
                                (mk_product
                                   (mk_function
                                      (mk_less_than (mk_var vi2) mk_zero) v2
                                      mk_void) v4
                                   (mk_less_than (mk_var vi2) (@mk_var o v))))) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      simpl.
      allrw in_app_iff.
      repeat nvo.
      allrw app_nil_r.
      simpl.
      allrw in_remove_nvars.
      simpl.
      allrw in_remove_nvars.
      simpl.
      repeat nvo.
      dands; tcsp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    simpl.

    unfold mk_member, mk_equality.
    repeat prove_alpha_eq4.

    pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                    :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx :: v5
                                    :: (allvars_op
             (mk_product
                (mk_function (mk_less_than (mk_var vi2) mk_zero) v2 mk_void)
                v4 (mk_less_than (mk_var vi2) (@mk_var o v)))) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v6]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      simpl.
      allrw app_nil_r.
      allrw in_app_iff.
      repeat nvo.
      simpl.
      allrw in_remove_nvars.
      simpl.
      repeat nvo.
      dands; tcsp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    unfold mk_product, mk_function, mk_less.
    allrw @sub_find_trivial1.

    repeat prove_alpha_eq4.

    pose proof (ex_fresh_var (v3 :: v4 :: v6 :: v :: nvarx
                                 :: [] )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v7]); simpl; auto;[|].
    { unfold all_vars; simpl.
      apply disjoint_singleton_l.
      simpl; sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    unfold mk_less.
    repeat prove_alpha_eq4.
  }

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                    :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                    :: (allvars_op
        (mk_equality (mk_apply f (mk_var vi1))
           (mk_apply (mk_var v0) (mk_var vi1)) T) ++
      allvars_op
        (mk_equality (mk_apply f (mk_var vi2))
           (mk_apply (mk_var v0) (mk_var vi2)) T)) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      allrw in_app_iff.
      sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
  }

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                    :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                    :: (allvars_op
         (mk_equality (mk_apply F f) (mk_apply F (mk_var v0)) mk_int) ++
       allvars_op
         (mk_equality (mk_apply F f) (mk_apply F (mk_var v0)) mk_int)) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      allrw in_app_iff.
      sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
  }
Qed.

Definition int2Tv {o} v (T : @NTerm o) := @mk_function o mk_int v T.

Definition continuous_type_aux_aux_v2v {o} vb vt vg vi vf (F f T : @NTerm o) :=
  mk_product
    mk_tnat
    vb
    (mk_isect
       (int2Tv vt T)
       vg
       (mk_isect
          (agree_upto_b_type_v2
             vi
             (mk_var vb)
             f
             (mk_var vg)
             T)
          vf
          (mk_equality
             (mk_apply F f)
             (mk_apply F (mk_var vg))
             mk_int))).

Lemma alphaeq_continuous_type_aux_aux_v2v {o} :
  forall vb1 vb2 vt1 vt2 vg1 vg2 vi1 vi2 vf1 vf2 (F f T : @NTerm o),
    closed F
    -> closed f
    -> closed T

    -> vi1 <> vb1
    -> vi1 <> vg1
    -> vg1 <> vb1
    -> vf1 <> vg1

    -> vi2 <> vb2
    -> vi2 <> vg2
    -> vg2 <> vb2
    -> vf2 <> vg2

    -> alphaeq
         (continuous_type_aux_aux_v2v vb1 vt1 vg1 vi1 vf1 F f T)
         (continuous_type_aux_aux_v2v vb2 vt2 vg2 vi2 vf2 F f T).
Proof.
  introv clF clf clT;
  introv ni1 ni2 ni3 ni4 ni5 ni6 ni7 ni8.

  apply alphaeq_eq.
  unfold continuous_type_aux_aux_v2v, mk_product.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                :: (newvar T)
                                :: (@newvar o mk_void)
                                :: (@newvar o (mk_less_than (mk_var vi1) (vterm vb1)))
                                :: (@newvar o (mk_less_than (mk_var vi2) (vterm vb2)))
                                :: (allvars_op
        (oterm (Can NIsect)
           [bterm [] (int2Tv vt1 T),
           bterm [vg1]
             (oterm (Can NIsect)
                [bterm []
                   (agree_upto_b_type_v2 vi1 (vterm vb1) f (vterm vg1) T),
                bterm [vf1]
                  (oterm (Can NEquality)
                     [bterm [] (oterm (NCan NApply) [bterm [] F, bterm [] f]),
                     bterm []
                       (oterm (NCan NApply)
                          [bterm [] F, bterm [] (vterm vg1)]),
                     bterm [] (oterm (Can NInt) [])])])]) ++
      allvars_op
        (oterm (Can NIsect)
           [bterm [] (int2Tv vt2 T),
           bterm [vg2]
             (oterm (Can NIsect)
                [bterm []
                   (agree_upto_b_type_v2 vi2 (vterm vb2) f (vterm vg2) T),
                bterm [vf2]
                  (oterm (Can NEquality)
                     [bterm [] (oterm (NCan NApply) [bterm [] F, bterm [] f]),
                     bterm []
                       (oterm (NCan NApply)
                          [bterm [] F, bterm [] (vterm vg2)]),
                     bterm [] (oterm (Can NInt) [])])])])))) as fv.
  exrepnd.
  allsimpl.
  rw in_app_iff in fv0.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v]); simpl; auto;[|].
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; allrw in_app_iff; sp.
  }

  allrw @sub_filter_nil_r.
  allrw memvar_singleton.

  pose proof (newvar_prop T) as nv1.
  remember (newvar T) as v1; clear Heqv1.
  pose proof (@newvar_prop o mk_void) as nv2.
  remember (newvar mk_void) as v2; clear Heqv2.
  pose proof (@newvar_prop o (mk_less_than (mk_var vi1) (vterm vb1))) as nv3.
  remember (newvar (mk_less_than (mk_var vi1) (vterm vb1))) as v3; clear Heqv3.
  pose proof (@newvar_prop o (mk_less_than (mk_var vi2) (vterm vb2))) as nv4.
  remember (newvar (mk_less_than (mk_var vi2) (vterm vb2))) as v4; clear Heqv4.
  allsimpl; allrw not_over_or; repnd.

  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[]).

  repeat prove_alpha_eq4.

  { unfold mk_function.
    repeat prove_alpha_eq4;[].
    pose proof (ex_fresh_var (vt1 :: vt2 :: all_vars T)) as fvs; exrepnd.
    allsimpl; allrw not_over_or; repnd.
    apply (al_bterm_aux [v0]); simpl; auto;[|].
    { apply disjoint_singleton_l.
      rw in_app_iff; sp. }
    repeat (rw @lsubst_aux_trivial_cl_term2; auto).
  }

  pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                :: v1 :: v2 :: v3 :: v4 :: v
                                :: (allvars_op
        (mk_isect
           (mk_isect
              (mk_set mk_int vi1
                 (mk_member (absolute_value (mk_var vi1))
                    (mk_set mk_int vi1
                       (mk_product
                          (mk_function (mk_less_than (mk_var vi1) mk_zero) v2
                             mk_void) v3
                          (mk_less_than (mk_var vi1) (mk_var v)))))) vi1
              (mk_equality (mk_apply f (mk_var vi1))
                 (mk_apply (mk_var vg1) (mk_var vi1)) T)) vf1
           (mk_equality (mk_apply F f) (mk_apply F (mk_var vg1)) mk_int)) ++
      allvars_op
        (mk_isect
           (mk_isect
              (mk_set mk_int vi2
                 (mk_member (absolute_value (mk_var vi2))
                    (mk_set mk_int vi2
                       (mk_product
                          (mk_function (mk_less_than (mk_var vi2) mk_zero) v2
                             mk_void) v4
                          (mk_less_than (mk_var vi2) (mk_var v)))))) vi2
              (mk_equality (mk_apply f (mk_var vi2))
                 (mk_apply (mk_var vg2) (mk_var vi2)) T)) vf2
           (mk_equality (mk_apply F f) (mk_apply F (mk_var vg2)) mk_int))))) as fvs.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  allrw not_over_or; repnd.

  apply (al_bterm_aux [v0]); simpl; auto;[|].
  { unfold all_vars; allrw @all_vars_eq_op.
    fold_terms.
    apply disjoint_singleton_l; allrw in_app_iff; sp. }

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_eq.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  simpl.
  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  GC.
  fold_terms.
  allrw beq_deq.
  repeat dis_deq_nvar.

  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow;[]).

  repeat prove_alpha_eq4.

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                  :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                  :: allvars_op
                          (mk_member (absolute_value (mk_var vi2))
                             (mk_set mk_int vi2
                                (mk_product
                                   (mk_function
                                      (mk_less_than (mk_var vi2) mk_zero) v2
                                      mk_void) v4
                                   (mk_less_than (mk_var vi2) (@mk_var o v))))) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      simpl.
      allrw in_app_iff.
      repeat nvo.
      allrw app_nil_r.
      simpl.
      allrw in_remove_nvars.
      simpl.
      allrw in_remove_nvars.
      simpl.
      repeat nvo.
      dands; tcsp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    simpl.

    unfold mk_member, mk_equality.
    repeat prove_alpha_eq4.

    pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                  :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx :: v5
                                  :: (allvars_op
             (mk_product
                (mk_function (mk_less_than (mk_var vi2) mk_zero) v2 mk_void)
                v4 (mk_less_than (mk_var vi2) (@mk_var o v)))) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v6]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      simpl.
      allrw app_nil_r.
      allrw in_app_iff.
      repeat nvo.
      simpl.
      allrw in_remove_nvars.
      simpl.
      repeat nvo.
      dands; tcsp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.

    unfold mk_product, mk_function, mk_less.
    allrw @sub_find_trivial1.

    repeat prove_alpha_eq4.

    pose proof (ex_fresh_var (v3 :: v4 :: v6 :: v :: nvarx
                                 :: [] )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v7]); simpl; auto;[|].
    { unfold all_vars; simpl.
      apply disjoint_singleton_l.
      simpl; sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    unfold mk_less.
    repeat prove_alpha_eq4.
  }

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                  :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                  :: (allvars_op
        (mk_equality (mk_apply f (mk_var vi1))
           (mk_apply (mk_var v0) (mk_var vi1)) T) ++
      allvars_op
        (mk_equality (mk_apply f (mk_var vi2))
           (mk_apply (mk_var v0) (mk_var vi2)) T)) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      allrw in_app_iff.
      sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
  }

  { pose proof (ex_fresh_var (vb1 :: vb2 :: vt1 :: vt2 :: vg1 :: vg2 :: vi1 :: vi2 :: vf1 :: vf2
                                  :: v1 :: v2 :: v3 :: v4 :: v :: v0 :: nvarx
                                  :: (allvars_op
         (mk_equality (mk_apply F f) (mk_apply F (mk_var v0)) mk_int) ++
       allvars_op
         (mk_equality (mk_apply F f) (mk_apply F (mk_var v0)) mk_int)) )) as fvs.
    exrepnd.
    allsimpl.
    allrw in_app_iff.
    repeat nvo.
    repnd.

    apply (al_bterm_aux [v5]); simpl; auto;[|].
    { unfold all_vars; allrw @all_vars_eq_op.
      fold_terms.
      apply disjoint_singleton_l.
      allrw in_app_iff.
      sp. }

    allrw @sub_filter_nil_r.
    allrw @sub_find_sub_filter_eq.

    simpl.
    allrw memvar_singleton.
    allrw <- @beq_var_refl.
    GC.
    fold_terms.
    allrw beq_deq.
    repeat dis_deq_nvar.
    allrw @sub_find_trivial1.

    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
  }
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
