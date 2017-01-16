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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

 *)


(*Require Export continuity_defs_ceq.*)
Require Export terms5.
Require Export alphaeq3.
Require Export subst_per.


Lemma sub_find_trivial1 {o} :
  forall v1 v2 (t : @NTerm o),
    sub_find (if deq_nvar v1 v2 then [] else [(v1, t)]) v2 = None.
Proof.
  introv.
  boolvar; simpl; boolvar; tcsp.
Qed.

Ltac dis_deq_nvar :=
  match goal with
    | [ H : !(?v1 = ?v2) |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : !(?v2 = ?v1) |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : ?v1 <> ?v2 |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
    | [ H : ?v2 <> ?v1 |- context[deq_nvar ?v1 ?v2] ] => destruct (deq_nvar v1 v2); tcsp; GC;[]
  end.

Definition allvars_op {o} (t : @NTerm o) := all_vars t.
Lemma all_vars_eq_op {o} :
  forall (t : @NTerm o), free_vars t ++ bound_vars t = allvars_op t.
Proof.
  sp.
Qed.
Opaque allvars_op.

Ltac nvo :=
  match goal with
    | [ H : context[!(_ [+] _)] |- _ ] => trw_h not_over_or H
    | [ |- context[!(_ [+] _)] ] => trw not_over_or
  end.

Definition alphaeqcv {o} vs (t1 t2 : @CVTerm o vs) :=
  alpha_eq (get_cvterm vs t1) (get_cvterm vs t2).

Lemma isprog_vars_substc2 {o} :
  forall x (a : @NTerm o) v b,
    isprog b
    -> isprog_vars [x,v] a
    -> isprog_vars [x] (subst a v b).
Proof.
  introv ispb ispa.
  apply subst_preserves_isprog_vars; auto.
Qed.

Definition substc2 {o} x (u : @CTerm o) (v : NVar) (t : CVTerm [x,v]) : CVTerm [x] :=
  let (a,pa) := t in
  let (b,pb) := u in
  exist (isprog_vars [x]) (subst a v b) (isprog_vars_substc2 x a v b pb pa).

Lemma substc2_uand {o} :
  forall v x (w : @CTerm o) (t u : CVTerm [v,x]),
    alphaeqcv
      [v]
      (substc2 v w x (mkcv_uand [v,x] t u))
      (mkcv_uand [v] (substc2 v w x t) (substc2 v w x u)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).

  simpl.
  allrw @sub_filter_nil_r.
  allrw memvar_singleton.

  unfold mk_uand; simpl.

  pose proof (newvarlst_prop [x2,x1]) as nvp1.
  remember (newvarlst [x2,x1]) as v1; clear Heqv1.

  pose proof (newvarlst_prop [x2,x1,mk_var v1]) as nvp2.
  remember (newvarlst [x2,x1,mk_var v1]) as v2; clear Heqv2.

  pose proof (newvarlst_prop [lsubst_aux x2 [(x,x0)],lsubst_aux x1 [(x,x0)] ]) as nvp3.
  remember (newvarlst [lsubst_aux x2 [(x,x0)],lsubst_aux x1 [(x,x0)] ]) as v3; clear Heqv3.

  pose proof (newvarlst_prop [lsubst_aux x2 [(x,x0)],lsubst_aux x1 [(x,x0)],mk_var v3]) as nvp4.
  remember (newvarlst [lsubst_aux x2 [(x,x0)],lsubst_aux x1 [(x,x0)],mk_var v3]) as v4; clear Heqv4.

  allsimpl.
  allrw app_nil_r.
  allrw in_app_iff.
  allrw not_over_or; repnd; GC.

  allrw beq_deq.
  allrw @sub_find_trivial1.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw @sub_find_trivial1.
  allrw beq_deq.
  repeat dis_deq_nvar.
  fold_terms.

  repeat prove_alpha_eq4.
  fold_terms.

  pose proof (ex_fresh_var (v2 :: v4 :: allvars_op
        (mk_isect (mk_approx mk_axiom (mk_cbv (mk_var v1) nvarx mk_axiom)) v2
           (oterm (NCan (NCanTest CanIsaxiom))
              [nobnd (mk_var v1),
              nobnd
                (lsubst_aux x2
                   (sub_filter (if deq_nvar x v1 then [] else [(x, x0)]) [v2])),
              nobnd
                (lsubst_aux x1
                   (sub_filter (if deq_nvar x v1 then [] else [(x, x0)]) [v2]))])) ++
      allvars_op
        (mk_isect (mk_halts (mk_var v3)) v4
           (mk_isaxiom (mk_var v3) (lsubst_aux x2 [(x, x0)])
              (lsubst_aux x1 [(x, x0)]))))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v0]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  repeat prove_alpha_eq4.
  fold_terms.

  pose proof (ex_fresh_var (v0 :: allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [nobnd (mk_var v0),
            nobnd
              (lsubst_aux
                 (lsubst_aux x2
                    (sub_filter (if deq_nvar x v1 then [] else [(x, x0)])
                       [v2])) [(v1, mk_var v0)]),
            nobnd
              (lsubst_aux
                 (lsubst_aux x1
                    (sub_filter (if deq_nvar x v1 then [] else [(x, x0)])
                       [v2])) [(v1, mk_var v0)])]) ++
       allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [nobnd (mk_var v0),
            nobnd (lsubst_aux (lsubst_aux x2 [(x, x0)]) [(v3, mk_var v0)]),
            nobnd (lsubst_aux (lsubst_aux x1 [(x, x0)]) [(v3, mk_var v0)])]))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v5]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  repeat prove_alpha_eq4.

  - repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux x2 [(x, x0)]));
            [|simpl; apply disjoint_singleton_r; complete auto]).
    repeat (rw (lsubst_aux_trivial_cl_term
                  (lsubst_aux x2 (sub_filter (if deq_nvar x v1 then [] else [(x, x0)]) [v2])));
            [|simpl; apply disjoint_singleton_r;
              rw @free_vars_lsubst_aux_cl;
              [|boolvar; simpl; allrw memvar_singleton; boolvar; eauto 3 with slow];
              boolvar; simpl; allrw memvar_singleton; boolvar; simpl;
              allrw remove_nvars_nil_l;
              auto;
              allrw in_remove_nvars; sp]).

    boolvar; simpl; allrw memvar_singleton; boolvar;
    allrw @lsubst_aux_nil; eauto 3 with slow; tcsp;
    rw @lsubst_aux_trivial_cl_term; simpl; auto;
    apply disjoint_singleton_r; auto.

  - repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux x1 [(x, x0)]));
            [|simpl; apply disjoint_singleton_r; complete auto]).
    repeat (rw (lsubst_aux_trivial_cl_term
                  (lsubst_aux x1 (sub_filter (if deq_nvar x v1 then [] else [(x, x0)]) [v2])));
            [|simpl; apply disjoint_singleton_r;
              rw @free_vars_lsubst_aux_cl;
              [|boolvar; simpl; allrw memvar_singleton; boolvar; eauto 3 with slow];
              boolvar; simpl; allrw memvar_singleton; boolvar; simpl;
              allrw remove_nvars_nil_l;
              auto;
              allrw in_remove_nvars; sp]).

    boolvar; simpl; allrw memvar_singleton; boolvar;
    allrw @lsubst_aux_nil; eauto 3 with slow; tcsp;
    rw @lsubst_aux_trivial_cl_term; simpl; auto;
    apply disjoint_singleton_r; auto.
Qed.

Lemma substc_alphaeqcv {o} :
  forall (t : @CTerm o) v u1 u2,
    alphaeqcv [v] u1 u2
    -> alphaeqc (substc t v u1) (substc t v u2).
Proof.
  introv aeq.
  destruct_cterms.
  unfold alphaeqcv in aeq; unfold alphaeqc; allsimpl.
  apply lsubst_alpha_congr2; auto.
Qed.

Lemma implies_isprog_uand {o} :
  forall (t1 t2 : @NTerm o),
    isprog t1
    -> isprog t2
    -> isprog (mk_uand t1 t2).
Proof.
  introv isp1 isp2.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_uand; auto.
Qed.

Definition mkc_uand {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_uand a b) (implies_isprog_uand a b x y).

Lemma substc_mkcv_uand {o} :
  forall v (t : @CTerm o) (a b : CVTerm [v]),
    alphaeqc
      (substc t v (mkcv_uand [v] a b))
      (mkc_uand (substc t v a) (substc t v b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).

  simpl.
  allrw @sub_filter_nil_r.
  allrw memvar_singleton.

  unfold mk_uand; simpl.

  pose proof (newvarlst_prop [x1,x0]) as nvp1.
  remember (newvarlst [x1,x0]) as v1; clear Heqv1.

  pose proof (newvarlst_prop [x1,x0,mk_var v1]) as nvp2.
  remember (newvarlst [x1,x0,mk_var v1]) as v2; clear Heqv2.

  pose proof (newvarlst_prop [lsubst_aux x1 [(v,x)],lsubst_aux x0 [(v,x)] ]) as nvp3.
  remember (newvarlst [lsubst_aux x1 [(v,x)],lsubst_aux x0 [(v,x)] ]) as v3; clear Heqv3.

  pose proof (newvarlst_prop [lsubst_aux x1 [(v,x)],lsubst_aux x0 [(v,x)],mk_var v3]) as nvp4.
  remember (newvarlst [lsubst_aux x1 [(v,x)],lsubst_aux x0 [(v,x)],mk_var v3]) as v4; clear Heqv4.

  allsimpl.
  allrw app_nil_r.
  allrw in_app_iff.
  allrw not_over_or; repnd; GC.

  allrw beq_deq.
  allrw @sub_find_trivial1.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw @sub_find_trivial1.
  allrw beq_deq.
  repeat dis_deq_nvar.
  fold_terms.

  repeat prove_alpha_eq4.
  fold_terms.

  pose proof (ex_fresh_var (v2 :: v4 :: allvars_op
        (mk_isect (mk_approx mk_axiom (mk_cbv (mk_var v1) nvarx mk_axiom)) v2
           (oterm (NCan (NCanTest CanIsaxiom))
              [nobnd (mk_var v1),
              nobnd
                (lsubst_aux x1
                   (sub_filter (if deq_nvar v v1 then [] else [(v, x)]) [v2])),
              nobnd
                (lsubst_aux x0
                   (sub_filter (if deq_nvar v v1 then [] else [(v, x)]) [v2]))])) ++
      allvars_op
        (mk_isect (mk_halts (mk_var v3)) v4
           (mk_isaxiom (mk_var v3) (lsubst_aux x1 [(v, x)])
              (lsubst_aux x0 [(v, x)]))))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v0]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  repeat prove_alpha_eq4.
  fold_terms.

  pose proof (ex_fresh_var (v0 :: allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [nobnd (mk_var v0),
            nobnd
              (lsubst_aux
                 (lsubst_aux x1
                    (sub_filter (if deq_nvar v v1 then [] else [(v, x)])
                       [v2])) [(v1, mk_var v0)]),
            nobnd
              (lsubst_aux
                 (lsubst_aux x0
                    (sub_filter (if deq_nvar v v1 then [] else [(v, x)])
                       [v2])) [(v1, mk_var v0)])]) ++
       allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [nobnd (mk_var v0),
            nobnd (lsubst_aux (lsubst_aux x1 [(v, x)]) [(v3, mk_var v0)]),
            nobnd (lsubst_aux (lsubst_aux x0 [(v, x)]) [(v3, mk_var v0)])]))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v5]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  repeat prove_alpha_eq4.

  - repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux x1 [(v, x)]));
            [|simpl; apply disjoint_singleton_r; complete auto]).
    repeat (rw (lsubst_aux_trivial_cl_term
                  (lsubst_aux x1 (sub_filter (if deq_nvar v v1 then [] else [(v, x)]) [v2])));
            [|simpl; apply disjoint_singleton_r;
              rw @free_vars_lsubst_aux_cl;
              [|boolvar; simpl; allrw memvar_singleton; boolvar; eauto 3 with slow];
              boolvar; simpl; allrw memvar_singleton; boolvar; simpl;
              allrw remove_nvars_nil_l;
              auto;
              allrw in_remove_nvars; sp]).

    boolvar; simpl; allrw memvar_singleton; boolvar;
    allrw @lsubst_aux_nil; eauto 3 with slow; tcsp;
    rw @lsubst_aux_trivial_cl_term; simpl; auto;
    apply disjoint_singleton_r; auto.

  - repeat (rw (lsubst_aux_trivial_cl_term (lsubst_aux x0 [(v, x)]));
            [|simpl; apply disjoint_singleton_r; complete auto]).
    repeat (rw (lsubst_aux_trivial_cl_term
                  (lsubst_aux x0 (sub_filter (if deq_nvar v v1 then [] else [(v, x)]) [v2])));
            [|simpl; apply disjoint_singleton_r;
              rw @free_vars_lsubst_aux_cl;
              [|boolvar; simpl; allrw memvar_singleton; boolvar; eauto 3 with slow];
              boolvar; simpl; allrw memvar_singleton; boolvar; simpl;
              allrw remove_nvars_nil_l;
              auto;
              allrw in_remove_nvars; sp]).

    boolvar; simpl; allrw memvar_singleton; boolvar;
    allrw @lsubst_aux_nil; eauto 3 with slow; tcsp;
    rw @lsubst_aux_trivial_cl_term; simpl; auto;
    apply disjoint_singleton_r; auto.
Qed.

Lemma substc2_equality {o} :
  forall v x (w : @CTerm o) (a b c : CVTerm [v,x]),
    substc2 v w x (mkcv_equality [v,x] a b c)
    = mkcv_equality [v] (substc2 v w x a) (substc2 v w x b) (substc2 v w x c).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc2_member {o} :
  forall v x (w : @CTerm o) (t u : CVTerm [v,x]),
    substc2 v w x (mkcv_member [v,x] t u)
    = mkcv_member [v] (substc2 v w x t) (substc2 v w x u).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_equality_substc {o} :
  forall v a b c (t : @CTerm o),
    substc t v (mkcv_equality [v] a b c)
    = mkc_equality (substc t v a) (substc t v b) (substc t v c).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_member_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_member [v] a b)
    = mkc_member (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc2_mk_cv_app_l {o} :
  forall (u : @CTerm o) v x (t : CVTerm [x]),
    substc2 v u x (mk_cv_app_l [v] [x] t)
    = mk_cv [v] (substc u x t).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma cl_lsubst_trivial {o} :
  forall (t : @NTerm o) sub,
    disjoint (dom_sub sub) (free_vars t)
    -> cl_sub sub
    -> lsubst t sub = t.
Proof.
  introv d cl.
  apply lsubst_trivial4; auto.
  introv i.
  rw @cl_sub_eq2 in cl; apply cl in i; rw i; auto.
Qed.

Lemma cl_subst_trivial {o} :
  forall (t : @NTerm o) v u,
    !LIn v (free_vars t)
    -> closed u
    -> subst t v u = t.
Proof.
  introv d cl.
  unfold subst; apply cl_lsubst_trivial; simpl; eauto with slow.
  apply disjoint_singleton_l; auto.
Qed.

Lemma substc2_mk_cv_app_r {o} :
  forall (u : @CTerm o) v x (t : CVTerm [v]),
    v <> x
    -> substc2 v u x (mk_cv_app_r [x] [v] t) = t.
Proof.
  introv d.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
  rw @cl_subst_trivial; eauto 3 with slow.
  rw @isprog_vars_eq in i0; repnd.
  allrw subvars_eq.
  intro j; apply i1 in j; allsimpl; sp.
Qed.

Lemma substc2_mk_cv {o} :
  forall v x (u : @CTerm o) t,
    substc2 v u x (mk_cv [v,x] t) = mk_cv [v] t.
Proof.
  introv; destruct_cterms.
  apply cvterm_eq; simpl.
  rw @subst_trivial; eauto 3 with slow.
Qed.

Lemma implies_isprog_vars_isaxiom {o} :
  forall (vs : list NVar) (a b c : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs (mk_isaxiom a b c).
Proof.
  introv i1 i2 i3.
  apply isprog_vars_isaxiom; sp.
Qed.

Definition mkcv_isaxiom {p} vs (t1 t2 t3 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist
      (isprog_vars vs)
      (mk_isaxiom a b c)
      (implies_isprog_vars_isaxiom vs a b c x y z).

Lemma mkcv_isaxiom_substc {o} :
  forall v a b c (t : @CTerm o),
    substc t v (mkcv_isaxiom [v] a b c)
    = mkc_isaxiom (substc t v a) (substc t v b) (substc t v c).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma implies_isprog_vars_halts {o} :
  forall (vs : list NVar) (a : @NTerm o),
    isprog_vars vs a
    -> isprog_vars vs (mk_halts a).
Proof.
  introv i.
  apply isprog_vars_halts; sp.
Qed.

Definition mkcv_halts {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist
      (isprog_vars vs)
      (mk_halts a)
      (implies_isprog_vars_halts vs a x).

Lemma mkc_uand_aeq {o} :
  forall v (a b : @CTerm o),
    alphaeqc
      (mkc_uand a b)
      (mkc_isect
         mkc_base
         v
         (mkcv_ufun
            [v]
            (mkcv_halts [v] (mkc_var v))
            (mkcv_isaxiom [v] (mkc_var v) (mk_cv [v] a) (mk_cv [v] b)))).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  unfold mk_uand; simpl.

  pose proof (newvarlst_prop [x0,x]) as nvp1.
  remember (newvarlst [x0,x]) as v1; clear Heqv1.

  pose proof (newvarlst_prop [x0,x,mk_var v1]) as nvp2.
  remember (newvarlst [x0,x,mk_var v1]) as v2; clear Heqv2.

  allsimpl.
  allrw app_nil_r.
  allrw in_app_iff.
  allrw not_over_or; repnd; GC.

  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (v1 :: v2
                               :: newvar (mk_isaxiom (mk_var v) x0 x)
                               :: allvars_op
         (oterm (Can NIsect)
            [bterm [] (mk_halts (vterm v1)),
            bterm [v2] (mk_isaxiom (vterm v1) x0 x)]) ++
       allvars_op (mk_ufun (mk_halts (vterm v)) (mk_isaxiom (vterm v) x0 x)))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v0]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  pose proof (newvar_prop (mk_isaxiom (mk_var v) x0 x)) as nvp6.
  remember (newvar (mk_isaxiom (mk_var v) x0 x)) as v6; clear Heqv6.

  allsimpl.
  allrw app_nil_r.
  allrw in_app_iff.
  allrw remove_nvars_nil_l.
  repeat nvo.
  repnd; GC.

  boolvar; tcsp;[].
  simpl; boolvar; tcsp;[].

  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (v1 :: v2 :: v :: v6
                               :: (allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [bterm [] (vterm v0), bterm [] (lsubst_aux x0 [(v1, vterm v0)]),
            bterm [] (lsubst_aux x [(v1, vterm v0)])]) ++
       allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [bterm [] (vterm v0), bterm [] (lsubst_aux x0 [(v, vterm v0)]),
            bterm [] (lsubst_aux x [(v, vterm v0)])])))) as fv.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  repeat nvo.
  repnd.

  apply (al_bterm_aux [v3]); auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l; simpl.
    allrw in_app_iff.
    repeat nvo; tcsp. }

  repeat (simpl;
          allrw @sub_find_sub_filter_eq;
          allrw memvar_singleton;
          allrw <- @beq_var_refl;
          GC;
          fold_terms;
          allrw beq_deq;
          repeat dis_deq_nvar).

  boolvar; tcsp;[].

  repeat (rw (lsubst_aux_trivial_cl_term2 x0); eauto 3 with slow).
  repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 3 with slow).
Qed.

Lemma mkcv_halts_substc {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_halts [v] a)
    = mkc_halts (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma wf_pair_iff {p} :
  forall a b : @NTerm p, (wf_term a # wf_term b) <=> wf_term (mk_pair a b).
Proof.
  introv; split; intro i.
  apply wf_apply; sp.
  allrw @wf_term_eq.
  inversion i as [|?| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)); intros k1 k2.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  inversion k1; subst.
  inversion k2; subst; sp.
Qed.

Lemma isprog_vars_pair {p} :
  forall (f a : @NTerm p) vs,
    isprog_vars vs (mk_pair f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_pair_iff; split; sp.
Qed.

Lemma isprog_vars_pair_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_pair a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_pair; sp.
Qed.

Definition mkcv_pair {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_pair a b) (isprog_vars_pair_implies a b vs x y).

Lemma mkcv_pair_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_pair [v] a b)
    = mkc_pair (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_lam_substc {o} :
  forall v x (b : @CVTerm o [x,v]) (t : CTerm),
    x <> v
    -> substc t v (mkcv_lam [v] x b)
       = mkc_lam x (substc2 x t v b).
Proof.
  introv d.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma mkcv_ax_eq {o} :
  forall vs, @mkcv_ax o vs = mk_cv vs mkc_axiom.
Proof.
  introv.
  apply cvterm_eq; simpl; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
