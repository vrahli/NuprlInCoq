(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export cvterm.
Require Export substitution3.

Require Export continuity_axiom2.
Require Export continuity_type_aux.

Require Export cequiv_tacs.
Require Export subst_tacs.

Require Export continuity_per.

Require Export list. (* why? *)



(*
Definition of_type_int {o} lib (t : @NTerm o) :=
  {z : Z & reduces_to lib t (mk_integer z)}.

Definition of_type_int_to_val {o} lib (f : @NTerm o) :=
  forall a,
    of_type_int lib a
    -> {v : NTerm
        & reduces_to lib (mk_apply f a) v
        # isvalue_like v}.

Definition of_type_int_to_val_TO_int {o} lib (F : @NTerm o) :=
  forall f,
    of_type_int_to_val lib f
    -> {z : Z & reduces_to lib (mk_apply F f) (mk_integer z)}.
*)


Definition value_like_type {o} lib (T : @CTerm o) :=
  forall t, member lib t T -> isvaluec_like t.

Definition agree_upto_b_c {o} lib (b f g : @CTerm o) :=
  forall (t : CTerm),
    member lib (absolute_value_c t) (mkc_natk b) (* take t's absolute value *)
    -> equality lib (mkc_apply f t) (mkc_apply g t) mkc_int.

Definition continuous2 {o} lib (F : @CTerm o) :=
  forall f,
    member lib f (mkc_fun mkc_int mkc_int)
    -> {b : CTerm
        & member lib b mkc_tnat
        # forall g : CTerm,
            member lib g (mkc_fun mkc_int mkc_int)
            -> agree_upto_b_c lib b f g
            -> equality lib (mkc_apply F f) (mkc_apply F g) mkc_int}.

Definition agree_upto_b_type_c {o} (b f g : @CTerm o) : CTerm :=
  mkc_isect
    (mkc_set
       mkc_int
       nvarx
       (mkcv_member
          [nvarx]
          (absolute_value_cv [nvarx] (mkc_var nvarx))
          (mkcv_natk [nvarx] (mk_cv [nvarx] b))))
    nvarx
    (mkcv_equality
       [nvarx]
       (mkcv_apply [nvarx] (mk_cv [nvarx] f) (mkc_var nvarx))
       (mkcv_apply [nvarx] (mk_cv [nvarx] f) (mkc_var nvarx))
       (mkcv_int [nvarx])).

Definition agree_upto_b_type_cv {o} vs (b f g : @CVTerm o vs) : CVTerm vs :=
  mkcv_isect
    vs
    (mkcv_set
       vs
       (mkcv_int vs)
       nvarx
       (mkcv_member
          (nvarx :: vs)
          (absolute_value_cv (nvarx :: vs) (mk_cv_app_r vs [nvarx] (mkc_var nvarx)))
          (mkcv_natk (nvarx :: vs) (mk_cv_app_l [nvarx] vs b))))
    nvarx
    (mkcv_equality
       (nvarx :: vs)
       (mkcv_apply (nvarx :: vs) (mk_cv_app_l [nvarx] vs f) (mk_cv_app_r vs [nvarx] (mkc_var nvarx)))
       (mkcv_apply (nvarx :: vs) (mk_cv_app_l [nvarx] vs g) (mk_cv_app_r vs [nvarx] (mkc_var nvarx)))
       (mkcv_int (nvarx :: vs))).

Definition continuous_type_c {o} (F f : @CTerm o) :=
  mkc_product
    mkc_tnat
    nvarb
    (mkcv_isect
       [nvarb]
       (mkcv_fun [nvarb] (mkcv_int [nvarb]) (mkcv_int [nvarb]))
       nvarg
       (mkcv_ufun
          [nvarg, nvarb]
          (agree_upto_b_type_cv
             [nvarg,nvarb]
             (mk_cv_app_l [nvarg] [nvarb] (mkc_var nvarb))
             (mk_cv [nvarg,nvarb] f)
             (mk_cv_app_r [nvarb] [nvarg] (mkc_var nvarg)))
          (mkcv_equality
             [nvarg,nvarb]
             (mkcv_apply [nvarg,nvarb] (mk_cv [nvarg,nvarb] F) (mk_cv [nvarg,nvarb] f))
             (mkcv_apply [nvarg,nvarb] (mk_cv [nvarg,nvarb] F) (mk_cv_app_r [nvarb] [nvarg] (mkc_var nvarg)))
             (mkcv_int [nvarg,nvarb])))).

Definition continuous_type_aux {o} vb vg vi (F f : @NTerm o) :=
  mk_product
    mk_tnat
    vb
    (mk_isect
       int2int
       vg
       (mk_ufun
          (agree_upto_b_type
             vi
             (mk_var vb)
             f
             (mk_var vg))
          (mk_equality
             (mk_apply F f)
             (mk_apply F (mk_var vg))
             mk_int))).

Definition continuous_type {o} (F f : @NTerm o) :=
  match newvars3 [F,f] with
    | (vb,vg,vi) => continuous_type_aux vb vg vi F f
  end.

Lemma lsubstc_continuous_type {o} :
  forall (F f : @NTerm o)
         (w : wf_term (continuous_type F f))
         (s : CSub)
         (c : cover_vars (continuous_type F f) s),
    {wF : wf_term F
     & {wf : wf_term f
     & {cF : cover_vars F s
     & {cf : cover_vars f s
     & alphaeqc
         (lsubstc (continuous_type F f) w s c)
         (continuous_type_c (lsubstc F wF s cF) (lsubstc f wf s cf))}}}}.
Proof.
  introv.

  assert (wf_term F # wf_term f) as wf.
  { unfold continuous_type in w.
    remember (newvars3 [F,f]) as p.
    destruct p as [p vi].
    destruct p as [vb vg].
    apply newvars3_prop in Heqp.
    allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
    apply wf_product_iff in w; repnd.
    apply wf_isect_iff in w; repnd.
    apply wf_ufun in w; repnd.
    apply wf_equality_iff in w; repnd.
    apply wf_apply_iff in w3; repnd; auto. }

  destruct wf as [wF wf].
  exists wF wf.

  assert (cover_vars F s # cover_vars f s) as cov.
  { unfold continuous_type in c.
    remember (newvars3 [F,f]) as p.
    destruct p as [p vi].
    destruct p as [vb vg].
    apply newvars3_prop in Heqp.
    allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.
    apply cover_vars_product in c; repnd.
    apply cover_vars_upto_isect in c; repnd.
    apply cover_vars_upto_ufun in c; repnd.
    apply cover_vars_upto_equality in c; repnd.
    apply cover_vars_upto_apply in c3; repnd.
    allrw <- @csub_filter_app_r; allsimpl.
    apply cover_vars_upto_csub_filter_disjoint in c5;
      [|rw eqvars_prop; simpl; sp; split; sp
       |allrw disjoint_cons_r; sp].
    apply cover_vars_upto_csub_filter_disjoint in c3;
      [|rw eqvars_prop; simpl; sp; split; sp
       |allrw disjoint_cons_r; sp].
    sp. }

  destruct cov as [cF cf].
  exists cF cf.

  unfold alphaeqc; simpl.
  unfold csubst, lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_csub2sub; boolvar; tcsp;
  try (complete (destruct n; tcsp)).

  simpl.
  allrw @sub_filter_nil_r.
  allrw <- @sub_filter_app_r; simpl.
  allrw @sub_find_sub_filter; simpl; tcsp.
  repeat gen_newvar.
  fold_terms.

  allrw @lsubst_aux_sub_filter;
    try (complete (repeat get_newvar_prop; allsimpl;
                   allrw remove_nvars_nil_l; allrw app_nil_r;
                   allrw in_app_iff; allrw not_over_or; repnd;
                   allrw disjoint_cons_r; sp)).

  fold_terms.
  unfold mk_natk.
  fold (@mk_natk_aux o n1 (mk_var n)).
  allfold (@mk_tnat o).
  allfold (@int2int o).
  pose proof (newvar_not_in_free_vars (@mk_var o nvarb)) as nve; simpl in nve.
  autodimp nve hyp;[intro k; repndors; tcsp; ginv|rw nve; clear nve].
  fold (agree_upto_b_type n1 (mk_var n) (lsubst_aux f (csub2sub s)) (mk_var n0)).
  fold (agree_upto_b_type nvarx (mk_var nvarb) (lsubst_aux f (csub2sub s)) (mk_var nvarg)).
  fold (continuous_type_aux_aux n n0 n1 n5 (lsubst_aux F (csub2sub s)) (lsubst_aux f (csub2sub s))).
  unfold mk_ufun.
  gen_newvar.
  fold (continuous_type_aux_aux nvarb nvarg nvarx n6 (lsubst_aux F (csub2sub s)) (lsubst_aux f (csub2sub s))).
  clear dependent n2.
  clear dependent n3.
  clear dependent n4.

  apply alphaeq_eq.
  repeat get_newvar_prop.
  allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw in_app_iff; allsimpl; allrw not_over_or; repnd; GC.
  apply alphaeq_continuous_type_aux_aux; tcsp;
  try (complete (apply cover_vars_iff_closed_lsubst_aux; auto));
  try (complete (intro k; inversion k)).
Qed.

Tactic Notation "one_lift_lsubst_cont" constr(T) ident(name) tactic(tac) :=
  match T with
    | context [lsubstc (continuous_type ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      pose proof (lsubstc_continuous_type a b w s c) as name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
  end.

Ltac one_lift_lsubst_cont_concl :=
  match goal with
    | [ |- ?T ] =>
      let name := fresh "eq" in
      one_lift_lsubst_cont
        T
        name
        (first [ rewrite name
               | progress (apply alphaeqc_sym in name; rwal_c name)
               ]);
        clear name
  end.

Ltac one_lift_lsubst_cont_hyp H :=
  let T := type of H in
  let name := fresh "eq" in
  one_lift_lsubst_cont
    T name
    (first [ rewrite name in H
           | progress (rwal_h name H)
           ]); clear name.

Ltac lift_lsubsts_cont :=
  repeat (match goal with
            | [ H : context [lsubstc _ _ _ _ ] |- _ ] => one_lift_lsubst_cont_hyp H
            | [ |- context [lsubstc _ _ _ _ ] ] => one_lift_lsubst_cont_concl
          end).


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
