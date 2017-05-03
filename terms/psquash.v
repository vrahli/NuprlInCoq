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


(*Require Export computation8.*)
Require Export substitution3.
Require Export cvterm.
Require Export alphaeq3.


Definition mk_psquash_per {o} v1 v2 (t : @NTerm o) :=
  mk_lam v1
         (mk_lam v2
                 (mk_uand (mk_member (mk_var v1) t)
                          (mk_member (mk_var v2) t))).

Definition mk_psquash {o} (t : @NTerm o) :=
  match newvars2 [t] with
    | (v1,v2) => mk_pertype (mk_psquash_per v1 v2 t)
  end.

Definition mkc_psquash_per {o} v1 v2 (t : @CTerm o) :=
  mkc_lam
    v1
    (mkcv_lam
       [v1] v2
       (mkcv_uand
          [v2,v1]
          (mkcv_member [v2,v1] (mk_cv_app_l [v2] [v1] (mkc_var v1)) (mk_cv [v2,v1] t))
          (mkcv_member [v2,v1] (mk_cv_app_r [v1] [v2] (mkc_var v2)) (mk_cv [v2,v1] t)))).

Lemma wf_mk_psquash {o} :
  forall (t : @NTerm o),
    wf_term (mk_psquash t) <=> wf_term t.
Proof.
  introv.
  unfold mk_psquash.
  remember (newvars2 [t]) as v; destruct v.
  rw <- @wf_pertype_iff.
  unfold mk_psquash_per.
  allrw <- @wf_lam_iff.
  rw @wf_uand.
  allrw <- @wf_member_iff.
  split; intro k; repnd; dands; tcsp.
Qed.

Lemma cover_vars_isaxiom {o} :
  forall (a b c : @NTerm o) (s : CSub) vs,
    cover_vars_upto (mk_isaxiom a b c) s vs
    <=> (cover_vars_upto a s vs
         # cover_vars_upto b s vs
         # cover_vars_upto c s vs).
Proof.
  introv.
  unfold mk_isaxiom, mk_can_test.
  unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_eqvars {o} :
  forall (t : @NTerm o) s vs1 vs2,
    eqvars vs1 vs2
    -> (cover_vars_upto t s vs1
        <=> cover_vars_upto t s vs2).
Proof.
  introv eqvs.
  allunfold @cover_vars_upto.
  allrw subvars_eq.
  split; introv cv i; apply cv in i; allrw in_app_iff; repndors; tcsp;
  rw eqvars_prop in eqvs; apply eqvs in i; sp.
Qed.

Lemma cover_vars_upto_uand {o} :
  forall (A B : @NTerm o) (s : CSub) vs,
    cover_vars_upto (mk_uand A B) s vs <=> (cover_vars_upto A s vs # cover_vars_upto B s vs).
Proof.
  introv.
  unfold mk_uand.
  remember (newvars2 [A,B]) as v; destruct v.
  allrw @cover_vars_upto_isect.
  rw @cover_vars_upto_base_iff.
  rw @cover_vars_isaxiom.
  allrw @cover_vars_upto_var; simpl.
  allrw <- @csub_filter_app_r; simpl.
  apply newvars2_prop2 in Heqv; allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cover_vars_upto_csub_filter_app
                A s [n, n0] [n, n0] vs) as h1.
  allrw disjoint_cons_r.
  repeat (autodimp h1 hyp); allsimpl.
  pose proof (cover_vars_upto_eqvars
                A (csub_filter s [n, n0])
                (n :: n0 :: vs)
                (n0 :: n :: vs)) as e1.
  autodimp e1 hyp.
  { rw eqvars_prop; simpl; introv; split; sp. }
  rw <- e1; rw h1; clear h1 e1.

  pose proof (cover_vars_upto_csub_filter_app
                B s [n, n0] [n, n0] vs) as h1.
  allrw disjoint_cons_r.
  repeat (autodimp h1 hyp); allsimpl.
  pose proof (cover_vars_upto_eqvars
                B (csub_filter s [n, n0])
                (n :: n0 :: vs)
                (n0 :: n :: vs)) as e1.
  autodimp e1 hyp.
  { rw eqvars_prop; simpl; introv; split; sp. }
  rw <- e1; rw h1; clear h1 e1.

  split; intro k; repnd; dands; tcsp.
Qed.

Lemma cover_vars_upto_member {o} :
  forall (vs : list NVar) (t T : @NTerm o) (sub : CSub),
    cover_vars_upto (mk_member t T) sub vs
    <=> (cover_vars_upto t sub vs # cover_vars_upto T sub vs).
Proof.
  introv.
  unfold mk_member.
  rw @cover_vars_upto_equality.
  split; sp.
Qed.

Lemma cover_vars_psquash {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_psquash t) s <=> cover_vars t s.
Proof.
  introv.
  unfold mk_psquash.
  remember (newvars2 [t]) as v; destruct v.
  rw @cover_vars_pertype.
  unfold mk_psquash_per.
  rw @cover_vars_lam.
  rw @cover_vars_upto_lam.
  rw @cover_vars_upto_uand.
  allrw @cover_vars_upto_member.
  allrw @cover_vars_upto_var.
  simpl.

  allrw <- @csub_filter_app_r; simpl.
  apply newvars2_prop2 in Heqv; allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cover_vars_upto_csub_filter_disjoint
                t s [n, n0] [n, n0]) as h1.
  allrw disjoint_cons_r.
  repeat (autodimp h1 hyp); allsimpl.
  pose proof (cover_vars_upto_eqvars
                t (csub_filter s [n, n0])
                [n,n0] [n0,n]) as e1.
  autodimp e1 hyp.
  { rw eqvars_prop; simpl; introv; split; sp. }
  rw <- e1; rw h1; clear h1 e1.

  split; intro k; repnd; dands; tcsp.
Qed.

Lemma implies_memvar_false :
  forall (v : NVar) (vars : list NVar),
    !LIn v vars -> memvar v vars = false.
Proof.
  introv ni.
  apply assert_memvar_false; auto.
Qed.

Lemma implies_memvar_true :
  forall (v : NVar) (vars : list NVar),
    LIn v vars -> memvar v vars = true.
Proof.
  introv ni.
  remember (memvar v vars) as b; destruct b; auto; symmetry in Heqb.
  apply assert_memvar_false in Heqb; auto.
Qed.

Definition allvars_op {o} (t : @NTerm o) := all_vars t.
Lemma all_vars_eq_op {o} :
  forall (t : @NTerm o), free_vars t ++ bound_vars t = allvars_op t.
Proof.
  sp.
Qed.
Opaque allvars_op.

Lemma lsubstc_mk_psquash_ex {o} :
  forall (t : @NTerm o) w s c,
    {w' : wf_term t
     & {c' : cover_vars t s
     & alphaeqc
         (lsubstc (mk_psquash t) w s c)
         (mkc_pertype (mkc_psquash_per nvarx nvary (lsubstc t w' s c')))}}.
Proof.
  introv.

  dup w as w'.
  rw @wf_mk_psquash in w'.
  exists w'.

  dup c as c'.
  rw @cover_vars_psquash in c'.
  exists c'.

  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow.
  simpl; fold_terms.
  allrw @sub_filter_nil_r.

  pose proof (newvarlst_prop [t]) as nvp1.
  remember (newvarlst [t]) as v1; clear Heqv1.
  pose proof (newvarlst_prop [t,mk_var v1]) as nvp2.
  remember (newvarlst [t, mk_var v1]) as v2; clear Heqv2.
  pose proof (newvarlst_prop [mk_member (mk_var v1) t, mk_member (mk_var v2) t]) as nvp3.
  remember (newvarlst [mk_member (mk_var v1) t, mk_member (mk_var v2) t]) as v3; clear Heqv3.
  pose proof (newvarlst_prop [mk_member (mk_var v1) t, mk_member (mk_var v2) t, mk_var v3]) as nvp4.
  remember (newvarlst [mk_member (mk_var v1) t, mk_member (mk_var v2) t, mk_var v3]) as v4; clear Heqv4.

  allsimpl.
  allrw app_nil_r; allrw remove_nvars_nil_l.
  repeat (allrw in_app_iff; allsimpl).
  allrw not_over_or; repnd; GC.

  allrw <- @sub_filter_app_r; allsimpl.
  allrw @sub_find_sub_filter_eq; allsimpl.

  repeat (rw implies_memvar_true;[|simpl; complete sp]).

  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (v1 :: v2
                               :: v3
                               :: v4
                               :: nvarx
                               :: nvary
                               :: (newvarlst [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
                              mk_member (vterm nvary) (lsubst t (csub2sub s))])
                               :: (newvarlst
              [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
               mk_member (vterm nvary) (lsubst t (csub2sub s)),
               mk_var (newvarlst
              [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
               mk_member (vterm nvary) (lsubst t (csub2sub s))])])
                               :: (allvars_op
        (oterm (Can NLambda)
           [bterm [v2]
              (oterm (Can NIsect)
                 [bterm [] (oterm (Can NBase) []),
                 bterm [v3]
                   (oterm (Can NIsect)
                      [bterm []
                         (oterm (Can NApprox)
                            [bterm [] mk_axiom,
                            bterm [] (mk_cbv (vterm v3) nvarx mk_axiom)]),
                      bterm [v4]
                        (oterm (NCan (NCanTest CanIsaxiom))
                           [bterm [] (vterm v3),
                           bterm []
                             (mk_member (vterm v1)
                                (lsubst_aux t
                                   (sub_filter (csub2sub s) [v1, v2, v3, v4]))),
                           bterm []
                             (mk_member (vterm v2)
                                (lsubst_aux t
                                   (sub_filter (csub2sub s) [v1, v2, v3, v4])))])])])]) ++
      allvars_op
        (oterm (Can NLambda)
           [bterm [nvary]
              (mk_uand (mk_member (vterm nvarx) (lsubst t (csub2sub s)))
                 (mk_member (vterm nvary) (lsubst t (csub2sub s))))])))) as fv.
  exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.

  apply (al_bterm_aux [v]); simpl; auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff; sp. }

  allrw <- @sub_filter_app_r; allsimpl.

  pose proof (newvarlst_prop [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
                              mk_member (vterm nvary) (lsubst t (csub2sub s))]) as nvp5.
  remember (newvarlst
              [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
               mk_member (vterm nvary) (lsubst t (csub2sub s))]) as v5.
  clear Heqv5.

  pose proof (newvarlst_prop [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
                              mk_member (vterm nvary) (lsubst t (csub2sub s)),
                              mk_var v5]) as nvp26.
  remember (newvarlst
              [mk_member (vterm nvarx) (lsubst t (csub2sub s)),
               mk_member (vterm nvary) (lsubst t (csub2sub s)),
               mk_var v5]) as v6.
  clear Heqv6.

  allsimpl.
  allrw app_nil_r; allrw remove_nvars_nil_l.
  repeat (allrw in_app_iff; allsimpl).
  allrw not_over_or; repnd.

  allsimpl.
  allrw memvar_singleton.
  boolvar; tcsp.
  Opaque memvar beq_var.
  allsimpl.
  allrw memvar_singleton.
  boolvar; tcsp.
  allrw not_over_or; repnd; GC.
  allsimpl.
  boolvar; tcsp; ginv.
  fold_terms.

  repeat (prove_alpha_eq4).
  fold_terms.

  pose proof (ex_fresh_var (v :: v1
                              :: v2
                              :: v3
                              :: v4
                              :: v5
                              :: v6
                              :: nvarx
                              :: nvary
                              :: (allvars_op
         (mk_isect (oterm (Can NBase) []) v3
            (mk_isect
               (mk_approx mk_axiom (mk_cbv (mk_var v3) nvarx mk_axiom)) v4
               (oterm (NCan (NCanTest CanIsaxiom))
                  [nobnd (mk_var v3),
                  nobnd
                    (mk_member (mk_var v)
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, mk_var v)])),
                  nobnd
                    (mk_member (mk_var v2)
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, mk_var v)]))]))) ++
       allvars_op
         (mk_isect (oterm (Can NBase) []) v5
            (mk_isect
               (mk_approx mk_axiom (mk_cbv (mk_var v5) nvarx mk_axiom)) v6
               (oterm (NCan (NCanTest CanIsaxiom))
                  [nobnd (mk_var v5),
                  nobnd
                    (mk_member (mk_var v)
                       (lsubst_aux (lsubst t (csub2sub s))
                          [(nvarx, mk_var v)])),
                  nobnd
                    (mk_member (mk_var nvary)
                       (lsubst_aux (lsubst t (csub2sub s))
                          [(nvarx, mk_var v)]))]))))))
    as fv'.
  exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.

  apply (al_bterm_aux [v0]); allsimpl; fold_terms; auto.
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff; sp. }

  simpl.
  allrw <- @sub_filter_app_r; allsimpl.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton; allsimpl.
  boolvar; tcsp.
  simpl.
  allrw memvar_singleton; simpl.
  boolvar; tcsp.
  fold_terms.

  repeat (prove_alpha_eq4).
  fold_terms.

  pose proof (ex_fresh_var (v :: v0
                              :: v1
                              :: v2
                              :: v3
                              :: v4
                              :: v5
                              :: v6
                              :: nvarx
                              :: nvary
                              :: (allvars_op
         (mk_isect (mk_approx mk_axiom (mk_cbv (mk_var v3) nvarx mk_axiom))
            v4
            (oterm (NCan (NCanTest CanIsaxiom))
               [nobnd (mk_var v3),
               nobnd
                 (mk_member (mk_var v)
                    (lsubst_aux
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, mk_var v)]) [(v2, mk_var v0)])),
               nobnd
                 (mk_member (mk_var v0)
                    (lsubst_aux
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, mk_var v)]) [(v2, mk_var v0)]))])) ++
       allvars_op
         (mk_isect (mk_approx mk_axiom (mk_cbv (mk_var v5) nvarx mk_axiom))
            v6
            (oterm (NCan (NCanTest CanIsaxiom))
               [nobnd (mk_var v5),
               nobnd
                 (mk_member (mk_var v)
                    (lsubst_aux
                       (lsubst_aux (lsubst t (csub2sub s))
                          [(nvarx, mk_var v)]) [(nvary, mk_var v0)])),
               nobnd
                 (mk_member (mk_var v0)
                    (lsubst_aux
                       (lsubst_aux (lsubst t (csub2sub s))
                          [(nvarx, mk_var v)]) [(nvary, mk_var v0)]))])))))
    as fv''.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  rw not_over_or in fv''0.
  repnd.

  apply (al_bterm_aux [v7]); try (complete (simpl; auto)).
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff.
    sp. }

  simpl.
  allrw <- @sub_filter_app_r; allsimpl.
  allrw @sub_filter_nil_r.
  allrw memvar_singleton; allsimpl.
  boolvar; tcsp.
  simpl.

  boolvar; tcsp.
  fold_terms.
  fold_terms.

  repeat (prove_alpha_eq4).

  pose proof (ex_fresh_var (v :: v0
                              :: v1
                              :: v2
                              :: v3
                              :: v4
                              :: v5
                              :: v6
                              :: v7
                              :: nvarx
                              :: nvary
                              :: (allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [bterm [] (vterm v7),
            bterm []
              (mk_member (vterm v)
                 (lsubst_aux
                    (lsubst_aux
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, vterm v)]) [(v2, vterm v0)])
                    [(v3, vterm v7)])),
            bterm []
              (mk_member (vterm v0)
                 (lsubst_aux
                    (lsubst_aux
                       (lsubst_aux
                          (lsubst_aux t
                             (sub_filter (csub2sub s) [v1, v2, v3, v4]))
                          [(v1, vterm v)]) [(v2, vterm v0)])
                    [(v3, vterm v7)]))]) ++
       allvars_op
         (oterm (NCan (NCanTest CanIsaxiom))
            [bterm [] (vterm v7),
            bterm []
              (mk_member (vterm v)
                 (lsubst_aux
                    (lsubst_aux
                       (lsubst_aux (lsubst t (csub2sub s)) [(nvarx, vterm v)])
                       [(nvary, vterm v0)]) [(v5, vterm v7)])),
            bterm []
              (mk_member (vterm v0)
                 (lsubst_aux
                    (lsubst_aux
                       (lsubst_aux (lsubst t (csub2sub s)) [(nvarx, vterm v)])
                       [(nvary, vterm v0)]) [(v5, vterm v7)]))]))))
    as fv'''.
  exrepnd.
  allsimpl.
  allrw in_app_iff.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  rw not_over_or in fv'''0.
  repnd.

  apply (al_bterm_aux [v8]); try (complete (simpl; auto));[|].
  { unfold all_vars; allrw @all_vars_eq_op.
    apply disjoint_singleton_l.
    rw in_app_iff.
    sp. }

  Transparent memvar.
  simpl.
  boolvar; tcsp.

  repeat (prove_alpha_eq4);[|].

  { applydup @cover_vars_iff_closed_lsubst_aux in c'.
    rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
    rw @lsubst_aux_sub_filter;[|repeat (rw disjoint_cons_r); dands; complete auto].
    repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto;[]).
    rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto. }

  { applydup @cover_vars_iff_closed_lsubst_aux in c'.
    rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
    rw @lsubst_aux_sub_filter;[|repeat (rw disjoint_cons_r); dands; complete auto].
    repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto;[]).
    rw (lsubst_aux_trivial_cl_term2 (lsubst_aux t (csub2sub s))); auto. }
Qed.

Definition mkc_psquash {o} (t : @CTerm o) :=
  mkc_pertype (mkc_psquash_per nvarx nvary t).

Lemma lsubstc_mk_psquash_ex2 {o} :
  forall (t : @NTerm o) w s c,
    {w' : wf_term t
     & {c' : cover_vars t s
     & alphaeqc (lsubstc (mk_psquash t) w s c)
                (mkc_psquash (lsubstc t w' s c')) }}.
Proof.
  introv.
  apply lsubstc_mk_psquash_ex.
Qed.
