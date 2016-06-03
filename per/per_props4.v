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


Require Export cover.
Require Export cvterm4.
Require Export cequiv_seq_util.
Require Export per_props_nat2.
Require Export per_props_nat3.
Require Export continuity_defs_ceq.
Require Export per_props_equality.
Require Export list. (* !!WTF *)


Lemma inhabited_squash {o} :
  forall lib (t : @CTerm o),
    inhabited_type lib (mkc_squash t) <=> inhabited_type lib t.
Proof.
  introv.
  split; intro k; allunfold @inhabited_type; exrepnd.
  - allrw @equality_in_mkc_squash; repnd.
    allunfold @inhabited_type; exrepnd.
    exists t1; auto.
  - exists (@mkc_axiom o).
    apply equality_in_mkc_squash; dands; spcast; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow).
    exists t0; auto.
Qed.

Lemma inhabited_product {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_product A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {a : CTerm
        , member lib a A
        # inhabited_type lib (substc a v B)}).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_product in k0; exrepnd; dands; tcsp.
    apply equality_refl in k5.
    apply equality_refl in k0.
    exists a1; dands; auto.
    exists b1; auto.

  - exrepnd.
    allunfold @inhabited_type; exrepnd.
    exists (mkc_pair a t).
    rw @equality_in_product; dands; tcsp.
    exists a a t t; dands; auto; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma inhabited_exists {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_exists A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {a : CTerm
        , member lib a A
        # inhabited_type lib (substc a v B)}).
Proof.
  introv.
  unfold mkc_exists.
  rw @inhabited_product; auto.
Qed.

Lemma nat_in_nat {o} :
  forall (lib : @library o) n,
    member lib (mkc_nat n) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat.
  exists n; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma member_tnat_implies_computes {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    -> {k : nat & computes_to_valc lib t (mkc_nat k)}.
Proof.
  introv mem.
  apply equality_in_tnat in mem.
  apply equality_of_nat_imp_tt in mem.
  unfold equality_of_nat_tt in mem; exrepnd.
  exists k; auto.
Qed.

Lemma member_tnat_iff {o} :
  forall lib (t : @CTerm o),
    member lib t mkc_tnat
    <=> {k : nat & computes_to_valc lib t (mkc_nat k)}.
Proof.
  introv; split; introv mem.
  - apply member_tnat_implies_computes; auto.
  - apply equality_in_tnat.
    exrepnd.
    exists k; dands; spcast; auto.
Qed.

Lemma reduces_toc_eapply_nseq {o} :
  forall lib s (t u : @CTerm o),
    reduces_toc lib t u
    -> reduces_toc lib (mkc_eapply (mkc_nseq s) t) (mkc_eapply (mkc_nseq s) u).
Proof.
  introv r.
  destruct_cterms.
  allunfold @reduces_toc; allsimpl.
  apply implies_eapply_red_aux; eauto 3 with slow.
Qed.

Lemma reduces_toc_trans {o} :
  forall lib (a b c : @CTerm o),
    reduces_toc lib a b
    -> reduces_toc lib b c
    -> reduces_toc lib a c.
Proof.
  introv r1 r2.
  destruct_cterms.
  allunfold @reduces_toc; allsimpl.
  eapply reduces_to_trans; eauto.
Qed.

Lemma member_respects_reduces_toc {o} :
  forall lib (t1 t2 T : @CTerm o),
  reduces_toc lib t1 t2
  -> member lib t2 T
  -> member lib t1 T.
Proof.
  introv r m.
  apply reduces_toc_implies_cequivc in r.
  apply cequivc_sym in r.
  eapply equality_respects_cequivc in r;[|exact m].
  apply equality_sym in r; apply equality_refl in r; auto.
Qed.

Lemma member_respects_cequivc {o} :
  forall lib (t1 t2 T : @CTerm o),
  cequivc lib t1 t2
  -> member lib t1 T
  -> member lib t2 T.
Proof.
  introv c m.
  eapply equality_respects_cequivc in c;[|exact m].
  apply equality_sym in c; apply equality_refl in c; auto.
Qed.

Lemma member_respects_cequivc_type {o} :
  forall lib (t T1 T2 : @CTerm o),
  cequivc lib T1 T2
  -> member lib t T1
  -> member lib t T2.
Proof.
  introv c m.
  eapply cequivc_preserving_equality; eauto.
Qed.

Lemma substcv_as_substc2 {o} :
  forall x (t : @CTerm o) v (u : CVTerm [x,v]),
    substcv [x] t v u = substc2 x t v u.
Proof.
  introv.
  destruct_cterms; simpl.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma equality_nat2nat_apply {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2nat
    -> equality lib a b mkc_tnat
    -> equality lib (mkc_apply f a) (mkc_apply g b) mkc_tnat.
Proof.
  introv eqf eqn.
  unfold nat2nat in eqf.
  apply equality_in_fun in eqf; repnd.
  apply eqf in eqn; auto.
Qed.

Lemma equality_int_nat_implies_cequivc {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    -> cequivc lib a b.
Proof.
  introv eqn.
  apply equality_in_tnat in eqn.
  apply equality_of_nat_imp_tt in eqn.
  unfold equality_of_nat_tt in eqn; exrepnd.
  eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact eqn1|].
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma member_nseq_nat2nat {o} :
  forall (lib : @library o) s,
    member lib (mkc_nseq s) nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply equality_in_fun; dands; tcsp; eauto 3 with slow.
  introv eqn.
  applydup @equality_int_nat_implies_cequivc in eqn.
  apply equality_respects_cequivc.
  { apply implies_cequivc_apply; auto. }
  clear eqn0.
  apply equality_refl in eqn.
  apply member_tnat_iff in eqn; exrepnd.

  eapply member_respects_cequivc.
  { apply cequivc_sym.
    apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact eqn0].
  }

  apply (member_respects_cequivc _ (mkc_nat (s k))).
  { apply cequivc_sym.
    apply reduces_toc_implies_cequivc.
    unfold reduces_toc; simpl.
    eapply reduces_to_if_split2.
    { csunf; simpl; auto. }
    apply reduces_to_if_step.
    csunf; simpl; dcwf h; simpl.
    boolvar; try omega.
    allrw @Znat.Nat2Z.id; auto.
  }
  apply nat_in_nat.
Qed.

Lemma cover_vars_upto_squash {o} :
  forall (T : @NTerm o) s vs,
    cover_vars_upto (mk_squash T) s vs
    <=> cover_vars_upto T s vs.
Proof.
  introv.
  unfold cover_vars_upto.
  simpl.
  allrw app_nil_r; allrw remove_nvars_nil_l; sp.
Qed.

Lemma lsubstc_vars_mk_squash_as_mkcv {o} :
  forall (T : @NTerm o) w s vs c,
    {w' : wf_term T
     & {c' : cover_vars_upto T s vs
     & lsubstc_vars (mk_squash T) w s vs c
       = mkcv_squash vs (lsubstc_vars T w' s vs c')}}.
Proof.
  introv.
  dup w as w'.
  rw @wf_squash in w'.
  dup c as c'.
  rw @cover_vars_upto_squash in c'.

  exists w' c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma cover_vars_upto_apply2 {o} :
  forall (vs : list NVar) (a b c : @NTerm o) (sub : CSub),
    cover_vars_upto (mk_apply2 a b c) sub vs
    <=> (cover_vars_upto a sub vs
         # cover_vars_upto b sub vs
         # cover_vars_upto c sub vs).
Proof.
  introv.
  unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  split; sp.
Qed.

Lemma lsubstc_vars_mk_cequiv_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & lsubstc_vars (mk_cequiv t1 t2) w s vs c
       = mkcv_cequiv
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2) }}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_cequiv_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_cequiv in c'; repnd.

  exists w'0 w' c'0 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubstc_vars_mk_approx_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & lsubstc_vars (mk_approx t1 t2) w s vs c
       = mkcv_approx
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2) }}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_cequiv_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_approx in c'; repnd.

  exists w'0 w' c'0 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubstc_vars_mk_apply_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & lsubstc_vars (mk_apply t1 t2) w s vs c
       = mkcv_apply
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2) }}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_apply_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_apply in c'; repnd.

  exists w'0 w' c'0 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubstc_vars_mk_apply2_as_mkcv {o} :
  forall (t1 t2 t3 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {w3 : wf_term t3
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & {c3 : cover_vars_upto t3 s vs
     & lsubstc_vars (mk_apply2 t1 t2 t3) w s vs c
       = mkcv_apply2
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2)
           (lsubstc_vars t3 w3 s vs c3) }}}}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_apply2_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_apply2 in c'; repnd.

  exists w'0 w'1 w' c'0 c'1 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubstc_vars_mk_product_as_mkcv {o} :
  forall (t1 : @NTerm o) (v : NVar) (t2 : NTerm) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 (csub_filter s [v]) (v :: vs)
     & lsubstc_vars (mk_product t1 v t2) w s vs c
       = mkcv_product
           vs
           (lsubstc_vars t1 w1 s vs c1)
           v
           (lsubstc_vars t2 w2 (csub_filter s [v]) (v :: vs) c2)}}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_product_iff in w'; repnd.
  exists w'0 w'.

  dup c as c'.
  rw @cover_vars_upto_product in c'; repnd.
  exists c'0 c'.

  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst; simpl.
  fold_terms.
  allrw @sub_filter_nil_r; auto.
  rw @sub_filter_csub2sub; auto.
Qed.

Lemma lsubstc_vars_mk_function_as_mkcv {o} :
  forall (t1 : @NTerm o) (v : NVar) (t2 : NTerm) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 (csub_filter s [v]) (v :: vs)
     & lsubstc_vars (mk_function t1 v t2) w s vs c
       = mkcv_function
           vs
           (lsubstc_vars t1 w1 s vs c1)
           v
           (lsubstc_vars t2 w2 (csub_filter s [v]) (v :: vs) c2)}}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_function_iff in w'; repnd.
  exists w'0 w'.

  dup c as c'.
  rw @cover_vars_upto_function in c'; repnd.
  exists c'0 c'.

  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst; simpl.
  fold_terms.
  allrw @sub_filter_nil_r; auto.
  rw @sub_filter_csub2sub; auto.
Qed.

Lemma lsubstc_vars_mk_var_as_mkcv1 {o} :
  forall v (w : @wf_term o (mk_var v)) s vs c,
    !LIn v (dom_csub s)
    -> lsubstc_vars (mk_var v) w s (v :: vs) c
       = mk_cv_app_r vs [v] (mkc_var v).
Proof.
  introv ni.
  apply cvterm_eq; simpl.
  apply csubst_var_not_in; auto.
Qed.

Lemma lsubstc_vars_mk_var_as_mkcv2 {o} :
  forall v v' (w : @wf_term o (mk_var v)) s c,
    !LIn v (dom_csub s)
    -> lsubstc_vars (mk_var v) w s [v',v] c
       = mk_cv_app_l [v'] [v] (mkc_var v).
Proof.
  introv ni.
  apply cvterm_eq; simpl.
  apply csubst_var_not_in; auto.
Qed.

Lemma lsubstc_vars_as_mk_cv {o} :
  forall (t : @NTerm o) w s vs c,
    disjoint vs (free_vars t)
    -> {c' : cover_vars t s
        & lsubstc_vars t w s vs c
          = mk_cv vs (lsubstc t w s c')}.
Proof.
  introv disj.
  assert (cover_vars t s) as cv.
  { apply cover_vars_eq.
    unfold cover_vars_upto in c.
    allrw subvars_prop; introv i.
    applydup c in i.
    allrw in_app_iff; repndors; tcsp.
    apply disj in i0; sp. }
  exists cv.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma lsubstc_vars_mk_lam_as_mkcv {o} :
  forall (v : NVar) (t : @NTerm o) w s vs c,
    {w1 : wf_term t
     & {c1 : cover_vars_upto t (csub_filter s [v]) (v :: vs)
     & lsubstc_vars (mk_lam v t) w s vs c
       = mkcv_lam
           vs
           v
           (lsubstc_vars t w1 (csub_filter s [v]) (v :: vs) c1)}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_lam_iff in w'; repnd.
  exists w'.

  dup c as c'.
  rw @cover_vars_upto_lam in c'; repnd.
  exists c'.

  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst; simpl.
  fold_terms.
  allrw @sub_filter_nil_r; auto.
  rw @sub_filter_csub2sub; auto.
Qed.

Lemma lsubstc_vars_mk_int_eq_as_mkcv {o} :
  forall (t1 t2 t3 t4 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {w3 : wf_term t3
     & {w4 : wf_term t4
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & {c3 : cover_vars_upto t3 s vs
     & {c4 : cover_vars_upto t4 s vs
     & lsubstc_vars (mk_int_eq t1 t2 t3 t4) w s vs c
       = mkcv_inteq
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2)
           (lsubstc_vars t3 w3 s vs c3)
           (lsubstc_vars t4 w4 s vs c4) }}}}}}}}.
Proof.
  introv.

  dup w as w'.
  rw <- @wf_int_eq_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_int_eq in c'; repnd.

  exists w'0 w'1 w'2 w' c'0 c'1 c'2 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Ltac lsubstc_vars_as_mkcv :=
  match goal with

    (* ====== on hypotheses ====== *)

    | [ H : context[lsubstc_vars mk_tnat ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      pose proof (lsubstc_vars_mk_tnat_as_mkcv w s vs c) as hyp;
        rewrite hyp in H;
        clear hyp

    | [ H : context[lsubstc_vars (mk_squash ?t) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf := fresh "w" in
      let cv := fresh "c" in
      pose proof (lsubstc_vars_mk_squash_as_mkcv t w s vs c) as hyp;
        destruct hyp as [wf hyp];
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_cequiv ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_cequiv_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_approx ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_approx_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_apply ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_apply_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_apply2 ?t1 ?t2 ?t3) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      pose proof (lsubstc_vars_mk_apply2_as_mkcv t1 t2 t3 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_int_eq ?t1 ?t2 ?t3 ?t4) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let wf4 := fresh "w4" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      let cv4 := fresh "c4" in
      pose proof (lsubstc_vars_mk_int_eq_as_mkcv t1 t2 t3 t4 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [wf4 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        destruct hyp as [cv4 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_lam ?v ?t) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      pose proof (lsubstc_vars_mk_lam_as_mkcv v t w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [cv1 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_function ?t1 ?v ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_function_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_var ?v) ?w ?s (?v :: ?vs) ?c] |- _ ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv1 v w s vs c ni) as hyp;
        rewrite hyp in H;
        clear ni hyp

    | [ H : context[lsubstc_vars (mk_var ?v) ?w ?s [?v1, ?v] ?c] |- _ ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv2 v v1 w s c ni) as hyp;
        rewrite hyp in H;
        clear ni hyp

    | [ H : context[lsubstc_vars ?t ?w ?s ?vs ?c] |- _ ] =>
      let ni  := fresh "ni" in
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      assert (disjoint vs (free_vars t)) as ni
          by (repeat (trw disjoint_cons_l);
              simpl; tcsp);
        pose proof (lsubstc_vars_as_mk_cv t w s vs c ni) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear ni hyp;
        proof_irr

    | [ H : context[lsubstc ?t ?w (csub_filter ?s ?vs) ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      pose proof (lsubstc_csub_filter_eq t w s vs c) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    (* ====== on conclusion ====== *)

    | [ |- context[lsubstc_vars mk_tnat ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      pose proof (lsubstc_vars_mk_tnat_as_mkcv w s vs c) as hyp;
        rewrite hyp;
        clear hyp

    | [ |- context[lsubstc_vars (mk_squash ?t) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf := fresh "w" in
      let cv := fresh "c" in
      pose proof (lsubstc_vars_mk_squash_as_mkcv t w s vs c) as hyp;
        destruct hyp as [wf hyp];
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_cequiv ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_cequiv_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_approx ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_approx_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_apply ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_apply_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_apply2 ?t1 ?t2 ?t3) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      pose proof (lsubstc_vars_mk_apply2_as_mkcv t1 t2 t3 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_int_eq ?t1 ?t2 ?t3 ?t4) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let wf4 := fresh "w4" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      let cv4 := fresh "c4" in
      pose proof (lsubstc_vars_mk_int_eq_as_mkcv t1 t2 t3 t4 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [wf4 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        destruct hyp as [cv4 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_lam ?v ?t) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      pose proof (lsubstc_vars_mk_lam_as_mkcv v t w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [cv1 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_function ?t1 ?v ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_function_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_var ?v) ?w ?s (?v :: ?vs) ?c] ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv1 v w s vs c ni) as hyp;
        rewrite hyp;
        clear ni hyp

    | [ |- context[lsubstc_vars (mk_var ?v) ?w ?s [?v1, ?v] ?c] ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv2 v v1 w s c ni) as hyp;
        rewrite hyp;
        clear ni hyp

    | [ |- context[lsubstc_vars ?t ?w ?s ?vs ?c] ] =>
      let ni  := fresh "ni" in
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      assert (disjoint vs (free_vars t)) as ni
          by (repeat (trw disjoint_cons_l);
              simpl; tcsp);
        pose proof (lsubstc_vars_as_mk_cv t w s vs c ni) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear ni hyp;
        proof_irr

    | [ |- context[lsubstc ?t ?w (csub_filter ?s ?vs) ?c] ] =>
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      pose proof (lsubstc_csub_filter_eq t w s vs c) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear hyp;
        proof_irr
  end.

Lemma alphaeqc_mkc_product1 {o} :
  forall (a b : @CTerm o) v t,
    alphaeqc a b
    -> alphaeqc (mkc_product a v t) (mkc_product b v t).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  unfold mk_product.
  repeat prove_alpha_eq4.
Qed.

Lemma tequality_mkc_member_implies_sp {o} :
  forall lib (a b A B : @CTerm o),
    tequality lib (mkc_member a A) (mkc_member b B)
    -> member lib a A
    -> equality lib a b A.
Proof.
  introv teq mem.
  allrw @tequality_mkc_member_sp; repnd.
  repndors; tcsp; spcast.
  eapply equality_respects_cequivc_right;[exact teq|]; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
