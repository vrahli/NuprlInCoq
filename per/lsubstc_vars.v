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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export csubst6.
Require Export cvterm4.
Require Export cover.
Require Export subst_tacs2.
Require Export natk.
Require Export cequiv_seq_util.
Require Export per_props_squash.
Require Export sequents.


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

Ltac propagate_true_step :=
  match goal with
  | [ |- context[?x = ?x] ] => trw true_eq_same
  | [ |- context[True [+] _] ] => trw or_true_l
  | [ |- context[_ [+] True] ] => trw or_true_r
  | [ |- context[True # _] ] => trw and_true_l
  | [ |- context[_ # True] ] => trw and_true_r
  | [ |- context[False [+] _] ] => trw or_false_l
  | [ |- context[_ [+] False] ] => trw or_false_r
  end.

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
              repeat (trw not_over_or);
              simpl;
              repeat (rewrite app_nil_r);
              repeat (trw in_remove_nvars);
              simpl;
              repeat propagate_true_step;
              dands; auto;
              intro xxx; repnd; repndors; auto;
              GC; match xxx with | _ => idtac end;
              tcsp);
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
      let xxx := fresh "xxx" in
      assert (disjoint vs (free_vars t)) as ni
          by (repeat (trw disjoint_cons_l);
              repeat (trw not_over_or);
              simpl;
              repeat (rewrite app_nil_r);
              repeat (trw in_remove_nvars);
              simpl;
              repeat propagate_true_step;
              dands; auto;
              intro xxx; repnd; repndors; auto;
              GC; match xxx with | _ => idtac end;
              tcsp);
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
