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

  Authors: Vincent Rahli

*)


Require Export rules_choice_util4.
Require Export rules_choice2.
Require Export per_can.



(**

<<
   H |-  ∀(n ∈ ℕ)(a:Free). ¬ ∀(k ∈ ℕ). a(k)=n ∈ ℕ

     By CsNotConst
>>

 *)

Definition rule_not_constant {o}
           (lib   : @library o)
           (n a k : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (not_const n a k) (not_const_extract n a)))
    []
    [].

Lemma rule_not_const_true {o} :
  forall lib (n a k : NVar) (H : @bhyps o)
         (d1 : n <> a) (d2 : n <> k) (d3 : a <> k) (safe : safe_library lib),
    rule_true lib (rule_not_constant lib n a k H).
Proof.
  unfold rule_not_constant, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (not_const_extract n a) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  dands; eauto 3 with slow;[].

  repeat match goal with
         | [ H : wf_term _ |- _ ] => clear H
         | [ H : cover_vars _ _ |- _ ] => clear H
         | [ H : covered _ _ |- _ ] => clear H
         | [ H : vswf_hypotheses _ _ |- _ ] => clear H
         end.

  clear dependent s1; clear dependent s2.

  apply equality_in_function2.
  dands;[rewrite <- fold_type; apply tequality_not_const_c; auto|].

  introv xt ea.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  apply equality_in_tnat in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.
  unfold equality_of_nat in *; exrepnd; spcast.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).
  autorewrite with slow.

  apply equality_in_function2.
  dands.

  {
    apply tequality_function; dands; eauto 3 with slow.

    introv xt ef.

    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].

    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv; apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv; apply substc2_not|].
    autorewrite with slow.

    apply tequality_not.

    repeat (rewrite substc2_mkcv_function; tcsp;[]).
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    repeat (first [progress autorewrite with slow
                  |rewrite substcv_mk_cv_app_r1; try (complete (simpl; tcsp));[]
                  |rewrite substcv_mk_cv_app_r2; try (complete (simpl; tcsp));[]
                  |rewrite substcv_mk_cv_app_r3; try (complete (simpl; tcsp));[]
           ]).

    apply tequality_function; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].

    assert (safe_library lib') as safe' by eauto 3 with slow.

    clear dependent lib.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    apply equality_in_csname_implies_equality_in_nat2nat in ef; auto.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.
    apply equality_nat2nat_apply; auto.
  }

  introv xt ef.

  eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  apply equality_in_csname in ef.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ef]; clear ef; introv y ef; exrepnd; spcast.
  eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  unfold equality_of_csname in *; exrepnd; spcast.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  rewrite substcv_as_substc2.
  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym;apply substc_alphaeqcv; apply substc2_not].
  autorewrite with slow.

  repeat (rewrite substc2_mkcv_function; tcsp;[]).
  repeat (rewrite substc_mkcv_function; tcsp;[]).
  repeat (first [progress autorewrite with slow
                |rewrite substcv_mk_cv_app_r1; try (complete (simpl; tcsp));[]
                |rewrite substcv_mk_cv_app_r2; try (complete (simpl; tcsp));[]
                |rewrite substcv_mk_cv_app_r3; try (complete (simpl; tcsp));[]
         ]).

  apply equality_in_not.
  dands.

  {
    apply tequality_function; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ef2;[|eauto].
    eapply lib_extends_preserves_computes_to_valc in ef0;[|eauto].

    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow;[].
    apply equality_nat2nat_apply; eauto 3 with slow.
  }

  introv ext inh.

  eapply lib_extends_preserves_computes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ef2;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ef0;[|eauto].

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib; rename safe' into safe.

  apply inhabited_function in inh; repnd.
  clear inh0 inh1.
  exrepnd.

  pose proof (inh0 (extend_choice_sequence_with lib name (S n0))) as inh0.
  autodimp inh0 hyp; eauto 3 with slow;[].

  pose proof (inh0
                (mkc_nat (Nat.pred (size_of_cs (extend_choice_sequence_with lib name (S n0)) name)))
                (mkc_nat (Nat.pred (size_of_cs (extend_choice_sequence_with lib name (S n0)) name)))) as inh0.
  autodimp inh0 hyp; eauto 3 with slow;[].
  autorewrite with slow in *.

  apply equality_in_mkc_equality in inh0; repnd.
  clear inh0 inh2.

  eapply equality_respects_cequivc_left in inh1;
    [|apply sp_implies_ccequivc_ext_apply;
      apply computes_to_valc_implies_ccequivc_ext;
      eapply lib_extends_preserves_computes_to_valc;[|eauto];
      eauto 3 with slow].

  clear dependent a1.
  clear dependent a'0.

  pose proof (find_cs_value_at_in_extend_choice_sequence_with name (S n0) lib) as xx.
  eapply implies_compute_to_valc_apply_choice_seq in xx;
    try apply computes_to_valc_refl; eauto 3 with slow.

  eapply equality_respects_cequivc_left in inh1;
    [|apply computes_to_valc_implies_ccequivc_ext;exact xx]; clear xx.

  eapply equality_respects_cequivc_right in inh1;
    [|apply computes_to_valc_implies_ccequivc_ext;
      eapply lib_extends_preserves_computes_to_valc;[|eauto];
      eauto 3 with slow].
  apply equality_in_tnat in inh1.
  apply (non_dep_all_in_ex_bar_implies (extend_choice_sequence_with lib name (S n0))).
  eapply all_in_ex_bar_modus_ponens1;[|exact inh1]; clear inh1; introv y inh1; exrepnd; spcast.
  unfold equality_of_nat in inh1; exrepnd; spcast.
  computes_to_value_isvalue; try lia.
Qed.
