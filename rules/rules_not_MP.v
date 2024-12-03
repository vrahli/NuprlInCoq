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



Require Export rules_choice_util2.



Definition MP {o} (P n : NVar) : @NTerm o :=
  mk_all
    mk_nat2bool
    P
    (mk_fun
       (mk_not (mk_all mk_tnat n (mk_not (mk_assert (mk_apply (mk_var P) (mk_var n))))))
       (mk_exists mk_tnat n (mk_assert (mk_apply (mk_var P) (mk_var n))))).


(* end hide*)

(**

<<
   H |- not MP ext Ax

     By notMP

>>

 *)

Definition rule_not_MP {o}
           (P n : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_not (MP P n))))
    []
    [].

Lemma rule_not_MP_true {o} :
  forall lib (P n : NVar) (H : @bhyps o) (safe : safe_library lib) (d : P <> n),
    rule_true lib (rule_not_MP P n H).
Proof.
  unfold rule_not_MP, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  unfold MP, mk_all.
  lsubst_tac.
  rw @tequality_not.
  rw @equality_in_not.
  rw @tequality_function.

  dands; eauto 3 with slow.

  {
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply lsubstc_mk_nat2bool|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply lsubstc_mk_nat2bool|].
    eauto 3 with slow.
  }

  {
    introv ext' eu.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_alphaeqcv;exact aeq|clear aeq].
    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_alphaeqcv;exact aeq|clear aeq].

    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_fun_substc|].

    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.

    eapply alphaeqc_preserving_equality in eu;[|apply lsubstc_mk_nat2bool];[].

    apply tequality_fun; dands.

    {
      apply tequality_not.
      apply tequality_function; dands; eauto 3 with slow.
      introv xt ea.
      repeat rewrite substcv_as_substc2.
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r;[|tcsp];[]).
      autorewrite with slow.
      apply tequality_not; eauto 3 with slow.
    }

    {
      introv xt inh.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.
      repeat (rewrite mkcv_product_substc;[|tcsp];[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r;[|tcsp];[]).
      autorewrite with slow; eauto 4 with slow.
    }
  }

  {
    unfold type.
    rw @tequality_function; dands; eauto 3 with slow.


    {
      eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply lsubstc_mk_nat2bool|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply lsubstc_mk_nat2bool|].
      eauto 3 with slow.
    }

    {
      introv ext' eu.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_alphaeqcv;exact aeq|clear aeq].
      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_alphaeqcv;exact aeq|clear aeq].

      eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_fun_substc|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_fun_substc|].

      repeat lsubstc_vars_as_mkcv.
      autorewrite with slow.
      repeat (rewrite substc_mkcv_function; tcsp;[]).
      repeat lsubstc_vars_as_mkcv.
      autorewrite with slow.

      eapply alphaeqc_preserving_equality in eu;[|apply lsubstc_mk_nat2bool];[].

      apply tequality_fun; dands.

      {
        apply tequality_not.
        apply tequality_function; dands; eauto 3 with slow.
        introv xt ea.
        repeat rewrite substcv_as_substc2.
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r;[|tcsp];[]).
        autorewrite with slow.
        apply tequality_not; eauto 3 with slow.
      }

      {
        introv xt inh.
        unfold mk_exists.
        repeat lsubstc_vars_as_mkcv.
        repeat (rewrite mkcv_product_substc;[|tcsp];[]).
        autorewrite with slow.
        apply tequality_product; dands; eauto 3 with slow;[].

        introv xt' en.
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r;[|tcsp];[]).
        autorewrite with slow; eauto 4 with slow.
      }
    }
  }

  introv ext' inh.
  rw @inhabited_function in inh; exrepnd.
  clear inh0 inh1.

  assert (safe_library lib'0) as safe' by eauto 3 with slow.

  (* WARNING *)
  clear lib lib' ext sim eqh ext' safe.
  rename lib'0 into lib.
  rename safe' into safe.


  pose proof (fresh_choice_seq_name_in_library_nat lib 1) as w; exrepnd.

  pose proof (inh2 (bool_choice_sequence_entry name :: lib)) as q.
  clear inh2.
  autodimp q hyp; eauto 3 with slow.

  pose proof (q (mkc_choice_seq name) (mkc_choice_seq name)) as q.
  autodimp q hyp.

  {
    eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply lsubstc_mk_nat2bool];[].
    apply mkc_choice_seq_in_nat2bool; eauto 3 with slow.
  }

  aeq_lsubstc_vars_not aeq.
  eapply alphaeqc_preserving_equality in q;[clear aeq|apply substc_alphaeqcv;exact aeq].
  eapply alphaeqc_preserving_equality in q;[|apply mkcv_fun_substc].

  unfold mk_exists in q.
  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow in *.
  repeat (rewrite substc_mkcv_function in q; tcsp;[]).
  repeat (rewrite mkcv_product_substc in q; tcsp;[]).
  repeat rewrite substcv_as_substc2 in q.
  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow in *.
  repeat (rewrite substc2_mk_cv_app_r in q;tcsp;[]).
  autorewrite with slow.

  apply equality_in_fun in q; repnd.
  clear q0 q1.

  remember (bool_choice_sequence_entry name :: lib) as lib'.
  assert (entry_in_library (bool_choice_sequence_entry name) lib') as eil by (subst; tcsp).
  assert (safe_library lib') as safe' by (subst; eauto 3 with slow).

  clear lib w4 Heqlib' safe.
  rename lib' into lib.
  rename safe' into safe.

  pose proof (q lib) as q; autodimp q hyp; eauto 3 with slow;[].
  pose proof (q (@mkc_axiom o) (@mkc_axiom o)) as q.

  autodimp q hyp.

  {
    apply equality_in_not; dands.

    {
      apply tequality_function; dands; eauto 3 with slow.
      introv xt ea.
      repeat rewrite substcv_as_substc2.
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r;[|tcsp];[]).
      autorewrite with slow.
      apply tequality_not; eauto 3 with slow.
      apply tequality_assert_apply_nat2bool; eauto 3 with slow.
      apply mkc_choice_seq_in_nat2bool; eauto 3 with slow.
    }

    introv ext inh.
    rw @inhabited_function in inh; exrepnd.
    clear inh0 inh1.

    eapply extends_bool_choice_sequence_entry in eil;[| |eauto]; auto;[]; exrepnd.

    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib.
    rename safe' into safe.
    pose proof (inh2 lib) as inh2; autodimp inh2 hyp; eauto 3 with slow;[].

    pose proof (inh2 (mkc_nat (length bs)) (mkc_nat (length bs))) as inh2.
    autodimp inh2 hyp; eauto 3 with slow;[].
    autorewrite with slow in *.

    apply equality_in_not in inh2; repnd; clear inh0.

    apply extends_bool_choice_sequence_entry2 in eil1; auto;[|eauto 4 with slow];[].
    exrepnd.

    pose proof (inh2 lib') as inh2; autodimp inh2 hyp; eauto 3 with slow.
    cbv beta in inh2.
    destruct inh2.

    pose proof (implies_compute_to_valc_apply_choice_seq
                  lib' (mkc_nat (length bs)) name (length bs) tt) as q.
    repeat (autodimp q hyp); eauto 3 with slow.

    {
      unfold find_cs_value_at.
      apply entry_in_library_implies_find_cs_some in eil2; rewrite eil2; simpl.
      rewrite find_value_of_cs_at_is_select.
      rewrite select_map.
      rewrite select_snoc_eq; boolvar; tcsp; try lia.
    }

    eapply inhabited_type_cequivc;
      [apply implies_ccequivc_ext_assert;
       apply ccequivc_ext_sym;
       introv xt; spcast;
       eapply lib_extends_preserves_computes_to_valc in q;[|eauto];
       apply computes_to_valc_implies_cequivc;eauto
      |];[].

    eapply inhabited_type_cequivc;
      [apply ccequivc_ext_sym;apply ccequivc_mkc_assert_tt|];[].
    eauto 3 with slow.
  }

  {
    apply inhabited_type_if_equality in q.
    apply inhabited_product in q; repnd.
    clear q0 q1; exrepnd.

    unfold all_in_ex_bar in q0; exrepnd.

    assert (exists n restr lib',
               lib_extends lib' lib
               /\ bar_lib_bar bar lib'
               /\ same_restrictions restr csc_bool
               /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n ff) restr)) lib') as blib.
    {
      pose proof (fresh_choice_seq_name_in_library_nat lib 1) as h; exrepnd.

      pose proof (bar_lib_bars bar (library2inf_def lib (simple_inf_choice_seq name0) name ff)) as q.
      autodimp q hyp;[eauto 4 with slow|];[].
      exrepnd.
      applydup q3 in eil.

      apply entry_in_library_extends_implies_entry_in_library in eil0; exrepnd.
      assert (safe_library_entry entry') as safe' by eauto 3 with slow.

      assert (name <> name0) as dname.
      { introv xx; subst name0.
        apply entry_in_library_implies_find_cs_some in eil.
        rewrite eil in *; ginv. }

      pose proof (entry_extends_bool_choice_sequence_entry_implies_def lib name name0 lib' entry' false) as q.
      repeat (autodimp q hyp);[].
      exrepnd; subst.
      exists n0 restr lib'; dands; auto.
    }

    exrepnd.
    pose proof (q1 _ blib2 _ (lib_extends_refl lib')) as q1.
    cbv beta in q1.

    exrepnd.
    clear q0.
    autorewrite with slow in *.

    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib.
    rename safe' into safe.

    apply member_tnat_implies_computes in q2.
    unfold all_in_ex_bar in q2; exrepnd.

    assert (exists n restr lib',
               lib_extends lib' lib
               /\ bar_lib_bar bar lib'
               /\ same_restrictions restr csc_bool
               /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n ff) restr)) lib') as blib.
    {
      pose proof (fresh_choice_seq_name_in_library_nat lib 1) as h; exrepnd.

      pose proof (bar_lib_bars bar (library2inf_def lib (simple_inf_choice_seq name0) name ff)) as q.
      autodimp q hyp;[eauto 4 with slow|];[].
      exrepnd.
      applydup q4 in blib0.

      apply entry_in_library_extends_implies_entry_in_library in blib1; exrepnd.
      assert (safe_library_entry entry') as safe' by eauto 3 with slow.

      assert (name <> name0) as dname.
      { introv xx; subst name0.
        apply entry_in_library_implies_find_cs_some in blib0.
        rewrite blib0 in *; ginv. }

      pose proof (entry_extends_bool_choice_sequence_entry_implies_def2 lib name name0 lib' entry' false restr n0) as q.
      repeat (autodimp q hyp);[].
      exrepnd; subst.
      exists n1 restr' lib'; dands; auto.
    }

    exrepnd.
    pose proof (q0 _ blib4 _ (lib_extends_refl lib')) as q0.
    cbv beta in q0.
    exrepnd.

    eapply member_monotone in q1;[|eauto];[].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib.
    rename safe' into safe.

    spcast.

    apply (extend_bool_choice_sequence_ff _ _ _ _ (S k)) in blib1; auto;[].
    exrepnd.
    eapply lib_extends_preserves_computes_to_valc in q2;[|eauto].
    eapply member_monotone in q1;[|eauto];[].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear dependent lib.
    rename lib' into lib.
    rename safe' into safe.

    pose proof (implies_compute_to_valc_apply_choice_seq lib a name k ff) as q.
    repeat (autodimp q hyp); eauto 3 with slow.

    {
      unfold find_cs_value_at.
      apply entry_in_library_implies_find_cs_some in blib0; allrw.
      rewrite find_value_of_cs_at_is_select; simpl.
      rewrite select_ntimes; boolvar; try lia;[]; auto.
    }

    eapply member_respects_cequivc_type in q1;
      [|apply implies_ccequivc_ext_assert;
        apply computes_to_valc_implies_ccequivc_ext; eauto].
    eapply member_respects_cequivc_type in q1;
      [|apply ccequivc_mkc_assert_ff].

    rewrite mkc_void_eq_mkc_false in q1.
    apply false_not_inhabited in q1; auto.
  }
Qed.
