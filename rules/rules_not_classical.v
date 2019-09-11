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


Require Export rules_choice_util.



(* end hide*)

(**

<<
   H |- not (forall P, squash(P \/ ~P)) ext Ax

     By notSquashedEM

>>

 *)

Definition rule_squashed_excluded_middle {o}
           (P : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_not (mk_all (mk_uni i) P (mk_squash (mk_or (mk_var P) (mk_not (mk_var P))))))))
    []
    [].

Lemma rule_squashed_excluded_middle_true {o} :
  forall lib (P : NVar) (i : nat) (H : @bhyps o) (safe : safe_library lib),
    rule_true lib (rule_squashed_excluded_middle P i H).
Proof.
  unfold rule_squashed_excluded_middle, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  unfold mk_all.
  lsubst_tac.
  rw @tequality_not.
  rw @equality_in_not.
  rw @tequality_function.

  dands; eauto 3 with slow.

  {
    introv ext' eu.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    apply tequality_mkc_squash.
    apply tequality_mkc_or; dands; eauto 3 with slow;[].

    pose proof (lsubstc_vars_mk_not_as_mkcv (mk_var P) w4 (csub_filter s1 [P]) [P] c8) as q; exrepnd.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;exact q1
      |].
    clear q1.

    pose proof (lsubstc_vars_mk_not_as_mkcv (mk_var P) w4 (csub_filter s2 [P]) [P] c10) as q; exrepnd.
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;exact q1
      |].
    clear q1.

    autorewrite with slow.
    apply tequality_not; eauto 3 with slow.
  }

  {
    unfold type.
    rw @tequality_function; dands; eauto 3 with slow.
    introv ext' eu.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    apply tequality_mkc_squash.
    apply tequality_mkc_or; dands; eauto 3 with slow;[].

    pose proof (lsubstc_vars_mk_not_as_mkcv (mk_var P) w2 (csub_filter s1 [P]) [P] c7) as q; exrepnd.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;exact q1
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;exact q1
      |].
    clear q1.

    autorewrite with slow.
    apply tequality_not; eauto 3 with slow.
  }

  introv ext' inh.
  rw @inhabited_function in inh; exrepnd.
  clear inh0 inh1.

  assert (safe_library lib'0) as safe' by eauto 3 with slow.

  (* WARNING *)
  clear lib lib' ext sim eqh ext' safe.
  rename lib'0 into lib.
  rename safe' into safe.

  pose proof (fresh_choice_seq_name_in_library lib []) as w; exrepnd.
  assert (is_nat_or_seq_kind name) as isn.
  eauto 3 with slow.

  pose proof (inh2 (choice_sequence_name2entry name :: lib)) as q.
  clear inh2.
  autodimp q hyp; eauto 3 with slow.

  pose proof (q (exists_1_choice name nvarx) (exists_1_choice name nvarx)) as q.
  autodimp q hyp.

  {
    unfold exists_1_choice.
    apply equality_product; dands; eauto 3 with slow.
    introv ext ea.
    autorewrite with slow.

    apply equality_int_nat_implies_cequivc in ea.
    apply ccequivc_ext_bar_iff_ccequivc_bar in ea.
    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

    apply equality_mkc_equality2_sp_in_uni; dands; eauto 3 with slow.
    split; exists (trivial_bar lib'0); apply in_ext_implies_all_in_bar_trivial_bar;
      introv ext'; right; eauto 3 with slow.
  }

  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow in q.
  apply equality_in_mkc_squash in q; repnd.
  clear q0 q1.

  remember (choice_sequence_name2entry name :: lib) as lib'.
  assert (entry_in_library (choice_sequence_name2entry name) lib') as eil by (subst; tcsp).
  assert (safe_library lib') as safe' by (subst; eauto 3 with slow).

  clear lib w4 Heqlib' safe.
  rename lib' into lib.
  rename safe' into safe.

  (* XXXXXXXXXXXXX *)
  unfold inhabited_type_bar, all_in_ex_bar in q; exrepnd.

  assert (exists n restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.
    applydup q3 in eil.

    apply entry_in_library_extends_implies_entry_in_library in eil0; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in eil.
      rewrite eil in *; ginv. }

    pose proof (entry_extends_choice_sequence_name2entry_implies lib name name0 lib' entry') as q.
    repeat (autodimp q hyp);[].
    exrepnd; subst.
    exists n restr lib'; dands; auto.
  }

  exrepnd.
  pose proof (q0 _ blib2 _ (lib_extends_refl lib')) as q0.
  cbv beta in q0.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib bar eil safe blib1 blib2.
  rename lib' into lib.
  rename safe' into safe.

  unfold inhabited_type in q0; exrepnd.
  apply equality_mkc_or in q1; repnd.
  clear q0 q2.
  rename q1 into q.

  (* XXXXXXXXXXXXX *)
  unfold all_in_ex_bar in q; exrepnd.

  assert (exists n restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.
    applydup q3 in blib0.

    apply entry_in_library_extends_implies_entry_in_library in blib1; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in blib0.
      rewrite blib0 in *; ginv. }

    pose proof (entry_extends_cs_zeros_implies lib name name0 n restr lib' entry') as q.
    repeat (autodimp q hyp);[].
    exrepnd; subst.
    exists n0 restr0 lib'; dands; auto.
  }

  clear n restr blib3 blib0.
  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (q0 _ blib2 _ (lib_extends_refl lib')) as q0.
  cbv beta in q0.

  clear lib bar safe blib1 blib2.
  rename lib' into lib.
  rename safe' into safe.

  repndors; exrepnd;[|].

  {
    clear q1 q2.
    rename q0 into q.
    assert (inhabited_type lib (exists_1_choice name nvarx)) as inh.
    { exists a1; eapply equality_refl; eauto. }
    eapply not_exists_1_choice in inh; eauto.
  }

  {
    clear q1 q2.
    pose proof (lsubstc_vars_mk_not_as_mkcv (mk_var P) w6 (csub_filter s1 [P]) [P] c7) as aeq; exrepnd.
    eapply alphaeqc_preserving_equality in q0;
      [|apply substc_alphaeqcv;exact aeq1].
    clear aeq1.
    autorewrite with slow in q0.
    apply equality_in_not in q0; repnd.
    clear q1.
    eapply not_in_ext_not_inhabited_exists_1_choice; eauto.
  }
Qed.
