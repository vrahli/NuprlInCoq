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



Require Export rules_choice_util3.




Definition IP {o} (A B n : NVar) (i : nat) : @NTerm o :=
  mk_all
    (mk_uni i)
    A
    (mk_all
       (mk_fun mk_tnat (mk_uni i))
       B
       (mk_fun
          (mk_fun (mk_var A) (mk_exists mk_tnat n (mk_apply (mk_var B) (mk_var n))))
          (mk_exists mk_tnat n (mk_fun (mk_var A) (mk_apply (mk_var B) (mk_var n)))))).


(* end hide*)

(**

<<
   H |- not IP ext Ax

     By notIP

>>

 *)

Definition rule_not_IP {o}
           (A B n : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_not (IP A B n i))))
    []
    [].

Lemma rule_not_IP_true {o} :
  forall lib (A B n : NVar) (i : nat) (H : @bhyps o) (safe : safe_library lib)
         (d1 : A <> B) (d2 : B <> n) (d3 : A <> n),
    rule_true lib (rule_not_IP A B n i H).
Proof.
  unfold rule_not_IP, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  unfold IP, mk_all.
  lsubst_tac.
  rw @tequality_not.
  rw @equality_in_not.
  rw @tequality_function.

  hide_wf.
  dands; eauto 3 with slow.

  {
    introv xt eu.
    clear dependent lib.
    clear dependent lib'.
    rename lib'0 into lib.

    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    apply tequality_function; dands; eauto 3 with slow; autorewrite with slow.

    { lsubst_tac; autorewrite with slow.
      apply tequality_fun; dands; eauto 3 with slow. }

    introv xt eb.
    repeat rewrite substcv_as_substc2.
    autorewrite with slow in *.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    eapply equality_monotone in eu;[|eauto].
    clear dependent lib.
    rename lib' into lib.

    apply tequality_fun.
    dands.

    {
      autorewrite with slow in *.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_fun.
      dands.

      {
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        autorewrite with slow; eauto 3 with slow.
      }

      introv xt inh.
      hide_wf.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.
      apply equality_in_fun in eb; repnd.
      clear eb0 eb1.
      apply eb in en; eauto 3 with slow.
    }

    introv xt inh.
    clear inh.
    unfold mk_exists.
    repeat lsubstc_vars_as_mkcv.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    repeat (rewrite mkcv_product_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow;[].

    introv xt' en.
    autorewrite with slow.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].
    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.
    repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.

    apply tequality_sym.

    assert (lib_extends lib'0 lib) as xt'' by eauto 3 with slow.
    apply tequality_fun; dands; eauto 3 with slow;[].

    introv xt''' inh.

    assert (lib_extends lib'1 lib) as xt'''' by eauto 3 with slow.

    lsubst_tac.
    autorewrite with slow in *.
    apply equality_in_fun in eb; repnd.
    clear eb0 eb1.
    apply equality_sym in en.
    apply eb in en; eauto 3 with slow.
  }

  {
    apply tequality_function; dands; eauto 3 with slow; autorewrite with slow;[].

    introv xtu eu.
    repeat rewrite substcv_as_substc2.
    autorewrite with slow in *.

    repeat lsubstc_vars_as_mkcv.
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    autorewrite with slow.
    apply tequality_function.
    lsubst_tac; autorewrite with slow.
    dands;[apply tequality_fun; dands; eauto 3 with slow|];[].

    hide_wf.

    introv xt ef.
    lsubst_tac; autorewrite with slow in *.
    repeat rewrite substcv_as_substc2.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    eapply equality_monotone in eu;[|eauto].
    clear dependent lib.
    clear dependent lib'0.
    rename lib'1 into lib.

    apply tequality_fun.
    dands.

    {
      autorewrite with slow in *.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      apply tequality_fun.
      dands.

      {
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        autorewrite with slow; eauto 3 with slow.
      }

      introv xt inh.
      hide_wf.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.
      apply equality_in_fun in ef; repnd.
      clear ef0 ef1.
      apply ef in en; eauto 3 with slow.
    }

    introv xt inh.
    clear inh.
    unfold mk_exists.
    repeat lsubstc_vars_as_mkcv.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    repeat (rewrite mkcv_product_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow;[].

    introv xt' en.
    autorewrite with slow.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].
    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.
    repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.

    assert (lib_extends lib'0 lib) as xt1' by eauto 3 with slow.
    assert (lib_extends lib'1 lib) as xt2' by eauto 3 with slow.
    apply tequality_fun; dands; eauto 3 with slow;[].

    introv xt''' inh.

    assert (lib_extends lib'2 lib) as xt'''' by eauto 3 with slow.

    lsubst_tac.
    autorewrite with slow in *.
    apply equality_in_fun in ef; repnd.
    clear ef0 ef1.
    apply ef in en; eauto 3 with slow.
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
  assert (is_primitive_kind name) as isn by (eauto 3 with slow).

  pose proof (inh2 (choice_sequence_name2entry name :: lib)) as q.
  clear inh2.
  autodimp q hyp; eauto 3 with slow;[].

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
  rewrite substc_mkcv_function in q; tcsp;[].
  apply equality_in_function2 in q; repnd.

  clear q0.
  hide_wf.

  remember (choice_sequence_name2entry name :: lib) as lib'.
  assert (entry_in_library (choice_sequence_name2entry name) lib') as eil by (subst; tcsp).
  assert (safe_library lib') as safe' by (subst; eauto 3 with slow).

  clear lib w4 Heqlib' safe.
  rename lib' into lib.
  rename safe' into safe.

  pose proof (q _ (lib_extends_refl _)) as q.

  pose proof (q (exists_1_choice_fun name nvarx) (exists_1_choice_fun name nvarx)) as q.
  autodimp q hyp.

  {
    autorewrite with slow.
    lsubst_tac; autorewrite with slow; eauto 3 with slow.
  }

  repeat rewrite substcv_as_substc2 in q.
  autorewrite with slow in *.

  aeq_lsubstc_vars_not aeq.
  eapply alphaeqc_preserving_equality in q;
    [clear aeq
    |apply substc_alphaeqcv;
     apply implies_alphaeqc_substc2;exact aeq].
  eapply alphaeqc_preserving_equality in q;
    [|apply substc_alphaeqcv;
      apply substc2_fun].
  eapply alphaeqc_preserving_equality in q;
    [|apply mkcv_fun_substc].

  apply equality_in_fun in q; repnd.
  clear q0 q1.

  pose proof (q _ (lib_extends_refl _) mkc_id mkc_id) as q.
  autodimp q hyp.

  {
    aeq_lsubstc_vars_not aeq.
    eapply alphaeqc_preserving_equality;
      [clear aeq
      |apply alphaeqc_sym; apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq].
    eapply alphaeqc_preserving_equality;
      [|apply alphaeqc_sym; apply substc_alphaeqcv;
        apply substc2_fun].
    eapply alphaeqc_preserving_equality;
      [|apply alphaeqc_sym; apply mkcv_fun_substc].

    apply equality_in_fun; dands.

    {
      rewrite lsubstc_vars_mk_var_as_mkcv2;
        [|repeat rewrite dom_csub_csub_filter; intro xx;
          apply in_remove_nvars in xx; simpl in xx; repnd;
          apply in_remove_nvars in xx0; simpl in xx0; repnd;
          apply not_over_or in xx0; repnd; tcsp];[].
      autorewrite with slow; eauto 3 with slow.
    }

    {
      introv xt inh.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply type_respects_alphaeqc;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.

      unfold exists_1_choice_fun.

      eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
      eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
      autorewrite with slow.

      apply tequality_mkc_equality2_sp; dands; eauto 3 with slow;[].
      apply equality_int_nat_implies_cequivc in en.
      apply ccequivc_ext_bar_iff_ccequivc_bar in en.
      unfold ccequivc_ext_bar in en.

      split; unfold equorsq_bar;
        [eapply all_in_ex_bar_modus_ponens1;[|exact en]
        |eapply all_in_ex_bar_modus_ponens1;[|exact en] ];
        clear en; introv y en; exrepnd; spcast; right; eauto 3 with slow.
    }

    introv xt ea.

    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym; introv xt'; spcast; apply cequivc_apply_id|].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym; introv xt'; spcast; apply cequivc_apply_id|].

    eapply cequivc_preserving_equality;[eauto|].
    introv xt'; spcast.

    rewrite lsubstc_vars_mk_var_as_mkcv2;
      [|repeat rewrite dom_csub_csub_filter; intro xx;
        apply in_remove_nvars in xx; simpl in xx; repnd;
        apply in_remove_nvars in xx0; simpl in xx0; repnd;
        apply not_over_or in xx0; repnd; tcsp];[].
    autorewrite with slow.

    apply cequivc_exists_1_choice_sub; auto.
  }

  (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
  (* we don't care about the extract *)
  remember (mkc_apply
              (mkc_apply (mkc_apply f (exists_1_choice name nvarx))
                         (exists_1_choice_fun name nvarx)) mkc_id) as ext; clear Heqext.

  unfold mk_exists in q.

  aeq_lsubstc_vars_prod aeq; rewrite aeq in q; clear aeq.
  eapply alphaeqc_preserving_equality in q;
    [|apply substc_alphaeqcv;
      apply substc2_product;tcsp].
  rewrite mkcv_product_substc in q; tcsp;[].
  apply inhabited_type_if_equality in q.
  apply inhabited_product in q; repnd.
  clear q0 q1.
  exrepnd.
  rename q0 into q.
  autorewrite with slow in q.

  unfold all_in_ex_bar in q; exrepnd.

  assert (exists m restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library
                  (lib_cs name (MkChoiceSeqEntry _ (ntimes m mkc_zero) restr))
                  lib') as blib.
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
    exists n0 restr lib'; dands; auto.
  }

  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (q0 _ blib2 _ (lib_extends_refl lib')) as q0.
  cbv beta in q0.

  exrepnd.
  clear dependent t.

  aeq_lsubstc_vars_not aeq.
  eapply alphaeqc_preserving_equality in q0;
    [clear aeq
    |apply substc_alphaeqcv;
     apply implies_alphaeqc_substc2;
     apply implies_alphaeqc_substc3;exact aeq].
  eapply alphaeqc_preserving_equality in q0;
    [|apply substc_alphaeqcv;
      apply implies_alphaeqc_substc2;
      apply substc3_fun].
  eapply alphaeqc_preserving_equality in q0;
    [|apply substc_alphaeqcv;
      apply substc2_fun].
  eapply alphaeqc_preserving_equality in q0;
    [|apply mkcv_fun_substc].

  apply member_tnat_iff in q2.
  unfold all_in_ex_bar in q2; exrepnd.

  clear dependent lib.
  rename lib' into lib.
  rename bar0 into bar.
  rename safe' into safe.

  assert (exists m restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library
                  (lib_cs name (MkChoiceSeqEntry _ (ntimes m mkc_zero) restr))
                  lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.

    applydup q4 in blib0.

    apply entry_in_library_extends_implies_entry_in_library in blib1; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in blib0.
      rewrite blib0 in *; ginv. }

    pose proof (entry_extends_cs_zeros_implies lib name name0 m restr lib' entry') as q.
    repeat (autodimp q hyp);[].
    exrepnd; subst.
    exists n0 restr0 lib'; dands; auto.
  }

  clear m blib0.
  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (q1 _ blib2 _ (lib_extends_refl lib')) as q1.
  cbv beta in q1.
  exrepnd; spcast.

  eapply equality_monotone in q0;[|eauto];[].

  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  apply equality_in_fun in q0; repnd.
  clear q1 q3.

  pose proof (extend_bool_choice_sequence_zero lib name m restr0 (S k)) as q.
  repeat (autodimp q hyp);[].
  exrepnd.

  assert (k < m + S k) as ltk by lia.
  remember (m + S k) as m'; clear Heqm'.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  eapply lib_extends_preserves_computes_to_valc in q2;[|eauto];[].

  pose proof (entry_cs_zeros_implies_exists_extension_with_one lib' name m' restr0) as q.
  repeat (autodimp q hyp);[].
  exrepnd.
  assert (safe_library lib'0) as safe'' by eauto 3 with slow.
  eapply lib_extends_preserves_computes_to_valc in q2;[|eauto];[].
  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.

  pose proof (q0 _ xt) as q0.
  clear dependent lib.
  clear dependent lib'.
  rename lib'0 into lib.
  rename safe'' into safe.
  clear dependent m.
  rename m' into m.

  pose proof (q0 (mkc_pair (mkc_nat m) mkc_axiom) (mkc_pair (mkc_nat m) mkc_axiom)) as q0.
  autodimp q0 hyp.

  {
    rewrite lsubstc_vars_mk_var_as_mkcv3;
      [|repeat rewrite dom_csub_csub_filter;
        repeat rw in_remove_nvars; simpl;
        intro xx; repnd; allrw not_over_or; repnd; tcsp];[].
    autorewrite with slow.
    eapply member_exists_1_choice; eauto.
  }

  repeat lsubstc_vars_as_mkcv.
  rewrite substc3_mkcv_apply in q0.
  rewrite substc2_apply in q0.
  autorewrite with slow in q0.
  rewrite lsubstc_vars_mk_var_as_mkcv3_2 in q0;
    [|repeat rewrite dom_csub_csub_filter;
      repeat rw in_remove_nvars; simpl;
      intro xx; repnd; allrw not_over_or; repnd; tcsp];[].
  autorewrite with slow in q0.
  rewrite substc2_mk_cv_app_r in q0; tcsp;[].
  autorewrite with slow in q0.
  rewrite substc3_mk_cv_app_r_2 in q0; tcsp;[].
  rewrite substc2_mk_cv_app_r in q0; tcsp;[].
  autorewrite with slow in q0.

  unfold exists_1_choice_fun in q0.
  eapply cequivc_preserving_equality in q0;[|apply ccequivc_ext_beta].
  autorewrite with slow in q0.
  apply inhabited_type_if_equality in q0.

  eapply inhabited_type_cequivc in q0;
    [|apply implies_ccequivc_ext_equality;
      [|apply ccequivc_ext_refl|apply ccequivc_ext_refl];
      apply computes_to_valc_implies_ccequivc_ext;
      apply (implies_compute_to_valc_apply_choice_seq _ _ _ k mkc_zero);
      eauto 3 with slow;
      apply entry_in_library_implies_find_cs_some in q5;
      unfold find_cs_value_at; allrw; simpl;
      rewrite find_value_of_cs_at_is_select;
      rewrite select_app_l; autorewrite with slow; simpl; auto;
      rewrite select_ntimes; boolvar; tcsp];[].

  apply inhabited_mkc_equality in q0.
  apply equality_int_nat_implies_cequivc in q0.
  apply (all_in_ex_bar_implies_exists_lib_extends (lib_extends_refl lib)) in q0; exrepnd; spcast.
  apply cequivc_nat_implies_computes_to_valc in q1.
  apply computes_to_valc_isvalue_eq in q1; eauto 3 with slow;[].
  inversion q1.
Qed.
