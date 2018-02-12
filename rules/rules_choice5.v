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


Require Export rules_choice2.
Require Export per_can.


Definition ils2 {o} (a b : NVar) : @NTerm o :=
  mk_function
    (mk_csname 0)
    a
    (mk_function
       (mk_csname 0)
       b
       (mk_or
          (mk_equality (mk_var a) (mk_var b) (mk_csname 0))
          (mk_not (mk_equality (mk_var a) (mk_var b) (mk_csname 0))))).

Definition ils2c {o} (a b : NVar) : @CTerm o :=
  mkc_function
    (mkc_csname 0)
    a
    (mkcv_function
       _
       (mkcv_csname _ 0)
       b
       (mkcv_or
          _
          (mkcv_equality _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)) (mkcv_csname _ 0))
          (mkcv_not _ (mkcv_equality _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)) (mkcv_csname _ 0))))).

Lemma lsubstc_ils2_eq {o} :
  forall a b (w : @wf_term o (ils2 a b)) s c,
    lsubstc (ils2 a b) w s c = ils2c a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ils2_eq : slow.

Lemma substc2_mkcv_csname {o} :
  forall b (t : @CTerm o) a n,
    substc2 b t a (mkcv_csname ([b,a]) n)
    = mkcv_csname _ n.
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl; tcsp.
Qed.
Hint Rewrite @substc2_mkcv_csname : slow.



(**

<<
   H |- ∀ (a b:Free(0)). a = b in Free(0) ∨ !(a = b in Free(0))

     By iLS2
>>

 *)


Definition rule_ils2 {o}
           (lib : @library o)
           (a b : NVar)
           (H  : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ils2 a b) (ls2_extract a b)))
    []
    [].

Lemma rule_ils2_true {o} :
  forall lib (a b : NVar) (H : @bhyps o) (d1 : a <> b) (safe : safe_library lib),
    rule_true lib (rule_ils2 lib a b H).
Proof.
  unfold rule_ils2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls2_extract a b) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp; introv h; autorewrite with slow in *; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  assert (tequality lib (ils2c a b) (ils2c a b)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    intros lib' xt a1 a2 ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat (rewrite substc_mkcv_function;[|auto];[]).
    autorewrite with slow.

    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_mkc_or.

    dands.

    { apply tequality_mkc_equality_sp; dands; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.
  }

  dands; auto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].
  clear teq.

  intros lib' xt a1 a2 ea.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).
  autorewrite with slow.

  apply equality_in_function2; dands; eauto 3 with slow.

  {
    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_mkc_or.

    dands.

    { apply equality_refl in ea.
      apply tequality_mkc_equality_sp; dands; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.

    apply equality_refl in ea.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.
  }

  intros lib' xt b1 b2 eb.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ea;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply reduces_toc_implies_ccequivc_ext;
     apply apply_apply_ls2c_extract;tcsp|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply reduces_toc_implies_ccequivc_ext;
     apply apply_apply_ls2c_extract;tcsp|].

  repeat rewrite substcv_as_substc2.
  autorewrite with slow.
  repeat rewrite substc2_mk_cv_app_r; tcsp.
  autorewrite with slow.

  apply equality_in_csname_iff in ea.
  apply equality_in_csname_iff in eb.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact eb]; clear ea eb; introv y ea eb; exrepnd; spcast.
  unfold equality_of_csname in *; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  apply equality_mkc_or.
  dands; eauto 3 with slow.

  { apply equality_on_closed_terms_is_a_type; eauto 3 with slow. }

  {
    eapply type_respects_alphaeqc;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    apply equality_on_closed_terms_is_a_type; eauto 3 with slow.
  }

  apply in_ext_implies_all_in_ex_bar.
  introv xt.

  eapply lib_extends_preserves_computes_to_valc in ea2;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in eb2;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in eb0;[|eauto].
  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  destruct (choice_sequence_name_deq name0 name) as [d|d]; subst.

  {
    left.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    apply member_equality.
    apply equality_in_csname_iff.
    apply in_ext_implies_all_in_ex_bar; introv xt; exists name; dands; spcast; eauto 3 with slow.
  }

  {
    right.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    eapply alphaeqc_preserving_equality;
      [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply equality_in_not; dands.

    { apply equality_on_closed_terms_is_a_type; eauto 3 with slow. }

    introv xt inh.
    apply inhabited_mkc_equality in inh.
    apply equality_in_csname_iff in inh.
    unfold equality_of_csname_bar in inh; exrepnd.

    pose proof (bar_non_empty bar) as q; exrepnd.
    pose proof (inh0 _ q0 lib'0) as inh0; autodimp inh0 hyp; eauto 3 with slow; simpl in *.
    unfold equality_of_csname in inh0; exrepnd; spcast.

    assert (lib_extends lib'0 lib) as xt1 by eauto 3 with slow.

    eapply lib_extends_preserves_computes_to_valc in ea2;[|exact xt1].
    eapply lib_extends_preserves_computes_to_valc in eb2;[|exact xt1].

    eapply computes_to_valc_eq in ea2;[|exact inh2].
    eapply computes_to_valc_eq in eb2;[|exact inh1].
    ginv; tcsp.
  }
Qed.



Definition els2 {o} (a b : NVar) : @NTerm o :=
  mk_function
    (mk_csname 0)
    a
    (mk_function
       (mk_csname 0)
       b
       (mk_or
          (mk_equality (mk_var a) (mk_var b) (mk_nat2nat))
          (mk_not (mk_equality (mk_var a) (mk_var b) (mk_nat2nat))))).

Definition mkcv_nat2nat vs {o} := @mkcv_fun o vs (mkcv_tnat _) (mkcv_tnat _).

Definition els2c {o} (a b : NVar) : @CTerm o :=
  mkc_function
    (mkc_csname 0)
    a
    (mkcv_function
       _
       (mkcv_csname _ 0)
       b
       (mkcv_or
          _
          (mkcv_equality _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)) (mkcv_nat2nat _))
          (mkcv_not _ (mkcv_equality _ (mk_cv_app_l [b] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var b)) (mkcv_nat2nat _))))).

Lemma lsubstc_els2_eq {o} :
  forall a b (w : @wf_term o (els2 a b)) s c,
    lsubstc (els2 a b) w s c = els2c a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_els2_eq : slow.

Lemma isprog_mk_nat2nat {o} : @isprog o mk_nat2nat.
Proof.
  introv.
  apply isprog_eq; split;[|apply nt_wf_eq; apply wf_term_mk_nat2nat].
  unfold closed; simpl; auto.
Qed.
Hint Resolve isprog_mk_nat2nat : slow.

Lemma substc2_mkcv_nat2nat {o} :
  forall b (t : @CTerm o) a,
    substc2 b t a (mkcv_nat2nat [b,a])
    = mkcv_nat2nat _.
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl; tcsp.
  fold (@mk_nat2nat o).
  rewrite subst_trivial; eauto 3 with slow.
Qed.
Hint Rewrite @substc2_mkcv_nat2nat : slow.

Lemma substc_mkcv_nat2nat {o} :
  forall v (t : @CTerm o),
    (mkcv_nat2nat [v]) [[v \\ t]]
    = nat2nat.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  fold (@mk_nat2nat o).
  rewrite subst_trivial; eauto 3 with slow.
Qed.
Hint Rewrite @substc_mkcv_nat2nat : slow.

Lemma tequality_nat2nat {o} :
  forall lib, @tequality o lib nat2nat nat2nat.
Proof.
  introv; apply type_nat2nat.
Qed.
Hint Resolve tequality_nat2nat : slow.



(**

<<
   H |- ∀ (a b:Free(0)). a = b in Baire ∨ !(a = b in Baire)

     By eLS2
>>

 *)


Definition rule_els2 {o}
           (lib : @library o)
           (a b : NVar)
           (H  : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (els2 a b) (ls2_extract a b)))
    []
    [].

Lemma rule_els2_true {o} :
  forall lib (a b : NVar) (H : @bhyps o) (d1 : a <> b) (safe : safe_library lib),
    rule_true lib (rule_els2 lib a b H).
Proof.
  unfold rule_els2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls2_extract a b) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp; introv h; autorewrite with slow in *; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  assert (tequality lib (els2c a b) (els2c a b)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    intros lib' xt a1 a2 ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat (rewrite substc_mkcv_function;[|auto];[]).
    autorewrite with slow.

    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_mkc_or.

    dands.

    { apply tequality_mkc_equality_sp; dands; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.
  }

  dands; auto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].
  clear teq.

  intros lib' xt a1 a2 ea.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).
  autorewrite with slow.

  apply equality_in_function2; dands; eauto 3 with slow.

  {
    apply tequality_function; dands; eauto 3 with slow;[].
    intros lib' xt b1 b2 eb.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ea;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat rewrite substcv_as_substc2.
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_mkc_or.

    dands.

    { apply equality_refl in ea.
      apply tequality_mkc_equality_sp; dands; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    eapply tequality_respects_alphaeqc_right;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.

    apply equality_refl in ea.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.
  }

  intros lib' xt b1 b2 eb.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ea;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply reduces_toc_implies_ccequivc_ext;
     apply apply_apply_ls2c_extract;tcsp|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply reduces_toc_implies_ccequivc_ext;
     apply apply_apply_ls2c_extract;tcsp|].

  repeat rewrite substcv_as_substc2.
  autorewrite with slow.
  repeat rewrite substc2_mk_cv_app_r; tcsp.
  autorewrite with slow.

  apply equality_in_csname_iff in ea.
  apply equality_in_csname_iff in eb.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact eb]; clear ea eb; introv y ea eb; exrepnd; spcast.
  unfold equality_of_csname in *; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply computes_to_valc_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  apply equality_mkc_or.
  dands; eauto 3 with slow.

  { apply equality_on_closed_terms_is_a_type; eauto 3 with slow. }

  {
    eapply type_respects_alphaeqc;
      [apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not|].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply tequality_not.
    apply equality_on_closed_terms_is_a_type; eauto 3 with slow.
  }

  apply in_ext_implies_all_in_ex_bar.
  introv xt.

  eapply lib_extends_preserves_computes_to_valc in ea2;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in eb2;[|eauto].
  eapply lib_extends_preserves_computes_to_valc in eb0;[|eauto].
  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  destruct (choice_sequence_name_deq name0 name) as [d|d]; subst.

  {
    left.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    apply member_equality.
    apply equality_in_csname_implies_equality_in_nat2nat; auto.
    apply equality_in_csname_iff.
    apply in_ext_implies_all_in_ex_bar; introv xt; exists name; dands; spcast; eauto 3 with slow.
  }

  {
    right.
    exists (@mkc_axiom o) (@mkc_axiom o).
    dands; spcast.

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    { unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    eapply alphaeqc_preserving_equality;
      [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_not].
    autorewrite with slow.
    repeat rewrite substc2_mk_cv_app_r; tcsp.
    autorewrite with slow.

    apply equality_in_not; dands.

    { apply equality_on_closed_terms_is_a_type; eauto 3 with slow. }

    introv xt inh.
    apply inhabited_mkc_equality in inh.

    (* extend inh with a library where a1 contains 0, and where b1 contains 1 *)

    Lemma extend_entries_with_different_values {o} :
      forall (lib : @library o) name1 name2,
        name1 <> name2
        -> compatible_choice_sequence_name 0 name1
        -> compatible_choice_sequence_name 0 name2
        -> safe_library lib
        -> exists lib' n,
          lib_extends lib' lib
          /\ find_cs_value_at lib' name1 n = Some mkc_zero
          /\ find_cs_value_at lib' name2 n = Some mkc_one.
    Proof.
      introv dn comp1 comp2 safe.
    Qed.

SearchAbout equality nat2nat.
XXXXXX
    apply equality_in_csname_iff in inh.
    unfold equality_of_csname_bar in inh; exrepnd.

    pose proof (bar_non_empty bar) as q; exrepnd.
    pose proof (inh0 _ q0 lib'0) as inh0; autodimp inh0 hyp; eauto 3 with slow; simpl in *.
    unfold equality_of_csname in inh0; exrepnd; spcast.

    assert (lib_extends lib'0 lib) as xt1 by eauto 3 with slow.

    eapply lib_extends_preserves_computes_to_valc in ea2;[|exact xt1].
    eapply lib_extends_preserves_computes_to_valc in eb2;[|exact xt1].

    eapply computes_to_valc_eq in ea2;[|exact inh2].
    eapply computes_to_valc_eq in eb2;[|exact inh1].
    ginv; tcsp.

XXXXXXXXX

XXXXX
    apply inhabited_cequiv in inh.
    eapply all_in_ex_bar_implies_exists_lib_extends in inh;[|apply lib_extends_refl].
    exrepnd; GC; spcast.
    eapply cequivc_choice_seq in inh0; eauto 3 with slow.
    apply computes_to_valc_isvalue_eq in inh0; ginv;eauto 3 with slow.
  }
Qed.
