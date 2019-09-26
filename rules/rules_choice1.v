Require Export rules_choice.



(**

<<
   H |- ∀ (n ∈ ℕ) (f ∈ ℕn→ℕ). ↓∃ (a:Free). f = a ∈ ℕn→ℕ

     By LS1
>>

 *)

(* Write a proper extract instead of axiom *)
Definition rule_ls1 {o}
           (lib   : @library o)
           (n f a : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls1 n f a) (ls1_extract n f)))
    []
    [].

Lemma rule_ls1_true {o} :
  forall lib (n f a : NVar) (H : @bhyps o)
         (d1 : n <> f) (d2 : n <> a) (d3 : a <> f) (safe : safe_library lib),
    rule_true lib (rule_ls1 lib n f a H).
Proof.
  unfold rule_ls1, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls1_extract n f) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  assert (tequality lib (ls1c n f a) (ls1c n f a)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    repeat (rewrite substc_mkcv_function;[|auto];[]).

    apply equality_in_tnat in ea; eapply e_all_in_ex_bar_as in ea.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib y safe.
    rename lib' into lib; rename safe' into safe.

    unfold equality_of_nat in ea; exrepnd; spcast.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls1_cond1; auto|];[].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls1_cond1; auto|];[].

    apply tequality_function; dands; eauto 3 with slow.

    {
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      autorewrite with slow.
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    introv xt ef.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
    autorewrite with slow in *.
    apply tequality_mkc_squash.

    repeat (rewrite mkcv_exists_substc; auto;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  dands; eauto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].

  clear teq.

  introv xt ea.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  repeat (rewrite substc_mkcv_function;[|auto];[]).

  apply equality_in_tnat in ea; apply e_all_in_ex_bar_as in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  unfold equality_of_nat in ea; exrepnd; spcast.

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
      apply subst_ls1_cond1; auto];[].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls1c_extract;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls1c_extract;eauto|].

  apply equality_in_function2.
  dands.

  {
    apply tequality_function; dands; eauto 3 with slow.

    {
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_mkcv_natk2nat|].
      autorewrite with slow.
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    introv xt ef.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
    autorewrite with slow in *.
    apply tequality_mkc_squash.

    repeat (rewrite mkcv_exists_substc; auto;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  introv xt ef.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib xt safe.
  rename lib' into lib; rename safe' into safe.

  eapply alphaeqc_preserving_equality in ef;[|apply substc_mkcv_natk2nat].
  autorewrite with slow in *.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_mkc_lam_ax;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_mkc_lam_ax;eauto|].

  rewrite mkcv_exists_substc; auto.
  autorewrite with slow.
  rewrite substc2_mk_cv_app_r; auto.

  apply equality_in_mkc_squash_ax.

  dup ef as en2n.
  eapply cequivc_preserving_equality in ef;
    [|introv ext; spcast; apply implies_cequivc_natk2nat;
      apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow].
  dup ef as enf.
  apply equality_natk2nat_implies2 in enf.

  eapply all_in_ex_bar_modus_ponens1;[|exact enf]; clear enf; introv y enf; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  eapply equality_monotone in ef;[|eauto].
  eapply equality_monotone in en2n;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib y safe.
  rename lib' into lib; rename safe' into safe.

  apply computes_upto_implies_exists_nat_seq in enf; exrepnd.

  apply inhabited_exists.
  dands; eauto 3 with slow.

  {
    introv xt ecs.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    eapply equality_monotone in en2n;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    clear lib xt safe enf0.
    rename lib' into lib; rename safe' into safe.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply equality_refl in en2n.
    apply tequality_mkc_equality_if_equal; eauto 3 with slow.

    {
      eapply tequality_respects_cequivc_left;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eapply tequality_respects_cequivc_right;
        [apply ccequivc_ext_sym; introv z; spcast; apply implies_cequivc_natk2nat;
         apply ccomputes_to_valc_ext_implies_cequivc;eauto 3 with slow|].
      eauto 3 with slow.
    }

    eapply equality_in_csname_implies_equality_in_natk2nat; eauto.
  }

  (* NOTE: We don't need a fresh [cs_name] because we have the restriction!
       Any [cs_name] would do. *)
  pose proof (fresh_choice_seq_name_in_library lib l) as w.
  exrepnd.

  assert (is_nat_or_seq_kind name) as isn.
  eauto 3 with slow.

  exists (@mkc_pair o (mkc_choice_seq name) mkc_axiom).
  apply e_all_in_ex_bar_as.
  apply all_in_ex_bar_implies_e_all_in_ex_bar.
  exists (extend_seq_to_bar lib safe n0 name isn).
  introv br ext.
  exists (@mkc_choice_seq o name) (@mkc_axiom o).
  autorewrite with slow.

  dands; spcast; eauto 3 with slow;[|].

  {
    apply equality_in_csname_iff.
    apply e_all_in_ex_bar_as.
    apply in_ext_implies_in_open_bar; introv xt.
    exists name; dands; spcast; eauto 3 with slow.
  }

  rw <- @member_equality_iff.
  eapply cequivc_preserving_equality;
    [|apply ccequivc_ext_sym;
      introv xt; spcast; apply implies_cequivc_natk2nat;
      apply ccomputes_to_valc_ext_implies_cequivc;eauto 5 with slow].

  simpl in *; exrepnd.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in br2; exrepnd.
  applydup safe' in br2.

  pose proof (extend_library_lawless_upto_implies_exists_nats name lib' lib'' entry n0) as q.
  repeat (autodimp q hyp); exrepnd.

  apply implies_equality_natk2nat_prop.
  introv ltk.

  pose proof (q1 m (nth m vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; omega|];[].
  unfold is_nat in w; exrepnd.
  assert (select m vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try omega. }

  assert (safe_library_entry (lib_cs name (MkChoiceSeqEntry _ vals restr))) as safee.
  { eapply entry_in_library_implies_safe_library_entry; eauto 3 with slow. }
  simpl in * |-; repnd.

  pose proof (enf0 m i) as enf0.
  autodimp enf0 hyp;
    [eapply satisfies_cs_kind_seq_implies_select_iff; eauto; try omega|];[].
  repnd; spcast.

  exists i.
  dands; spcast; eauto 5 with slow;[].
  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto.
Qed.
Hint Resolve rule_ls1_true : slow.



(**

<<
   H |- f ∈ ℕ→ℕ

     By FreeSubypeBaire

     H |- f ∈ Free(0)
>>

 *)

(* Write a proper extract instead of axiom *)
Definition rule_free_sub_baire {o}
           (lib   : @library o)
           (f e   : NTerm)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member f (mk_fun mk_tnat mk_tnat))))
    [mk_baresequent H (mk_concl (mk_member f (mk_csname 0)) e)]
    [].

Lemma rule_free_sub_baire_true {o} :
  forall lib (f e : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true lib (rule_free_sub_baire lib f e H).
Proof.
  unfold rule_free_sub_baire, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (@covered o mk_axiom (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  lsubst_tac.

  rw <- @member_member_iff.
  eapply teq_and_member_if_member; eauto.

  {
    lsubst_tac.
    autorewrite with slow.
    fold (@nat2nat o).
    apply type_nat2nat.
  }

  clear dependent s1.
  clear dependent s2.
  introv eqh sim.

  vr_seq_true in hyp1.
  pose proof (hyp1 lib' ext s1 s2 eqh sim) as hyp1; exrepnd.
  lsubst_tac.
  apply member_if_inhabited in hyp1.
  apply tequality_mkc_member_implies_sp in hyp0; auto;[].
  autorewrite with slow in *.
  fold (@nat2nat o).

  remember (lsubstc f wt s1 ca1) as t1; clear Heqt1.
  remember (lsubstc f wt s2 ca2) as t2; clear Heqt2.
  eauto 3 with slow.
Qed.
