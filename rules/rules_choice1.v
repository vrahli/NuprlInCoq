Require Export rules_choice.



Lemma fresh_choice_seq_nat {o} :
  forall (lib : @library o) (n : nat),
  exists (name : choice_sequence_name),
    find_cs lib name = None
    /\ csn_kind name = cs_kind_nat n.
Proof.
  introv.
  exists (MkChoiceSequenceName (fresh_cs_in_lib lib) (cs_kind_nat n)); simpl; dands; auto.
  unfold fresh_cs_in_lib.
  pose proof (fresh_cs_not_in (map csn_name (choice_seq_names_in_lib lib))) as q.
  remember (fresh_cs (map csn_name (choice_seq_names_in_lib lib))) as v; clear Heqv.
  induction lib; simpl; auto.
  destruct a;[|].

  { destruct name; simpl;[].
    simpl; boolvar; ginv.

    - allrw in_map_iff; simpl in *.
      destruct q.
      eexists; dands;eauto.

    - allrw in_map_iff; simpl in *.
      apply IHlib; clear IHlib; introv xx; exrepnd; subst.
      destruct q; exrepnd.
      eexists; dands;eauto. }

  { allrw in_map_iff; simpl in *.
    apply IHlib; clear IHlib; introv xx; exrepnd; subst.
    destruct q; exrepnd.
    eexists; dands;eauto. }
Qed.

Lemma correct_restriction_csc_seq {o} :
  forall name l n,
    1 < n
    -> csn_kind name = cs_kind_nat n
    -> @correct_restriction o name (csc_seq l).
Proof.
  introv ltn h.
  unfold correct_restriction; simpl.
  rewrite h; simpl; auto.
  boolvar; subst; tcsp; try omega.
  apply Nat.lt_irrefl in ltn; tcsp.
Qed.
Hint Resolve correct_restriction_csc_seq : slow.

SearchAbout csc_nat correct_restriction.

Lemma correct_restriction_csc_nat_0 {o} :
  forall name,
    csn_kind name = cs_kind_nat 0
    -> @correct_restriction o name csc_nat.
Proof.
  introv h.
  apply correct_restriction_csc_nat.
  unfold is_nat_choice_sequence_name; allrw; auto; boolvar; tcsp.
Qed.
Hint Resolve correct_restriction_csc_nat_0 : slow.

Definition new_lib_cs_seq {o} name (l : list nat) : @library_entry o :=
  lib_cs name (MkChoiceSeqEntry _ (map mkc_nat l) csc_nat).

Lemma safe_library_entry_new_lib_cs_seq {o} :
  forall name l,
    csn_kind name = cs_kind_nat 0
    -> @safe_library_entry o (new_lib_cs_seq name l).
Proof.
  introv h.
  unfold safe_library_entry; simpl; dands; eauto 3 with slow.
  introv q; simpl in *.
  rewrite select_map in q.
  unfold option_map in q; remember (select n l) as w; symmetry in Heqw; destruct w; ginv; eauto 3 with slow.
Qed.
Hint Resolve safe_library_entry_new_lib_cs_seq : slow.

Lemma non_shadowed_entry_new_lib_cs_seq {o} :
  forall name l (lib : @library o),
    find_cs lib name = None
    -> non_shadowed_entry (new_lib_cs_seq name l) lib.
Proof.
  introv h.
  unfold non_shadowed_entry.
  rewrite forallb_forall; introv i.
  eapply find_cs_none_implies_diff_entry_names; eauto.
Qed.
Hint Resolve non_shadowed_entry_new_lib_cs_seq : slow.

Lemma compatible_choice_sequence_name_0_if_kind_nat_0 :
  forall name,
    csn_kind name = cs_kind_nat 0
    -> compatible_choice_sequence_name 0 name.
Proof.
  introv h.
  unfold compatible_choice_sequence_name, compatible_cs_kind; simpl; allrw; simpl; auto.
Qed.
Hint Resolve compatible_choice_sequence_name_0_if_kind_nat_0 : slow.

Lemma ccomputes_to_valc_ext_choice_seq_if_extends_new_lib_cs_seq {o} :
  forall (lib : @library o) name m l,
    m < length l
    -> entry_in_library_extends (new_lib_cs_seq name l) lib
    -> (mkc_apply (mkc_choice_seq name) (mkc_nat m)) ===>(lib) (mkc_nat (nth m l 0)).
Proof.
  introv ltl i.
  eapply implies_ccomputes_to_valc_ext_apply_cs;
    try apply lib_extends_refl;
    try apply ccomputes_to_valc_ext_refl; eauto 3 with slow.
  apply entry_in_library_extends_implies_entry_in_library in i; exrepnd.

  inversion i0; subst; eauto 3 with slow; clear i0.

  { apply entry_in_library_implies_find_cs_some in i1; tcsp.
    unfold find_cs_value_at; allrw.
    rewrite find_value_of_cs_at_is_select; simpl.
    rewrite select_map.
    rewrite (nth_select1 _ _ 0); auto. }

  { apply entry_in_library_implies_find_cs_some in i1; tcsp.
    unfold find_cs_value_at; allrw.
    rewrite find_value_of_cs_at_is_select; simpl.
    rewrite select_app_l; try autorewrite with slow; auto;[].
    rewrite select_map.
    rewrite (nth_select1 _ _ 0); auto. }
Qed.


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
         (d1 : n <> f) (d2 : n <> a) (d3 : a <> f)
         (safe : safe_library lib)
         (norep : no_repeats_library lib),
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
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib safe norep ext.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.

  assert (tequality lib (ls1c n f a) (ls1c n f a)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib xt safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

    repeat (rewrite substc_mkcv_function;[|auto];[]).

    apply equality_in_tnat in ea.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib y safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib xt safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib xt safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib xt safe norep.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.

  repeat (rewrite substc_mkcv_function;[|auto];[]).

  apply equality_in_tnat in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe norep.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib xt safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    clear lib xt safe norep.
    rename lib' into lib; rename safe' into safe; rename norep' into norep.

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
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib xt safe norep.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.

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

  apply all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar.
  eapply all_in_ex_bar_modus_ponens1;[|exact enf]; clear enf; introv y enf; exrepnd; spcast.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  eapply equality_monotone in ef;[|eauto].
  eapply equality_monotone in en2n;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe norep.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.

  apply computes_upto_implies_exists_nat_seq in enf; exrepnd.
  introv xta.

  pose proof (fresh_choice_seq_nat lib' 0) as fn; exrepnd.
  assert (lib_extends (new_lib_cs_seq name l :: lib') lib') as xtb.
  { apply implies_lib_extends_cons_left; eauto 3 with slow. }
  exists (new_lib_cs_seq name l :: lib') xtb.

  introv xtc.

  apply inhabited_exists.
  dands; eauto 3 with slow.

  {
    introv xt ecs.

    assert (lib_extends lib'1 lib) as xtd by eauto 4 with slow.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea1;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
    eapply equality_monotone in ef;[|eauto].
    eapply equality_monotone in en2n;[|eauto].
    assert (safe_library lib'1) as safe' by eauto 3 with slow.
    assert (no_repeats_library lib'1) as norep' by eauto 3 with slow.
    clear lib xt safe norep enf0 xta xtd.
    rename lib'1 into lib; rename safe' into safe; rename norep' into norep.

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

  exists (@mkc_pair o (mkc_choice_seq name) mkc_axiom).
  apply in_ext_implies_all_in_ex_bar; introv xtd.
  exists (@mkc_choice_seq o name) (@mkc_axiom o).
  autorewrite with slow.

  dands; spcast; eauto 3 with slow;[|].

  {
    apply equality_in_csname_iff.
    apply in_ext_implies_in_open_bar; introv xt.
    exists name; dands; spcast; eauto 3 with slow.
  }

  rw <- @member_equality_iff.
  eapply cequivc_preserving_equality;
    [|apply ccequivc_ext_sym;
      introv xt; spcast; apply implies_cequivc_natk2nat;
      apply ccomputes_to_valc_ext_implies_cequivc;
      assert (lib_extends lib'2 lib) as xt' by eauto 5 with slow;
      eapply lib_extends_preserves_ccomputes_to_valc; eauto].

  apply implies_equality_natk2nat_prop.
  introv ltn.
  pose proof (enf0 m (nth m l 0)) as w.
  autodimp w hyp;[apply nth_select1; omega|];[].
  repnd; clear w.

  assert (lib_extends lib'1 lib) as xte by eauto 4 with slow.
  eexists; dands;[eapply lib_extends_preserves_ccomputes_to_valc; eauto|].

  assert (lib_extends lib'1 (new_lib_cs_seq name l :: lib')) as xtf by eauto 3 with slow.
  assert (entry_in_library (new_lib_cs_seq name l) (new_lib_cs_seq name l :: lib')) as i by tcsp.
  apply implies_lib_extends_ext in xtf.
  apply xtf in i.
  apply ccomputes_to_valc_ext_choice_seq_if_extends_new_lib_cs_seq; auto; try omega.
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
  forall lib (f e : NTerm) (H : @bhyps o) (safe : safe_library lib) (norep : no_repeats_library lib),
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
  apply equality_in_csname_implies_equality_in_nat2nat; eauto 2 with slow.
Qed.
