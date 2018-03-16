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
    [apply ccequivc_ext_sym; apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym; apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].

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
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
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

  eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb0;[|eauto].
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

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
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

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
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

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|exact xt1].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|exact xt1].

    computes_to_eqval_ext; ccomputes_to_valc_ext_val.
    hide_hyp eb2.
    computes_to_eqval_ext; ccomputes_to_valc_ext_val.
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

Lemma exists_extend_library_with_name2 {o} :
  forall name (lib : @library o),
    is_nat_or_seq_kind name
    -> safe_library lib
    ->
    exists lib',
      lib_extends lib' lib
      /\ name_in_library name lib'.
Proof.
  introv ins safe.
  exists (add_cs_if_not_in name lib); dands; eauto 3 with slow.
Qed.

Lemma entry_in_library_implies_name_in_library {o} :
  forall (name : choice_sequence_name) (lib : @library o) entry,
    entry_in_library entry lib
    -> entry2name entry = entry_name_cs name
    -> name_in_library name lib.
Proof.
  induction lib; introv i e; simpl in *; tcsp.
  repndors; repnd; subst; allrw; tcsp.

  applydup IHlib in i; auto.
  right; dands; auto; introv xx.
  destruct a; simpl in *; subst; ginv.
  destruct i0.
  unfold matching_entries; allrw; simpl; auto.
Qed.

Lemma entry_extends_implies_same_entry2name {o} :
  forall (entry1 entry2 : @library_entry o),
    entry_extends entry1 entry2
    -> entry2name entry1 = entry2name entry2.
Proof.
  introv h.
  unfold entry_extends in *; destruct entry1, entry2; simpl in *; repnd; subst; tcsp; ginv.
  inversion h; subst; tcsp.
Qed.

Lemma name_in_library_monotone {o} :
  forall name (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> name_in_library name lib1
    -> name_in_library name lib2.
Proof.
  introv ext i.
  apply name_in_library_implies_entry_in_library in i; exrepnd.
  apply ext in i1.
  apply entry_in_library_extends_implies_entry_in_library in i1; exrepnd.
  eapply entry_in_library_implies_name_in_library; eauto.
  apply entry_extends_implies_same_entry2name in i2; congruence.
Qed.
Hint Resolve name_in_library_monotone : slow.

Definition cs_kind_size (k : cs_kind) : nat :=
  match k with
  | cs_kind_nat _ => 0
  | cs_kind_seq l => length l
  end.

Definition cs_name_size (name : choice_sequence_name) : nat :=
  match name with
  | MkChoiceSequenceName n k => cs_kind_size k
  end.

Fixpoint cs_entry_size {o} (lib : @library o) (name : choice_sequence_name) : nat :=
  match lib with
  | [] => 0
  | lib_cs name' e :: lib' =>
    if choice_sequence_name_deq name name'
    then length (cse_vals e)
    else cs_entry_size lib' name
  | lib_abs _ _ _ _ :: lib' => cs_entry_size lib' name
  end.

Lemma cs_entry_in_library_lawless_upto_implies_length_eq {o} :
  forall (lib lib' : @library o) name k vals restr,
    cs_entry_size lib' name <= k
    -> is_nat_or_seq_kind name
    -> correct_restriction name restr
    -> extend_library_lawless_upto lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> k = length vals.
Proof.
  induction lib; introv lek isn cor ext ilib; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto.

  { destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
    destruct restr; tcsp.

    - destruct entry.
      destruct cse_restriction; repnd; exrepnd; subst; ginv;[].
      rewrite length_app; allrw; simpl in *; try omega.

    - unfold correct_restriction in *.
      subst.
      unfold is_nat_or_seq_kind in *.
      destruct name0 as [name kd]; simpl in *.
      destruct kd; subst; boolvar; tcsp. }

  { eapply IHlib; eauto.
    destruct l; simpl in *; tcsp;[].
    boolvar; subst; tcsp;[].
    destruct a; simpl in *; tcsp; ginv.
    boolvar; tcsp; ginv.
    destruct ilib0; tcsp. }
Qed.
Hint Resolve cs_entry_in_library_lawless_upto_implies_length_eq : slow.

Lemma safe_library_implies_correct_restriction {o} :
  forall (lib : @library o) name vals restr,
    safe_library lib
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
    -> correct_restriction name restr.
Proof.
  introv safe f.
  apply find_cs_some_implies_entry_in_library in f.
  apply safe in f.
  simpl in *; tcsp.
Qed.
Hint Resolve safe_library_implies_correct_restriction : slow.

Lemma extend_library_lawless_upto_doesnt_change_size_others {o} :
  forall (lib' lib : @library o) name name0 m,
    extend_library_lawless_upto lib' lib name m
    -> name0 <> name
    -> cs_entry_size lib' name0 = cs_entry_size lib name0.
Proof.
  induction lib'; introv ext d; simpl in *; destruct lib; tcsp.
  repnd.
  eapply IHlib' in ext; eauto.
  simpl in *.
  destruct a, l; simpl in *; tcsp; boolvar; subst; tcsp; ginv; tcsp.
Qed.

Lemma extend_library_lawless_upto_doesnt_change_others {o} :
  forall (lib' lib : @library o) name name0 m vals restr,
    extend_library_lawless_upto lib' lib name m
    -> name0 <> name
    -> find_cs lib name0 = Some (MkChoiceSeqEntry _ vals restr)
    -> find_cs lib' name0 = Some (MkChoiceSeqEntry _ vals restr).
Proof.
  induction lib'; introv ext d f; simpl in *; destruct lib; tcsp.
  repnd.
  simpl in *.
  destruct a,l; simpl in *; tcsp; boolvar; subst; tcsp; ginv; tcsp;
    subst; GC; eapply IHlib' in ext; eauto.
Qed.

Lemma find_cs_snoc {o} :
  forall (lib : @library o) a name,
    find_cs (snoc lib a) name
    = match find_cs lib name with
      | Some x => Some x
      | None =>
        match a with
        | lib_cs name' e => if choice_sequence_name_deq name name' then Some e else None
        | _ => None
        end
      end.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; allrw; tcsp.
  boolvar; subst; tcsp.
Qed.

Lemma implies_choice_sequence_satisfies_restriction_snoc {o} :
  forall name vals (restr : @ChoiceSeqRestriction o) k,
    choice_sequence_satisfies_restriction vals restr
    -> compatible_choice_sequence_name 0 name
    -> cs_name_size name <= length vals
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction (snoc vals (mkc_nat k)) restr.
Proof.
  introv sat comp lev cor.
  unfold choice_sequence_satisfies_restriction.
  destruct restr; simpl in *; tcsp.

  - introv h.
    allrw @select_snoc_eq.
    boolvar; tcsp; ginv.
    unfold correct_restriction in cor.
    unfold compatible_choice_sequence_name in *; simpl in *.
    unfold compatible_cs_kind in *; boolvar; tcsp; GC.
    destruct name as [name kd]; simpl in *.
    destruct kd; simpl in *; boolvar; subst; tcsp; GC; repnd.

    + apply cor; eauto 3 with slow.

    + apply cor; auto; eauto 3 with slow.

  - introv h; autorewrite with slow in *.
    rewrite select_snoc_eq; boolvar; tcsp; subst; try omega.
    unfold correct_restriction in *.
    unfold compatible_choice_sequence_name in *.
    unfold compatible_cs_kind in *; boolvar; tcsp; GC.
    destruct name as [name kd]; simpl in *.
    destruct kd; subst; tcsp; boolvar; tcsp.
Qed.
Hint Resolve implies_choice_sequence_satisfies_restriction_snoc : slow.

Lemma extend_choice_sequence {o} :
  forall name vals restr k (lib : @library o),
    compatible_choice_sequence_name 0 name
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
    -> cs_name_size name <= length vals
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> exists lib',
        lib_extends lib' lib
        /\ map entry2name lib' = map entry2name lib
        /\ find_cs lib' name = Some (MkChoiceSeqEntry _ (snoc vals (mkc_nat k)) restr)
        /\ (forall name', name <> name' -> find_cs lib' name' = find_cs lib name').
Proof.
  induction lib using rev_list_ind; introv comp find ges cor sat; simpl in *; tcsp;[].
  rewrite find_cs_snoc in find.
  remember (find_cs lib name) as f; symmetry in Heqf.
  destruct f; ginv.

  {
    repeat (autodimp IHlib hyp); exrepnd.
    exists (snoc lib' a); dands; eauto 3 with slow.

    { apply implies_lib_extends_snoc_lr_same_names; auto. }

    { allrw map_snoc; allrw; tcsp. }

    { rewrite find_cs_snoc; rewrite IHlib3; auto. }

    { introv d.
      repeat (rewrite find_cs_snoc).
      rewrite IHlib0; auto. }
  }

  {
    destruct a; boolvar; tcsp; ginv.
    clear IHlib.
    exists (snoc lib (lib_cs name0 (MkChoiceSeqEntry _ (snoc vals (mkc_nat k)) restr))).
    allrw map_snoc; simpl.
    dands; auto.

    { apply implies_lib_extends_snoc; eauto 3 with slow.

      - simpl; dands; auto 3 with slow.
        eapply implies_choice_sequence_satisfies_restriction_snoc; eauto.

      - unfold entry_extends; dands; auto.
        unfold choice_sequence_entry_extend; simpl; dands; eauto 3 with slow.
        unfold choice_sequence_vals_extend.
        exists [@mkc_nat o k].
        rewrite snoc_as_append; auto.
    }

    { rewrite find_cs_snoc.
      allrw; boolvar; tcsp. }

    { introv d.
      repeat (rewrite find_cs_snoc).
      remember (find_cs lib name') as fc; destruct fc; tcsp.
      boolvar; tcsp. }
  }
Qed.

Lemma extend_two_choice_sequences {o} :
  forall (lib : @library o) name1 name2 vals1 restr1 vals2 restr2,
    name1 <> name2
    -> compatible_choice_sequence_name 0 name1
    -> compatible_choice_sequence_name 0 name2
    -> cs_name_size name1 <= length vals1
    -> cs_name_size name2 <= length vals2
    -> correct_restriction name1 restr1
    -> correct_restriction name2 restr2
    -> choice_sequence_satisfies_restriction vals1 restr1
    -> choice_sequence_satisfies_restriction vals2 restr2
    -> find_cs lib name1 = Some (MkChoiceSeqEntry _ vals1 restr1)
    -> find_cs lib name2 = Some (MkChoiceSeqEntry _ vals2 restr2)
    -> exists lib',
        lib_extends lib' lib
        /\ find_cs lib' name1 = Some (MkChoiceSeqEntry _ (snoc vals1 mkc_zero) restr1)
        /\ find_cs lib' name2 = Some (MkChoiceSeqEntry _ (snoc vals2 mkc_one) restr2).
Proof.
  introv d comp1 comp2 le1 le2 cor1 cor2 sat1 sat2; introv find1 find2.

  pose proof (extend_choice_sequence name1 vals1 restr1 0 lib) as q.
  repeat (autodimp q hyp); exrepnd;[].

  rewrite <- q0 in find2; tcsp;[].

  clear find1 q0.

  pose proof (extend_choice_sequence name2 vals2 restr2 1 lib') as h.
  repeat (autodimp h hyp); exrepnd;[].
  rewrite <- h0 in q3; tcsp;[].

  allrw <- @mkc_zero_eq.
  allrw <- @mkc_one_eq.

  exists lib'0; dands; eauto 3 with slow.
Qed.

Lemma safe_library_implies_choice_sequence_satisfies_restriction {o} :
  forall (lib : @library o) name vals restr,
    safe_library lib
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
    -> choice_sequence_satisfies_restriction vals restr.
Proof.
  introv safe f.
  apply find_cs_some_implies_entry_in_library in f.
  apply safe in f.
  simpl in *; tcsp.
Qed.
Hint Resolve safe_library_implies_choice_sequence_satisfies_restriction : slow.

Lemma implies_ccomputes_to_valc_ext_apply_choice_seq {o} :
  forall lib (a : @CTerm o) name n v,
    ccomputes_to_valc_ext lib a (mkc_nat n)
    -> find_cs_value_at lib name n = Some v
    -> iscvalue v
    -> ccomputes_to_valc_ext lib (mkc_apply (mkc_choice_seq name) a) v.
Proof.
  introv comp find iscv.
  apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext.
  eapply ccomputes_to_valc_ext_integer_implies_computes_to_valc_in_ext in comp; eauto.
  spcast.
  eapply implies_compute_to_valc_apply_choice_seq; eauto; eauto 3 with slow.
Qed.



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
    [apply ccequivc_ext_sym;apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply ccequivc_ext_apply_apply_ls2c_extract;tcsp|].

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
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccequivc_ext_refl
     |apply ccequivc_ext_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_cs_eq;
     [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
     |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto
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

  eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in ea0;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
  eapply lib_extends_preserves_ccomputes_to_valc in eb0;[|eauto].
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

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
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

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
      split; eauto 3 with slow.
      apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; ginv; tcsp. }

    { apply in_ext_computes_to_valc_implies_ccomputes_to_valc_ext; introv ext; spcast.
      unfold computes_to_valc; simpl.
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

    clear a2 ea0.
    clear b2 eb0.

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
    assert (safe_library lib') as safe' by eauto 2 with slow.
    clear eqh sim.
    clear lib xt safe.
    rename safe' into safe.
    rename lib' into lib.

    pose proof (exists_extend_library_with_name2 name lib) as q.
    repeat (autodimp q hyp); eauto 3 with slow; exrepnd.

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
    eapply equality_monotone in inh;[|eauto].
    assert (safe_library lib') as safe' by eauto 2 with slow.
    clear lib q1 safe.
    rename safe' into safe.
    rename lib' into lib.

    pose proof (exists_extend_library_with_name2 name0 lib) as q.
    repeat (autodimp q hyp); eauto 3 with slow; exrepnd.

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
    eapply equality_monotone in inh;[|eauto].
    eapply name_in_library_monotone in q0;[|eauto].
    assert (safe_library lib') as safe' by eauto 2 with slow.
    clear lib q2 safe.
    rename safe' into safe.
    rename lib' into lib.

    pose proof (fresh_choice_seq_name_in_library lib []) as fresh; exrepnd.
    remember (library2inf lib (simple_inf_choice_seq name1)) as ilib.

    remember (Peano.max
                (Peano.max
                   (cs_name_size name)
                   (cs_name_size name0))
                (Peano.max
                   (cs_entry_size lib name)
                   (cs_entry_size lib name0))) as m.

    pose proof (exists_extend_library_lawless_upto_following_infinite ilib name m lib) as q.
    repeat (autodimp q hyp); try (complete (subst; eauto 3 with slow)).
    exrepnd.

    pose proof (exists_extend_library_lawless_upto_following_infinite ilib name0 m lib') as q.
    repeat (autodimp q hyp); try (complete (subst; eauto 3 with slow)).
    exrepnd.

    assert (lib_extends lib' lib) as xt1 by eauto 3 with slow.
    assert (lib_extends lib'0 lib) as xt2 by eauto 3 with slow.
    eapply name_in_library_monotone in q0;[|exact xt1].
    eapply name_in_library_monotone in q1;[|exact xt2].

    apply name_in_library_implies_entry_in_library in q0; exrepnd.
    apply name_in_library_implies_entry_in_library in q1; exrepnd.

    pose proof (extend_library_lawless_upto_implies_exists_nats name lib' lib entry m) as xx.
    repeat (autodimp xx hyp); eauto 3 with slow; try congruence.

    pose proof (extend_library_lawless_upto_implies_exists_nats name0 lib'0 lib' entry0 m) as yy.
    repeat (autodimp yy hyp); eauto 3 with slow; try congruence.

    exrepnd.

    assert (length vals0 = m) as le1.
    {
      pose proof (cs_entry_in_library_lawless_upto_implies_length_eq lib' lib name m vals0 restr0) as zz.
      repeat (autodimp zz hyp); eauto 3 with slow;[].
      subst m; eapply le_trans;[|apply max_prop2]; apply max_prop1.
    }
    clear xx2.

    assert (length vals = m) as le2.
    {
      pose proof (cs_entry_in_library_lawless_upto_implies_length_eq lib'0 lib' name0 m vals restr) as zz.
      repeat (autodimp zz hyp); eauto 3 with slow;[].
      eapply extend_library_lawless_upto_doesnt_change_size_others in q3;eauto.
      subst m; rewrite q3; eapply le_trans;[|apply max_prop2]; apply max_prop2.
    }
    clear yy2.

    eapply extend_library_lawless_upto_doesnt_change_others in xx0;[|eauto|]; tcsp.

    clear lib' q3 q2 q5 xt1 q0.
    clear entry q6.
    clear entry0 q1 q7.
    clear ilib Heqilib q4.
    clear name1 fresh1 fresh0.

    assert (length vals0 = length vals) as eqlen by congruence.
    assert (cs_name_size name <= length vals0) as leq1.
    { allrw; eapply le_trans;[|apply max_prop1];apply max_prop1. }
    assert (cs_name_size name0 <= length vals) as leq2.
    { allrw; eapply le_trans;[|apply max_prop1];apply max_prop2. }

    clear m Heqm le1 le2.

    rename lib'0 into lib'.

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
    eapply equality_monotone in inh;[|eauto].
    assert (safe_library lib') as safe' by eauto 2 with slow.
    clear lib safe xt2.
    rename safe' into safe.
    rename lib' into lib.

    pose proof (extend_two_choice_sequences lib name name0 vals0 restr0 vals restr) as h.
    repeat (autodimp h hyp); eauto 3 with slow.

    exrepnd.

    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].
    eapply equality_monotone in inh;[|eauto].
    assert (safe_library lib') as safe' by eauto 2 with slow.
    clear lib safe h1 yy0 xx0.
    rename safe' into safe.
    rename lib' into lib.

    eapply equality_respects_cequivc_left in inh;
      [|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto].
    eapply equality_respects_cequivc_right in inh;
      [|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto].

    apply (equality_nat2nat_apply _ _ _ (mkc_nat (length vals)) (mkc_nat (length vals))) in inh; eauto 3 with slow;[].
    apply equality_in_tnat in inh.
    unfold per_props_nat.equality_of_nat_bar, all_in_ex_bar in inh; exrepnd.

    pose proof (bar_non_empty bar) as q; exrepnd.
    pose proof (inh0 _ q0 lib') as inh0; autodimp inh0 hyp; eauto 3 with slow; simpl in *.
    unfold per_props_nat.equality_of_nat in inh0; exrepnd; spcast.

    assert (lib_extends lib' lib) as ext by eauto 3 with slow.
    clear bar q0.
    eapply lib_extends_preserves_find_cs in h2;[|eauto].
    eapply lib_extends_preserves_find_cs in h0;[|eauto].
    exrepnd; simpl in *.
    unfold choice_sequence_vals_extend in *; exrepnd.
    destruct entry0, entry2; simpl in *; subst.
    eapply lib_extends_preserves_ccomputes_to_valc in ea2;[|eauto].
    eapply lib_extends_preserves_ccomputes_to_valc in eb2;[|eauto].

    pose proof (implies_ccomputes_to_valc_ext_apply_choice_seq lib' (mkc_nat (length vals)) name0 (length vals) mkc_one) as w.
    repeat (autodimp w hyp); eauto 3 with slow.

    {
      unfold find_cs_value_at; allrw; simpl.
      rewrite find_value_of_cs_at_vals_as_select.
      rewrite select_app_l; autorewrite with slow; try omega.
      rewrite select_snoc_eq; boolvar; try omega; tcsp.
    }

    pose proof (implies_ccomputes_to_valc_ext_apply_choice_seq lib' (mkc_nat (length vals)) name (length vals) mkc_zero) as z.
    repeat (autodimp z hyp); eauto 3 with slow.

    {
      unfold find_cs_value_at; allrw; simpl.
      rewrite find_value_of_cs_at_vals_as_select.
      rewrite select_app_l; autorewrite with slow; try omega.
      rewrite select_snoc_eq; boolvar; try omega; tcsp.
    }

    computes_to_eqval_ext.
    rw @mkc_zero_eq in ceq; repeat (rw @mkc_nat_eq in ceq).
    ccomputes_to_valc_ext_val.
    apply Nat2Z.inj in ceq; subst.
    hide_hyp inh1.

    computes_to_eqval_ext.
    rw @mkc_one_eq in ceq; repeat (rw @mkc_nat_eq in ceq).
    ccomputes_to_valc_ext_val.
    apply Nat2Z.inj in ceq; subst; omega.
  }
Qed.
