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


Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export subst_tacs3.
Require Export cequiv_tacs.
Require Export cequiv_props3.
Require Export per_props_equality.
Require Export per_props_product.
Require Export per_props_nat.
Require Export per_props_squash.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export rules_tyfam.
Require Export lsubst_hyps.
Require Export terms_pi.
Require Export per_props_natk2nat.
Require Export per_props_cs.
Require Export fresh_cs.


Definition entry_free_from_choice_seq_name {o} (e : @library_entry o) (name : choice_sequence_name) :=
  match e with
  | lib_cs n l =>
    if choice_sequence_name_deq n name then False
    else True
  | lib_abs _ _ _ _ => True
  end.

Fixpoint lib_free_from_choice_seq_name {o} (lib : @plibrary o) (name : choice_sequence_name) :=
  match lib with
  | [] => True
  | e :: es =>
    (entry_free_from_choice_seq_name e name)
      # lib_free_from_choice_seq_name es name
  end.

Definition sequent_true_ex_ext {o} uk lib (s : @csequent o) :=
  {lib' : library & lib_extends lib' lib # sequent_true uk lib' s}.

Definition rule_true_ex_ext {o} uk lib (R : @rule o) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  forall cargs: args_constraints (sargs R) (hyps (goal R)),
  forall hyps : (forall s : baresequent,
                   LIn s (subgoals R)
                   -> {c : wf_csequent s & sequent_true uk lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & sequent_true_ex_ext uk lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.


Definition ls1 {o} (n f a : NVar) : @NTerm o :=
  mk_function
    mk_tnat
    n
    (mk_function
       (mk_natk2nat (mk_var n))
       f
       (mk_squash
          (mk_exists
             (mk_csname 0)
             a
             (mk_equality
                (mk_var f)
                (mk_var a)
                (mk_natk2nat (mk_var n)))))).

Definition ls1c {o} (n f a : NVar) : @CTerm o :=
  mkc_function
    mkc_tnat
    n
    (mkcv_function
       _
       (mkcv_natk2nat _ (mkc_var n))
       f
       (mkcv_squash
          _
          (mkcv_exists
             _
             (mkcv_csname _ 0)
             a
             (mkcv_equality
                [a,f,n]
                (mk_cv_app_l [a] _ (mk_cv_app_r [n] _ (mkc_var f)))
                (mk_cv_app_r [f,n] _ (mkc_var a))
                (mk_cv_app_l [a,f] _ (mkcv_natk2nat _ (mkc_var n))))))).

Definition ls1_extract {o} (n f : NVar) : @NTerm o :=
  mk_lam n (mk_lam f mk_axiom).

Definition ls1c_extract {o} (n f : NVar) : @CTerm o :=
  mkc_lam n (mkcv_lam [n] f (mkcv_ax _)).

Lemma lsubstc_ls1_extract_eq {o} :
  forall n f (w : @wf_term o (ls1_extract n f)) s c,
    lsubstc (ls1_extract n f) w s c = ls1c_extract n f.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls1_extract_eq : slow.

Lemma rename_nvars_cons_left :
  forall a k l, remove_nvars (a :: k) (a :: l) = remove_nvars (a :: k) l.
Proof.
  introv.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars_cons_left : slow.

Lemma rename_nvars_cons_cons :
  forall a b k l, remove_nvars (a :: k) (b :: a :: l) = remove_nvars (a :: k) (b :: l).
Proof.
  introv.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars_cons_cons : slow.

Lemma rename_nvars2_cons :
  forall a b k j l,
    remove_nvars (a :: k) (remove_nvars (b :: j) (a :: l))
    = remove_nvars (a :: k) (remove_nvars (b :: j) l).
Proof.
  introv.
  repeat (rewrite remove_nvars_app_l); simpl.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars2_cons : slow.

Lemma rename_nvars3_cons :
  forall a1 a2 a3 k1 k2 k3 l,
    remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) (a1 :: l)))
    = remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) l)).
Proof.
  introv.
  repeat (rewrite remove_nvars_app_l); simpl.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars3_cons : slow.

Lemma rename_nvars4_cons :
  forall a1 a2 a3 a4 k1 k2 k3 k4 l,
    remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) (remove_nvars (a4 :: k4) (a1 :: l))))
    = remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) (remove_nvars (a4 :: k4) l))).
Proof.
  introv.
  repeat (rewrite remove_nvars_app_l); simpl.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars4_cons : slow.

Lemma rename_nvars5_cons :
  forall a1 a2 a3 a4 a5 k1 k2 k3 k4 k5 l,
    remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) (remove_nvars (a4 :: k4) (remove_nvars (a5 :: k5) (a1 :: l)))))
    = remove_nvars (a1 :: k1) (remove_nvars (a2 :: k2) (remove_nvars (a3 :: k3) (remove_nvars (a4 :: k4) (remove_nvars (a5 :: k5) l)))).
Proof.
  introv.
  repeat (rewrite remove_nvars_app_l); simpl.
  unfold remove_nvars; simpl; boolvar; auto; tcsp.
Qed.
Hint Rewrite rename_nvars5_cons : slow.

Hint Rewrite remove_nvars_app_r : slow.
Hint Rewrite remove_nvars_nil_r : slow.
Hint Rewrite app_nil_l : slow.

Lemma lsubstc_ls1_eq {o} :
  forall n f a (w : @wf_term o (ls1 n f a)) s c,
    lsubstc (ls1 n f a) w s c = ls1c n f a.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls1_eq : slow.

(* MOVE *)
Lemma tequality_mkc_tnat {o} : forall uk lib, @tequality o uk lib mkc_tnat mkc_tnat.
Proof.
  introv; apply tnat_type.
Qed.
Hint Resolve tequality_mkc_tnat : slow.

Lemma fold_image {o} :
  forall (a b : @NTerm o),
    oterm (Can NImage) [nobnd a, nobnd b]
    = mk_image a b.
Proof.
  tcsp.
Qed.

Lemma fold_mk_squash {o} :
  forall (a : @NTerm o),
    mk_image a (mk_lam nvarx mk_axiom) = mk_squash a.
Proof.
  tcsp.
Qed.

Lemma implies_alpha_eq_mk_squash {o} :
  forall (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (mk_squash a) (mk_squash b).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma implies_alpha_eq_mk_product {o} :
  forall x v (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (mk_product x v a) (mk_product x v b).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma implies_alpha_eq_mk_equality {o} :
  forall x y (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (mk_equality x y a) (mk_equality x y b).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma subst_ls1_cond1 {o} :
  forall n f a (t : @CTerm o) (d1 : n <> a) (d2 : n <> f),
    alphaeqcv
      _
      (substcv
         [f] t n
         (mkcv_squash
            _
            (mkcv_exists
               _
               (mkcv_csname _ 0)
               a
               (mkcv_equality
                  _
                  (mk_cv_app_l [a] ([f] ++ [n]) (mk_cv_app_r [n] [f] (mkc_var f)))
                  (mk_cv_app_r [f, n] [a] (mkc_var a))
                  (mk_cv_app_l [a, f] [n] (mkcv_natk2nat [n] (mkc_var n)))))))
      (mkcv_squash
         [f]
         (mkcv_exists
            _
            (mkcv_csname _ 0)
            a
            (mkcv_equality
               _
               (mk_cv_app_l [a] _ (mkc_var f))
               (mk_cv_app_r [f] [a] (mkc_var a))
               (mk_cv _ (natk2nat t))))).
Proof.
  introv d1 d2.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfsubst; simpl.

  autorewrite with slow.
  boolvar; tcsp.
  fold_terms.
  simpl.
  repeat (autorewrite with slow; rewrite beq_var_newvar_trivial1; simpl; tcsp;[]).
  boolvar; tcsp;[].

  allrw @fold_image.
  allrw @fold_mk_squash.
  allrw @fold_csname.
  apply implies_alpha_eq_mk_squash.
  apply implies_alpha_eq_mk_product.
  apply implies_alpha_eq_mk_equality.

  fold (mk_natk2nat x).

  pose proof (substc_mkcv_natk2nat n (mkc_var n) (mk_ct x i)) as q.
  unfold alphaeqc in q; simpl in q.
  unfsubst in q; simpl in q.

  repeat (autorewrite with slow in q; rewrite beq_var_newvar_trivial1 in q; simpl in q; tcsp;[]).
  fold_terms.

  unfsubst in q; simpl in *; boolvar; tcsp.
Qed.

Lemma implies_alphaeqc_mk_function {o} :
  forall x v (a b : @CVTerm o [v]),
    alphaeqcv [v] a b
    -> alphaeqc (mkc_function x v a) (mkc_function x v b).
Proof.
  introv aeq.
  destruct_cterms.
  unfold alphaeqc, alphaeqcv in *; simpl in *.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma implies_equality_natk2nat_bar {o} :
  forall uk lib (f g : @CTerm o) n,
    in_open_bar
      lib
      (fun lib =>
         forall m,
           m < n
           -> {k : nat
               , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
               # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality uk lib f g (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { eapply type_mkc_natk_aux; rewrite mkc_nat_eq; eauto 3 with slow. }

  introv x e.
  eapply equality_in_natk_aux in e; exrepnd;[|rewrite mkc_nat_eq; eauto 3 with slow].

  eapply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv y e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        exact e1]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  assert (m < n) as ltm by lia.
  clear e0.

  apply equality_in_tnat.
  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
  clear dependent lib'.
  eapply lib_extends_preserves_all_in_ex_bar in imp;[|exact xt].
  eapply all_in_ex_bar_modus_ponens1;try exact imp; clear imp; introv ext imp; exrepnd; spcast.
  clear dependent lib.

  pose proof (imp m ltm) as h; exrepnd.
  exists k; dands; spcast; eauto 2 with slow.
Qed.

Lemma implies_member_natk2nat_bar {o} :
  forall uk lib (f : @CTerm o) n,
    in_open_bar
      lib
      (fun lib =>
         forall m,
           m < n
           -> {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member uk lib f (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nat_bar.
  eapply all_in_ex_bar_modus_ponens1;try exact imp; clear imp; introv ext imp; exrepnd; spcast.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists k; auto.
Qed.

Lemma name_in_library_implies_entry_in_library {o} :
  forall name (lib : @plibrary o),
    name_in_library name lib
    ->
    exists entry,
      entry_in_library entry lib
      /\ entry2name entry = entry_name_cs name.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; repndors; repnd; subst; tcsp; GC.

  - exists (lib_cs name0 entry); simpl; dands; tcsp.

  - autodimp IHlib hyp; exrepnd.
    exists entry0; simpl; dands; tcsp.
    right; dands; tcsp.
    unfold matching_entries; allrw; simpl; auto.

  - autodimp IHlib hyp; exrepnd.
    exists entry; simpl; dands; tcsp.
    right; dands; tcsp.
    unfold matching_entries; allrw; simpl; auto.
Qed.

(*Lemma is_nat_or_seq_kind_implies_compatible_choice_sequence_name_0 :
  forall name,
    is_primitive_kind name
    -> compatible_choice_sequence_name 0 name.
Proof.
  introv h; destruct name as [name k]; simpl in *.
  unfold is_primitive_kind in *; simpl in *.
  unfold compatible_choice_sequence_name; simpl.
  unfold compatible_cs_kind; boolvar; tcsp.
Locate compatible_choice_sequence_name.
Qed.
Hint Resolve is_primitive_kind_implies_compatible_choice_sequence_name_0 : slow.*)

Lemma compatible_choice_sequence_name_0_implies_is_primitive_kind :
  forall name,
    compatible_choice_sequence_name 0 name
    -> is_primitive_kind name.
Proof.
  introv h; destruct name as [name k]; simpl in *.
  unfold is_primitive_kind in *; simpl in *.
  unfold compatible_choice_sequence_name in *; simpl.
  unfold compatible_cs_kind in *; boolvar; tcsp.
  simpl in *; GC; destruct k; subst; tcsp.
Qed.
Hint Resolve compatible_choice_sequence_name_0_implies_is_primitive_kind : slow.

Hint Resolve entry_in_library_implies_find_cs_some : slow.

Lemma cs_entry_in_library_lawless_upto_implies_length_ge {o} :
  forall C (lib lib' : @plibrary o) name k vals restr,
    is_primitive_kind name
    -> correct_restriction name restr
    -> extend_plibrary_lawless_upto C lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> k <= length vals.
Proof.
  induction lib; introv isn cor ext ilib; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto;[].

  destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
  inversion ext0 as [? ? ? ? ext'(*|? ? ? ? ? ext'|*)]; subst; clear ext0;
    try (complete (unfold extend_choice_seq_vals_lawless_upto in *;
                   exrepnd; subst; rewrite length_app; try lia)).
Qed.
Hint Resolve cs_entry_in_library_lawless_upto_implies_length_ge : slow.

Lemma is_nat_mkc_nat {o} :
  forall n i, @is_nat o n (mkc_nat i).
Proof.
  introv; eexists; eauto.
Qed.
Hint Resolve is_nat_mkc_nat : slow.

Lemma cterm_is_nth_implies_is_nat {o} :
  forall (v : @CTerm o) n l,
    cterm_is_nth v n l
    -> is_nat n v.
Proof.
  introv h.
  unfold cterm_is_nth in *; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve cterm_is_nth_implies_is_nat : slow.

Lemma is_nat_if_compatible_and_correct {o} :
  forall name res vals n (v : @ChoiceSeqVal o),
    correct_restriction name res
    -> compatible_choice_sequence_name 0 name
    -> choice_sequence_satisfies_restriction vals res
    -> select n vals = Some v
    -> is_nat n v.
Proof.
  introv cor comp sat sel.
  unfold choice_sequence_satisfies_restriction, correct_restriction, compatible_choice_sequence_name in *.
  destruct res, name as [name kd], kd; simpl in *; tcsp; boolvar; subst; repnd; tcsp;
    try (complete (apply cor; auto)).

  { destruct (lt_dec n (length l)) as [dd|dd];
      try (complete (apply cor; auto; try lia)).
    apply sat in sel; apply cor0 in sel; auto; eauto 3 with slow. }

(*  { rewrite sat in sel; eauto 3 with slow; inversion sel; subst; auto. }*)
Qed.

Lemma cs_entry_in_library_lawless_upto_implies_is_nat {o} :
  forall C (lib lib' : @plibrary o) name k vals restr n v,
    compatible_choice_sequence_name 0 name
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> extend_plibrary_lawless_upto C lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> select n vals = Some v
    -> is_nat n v.
Proof.
  induction lib; introv isn cor sat ext ilib sel; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto;[].

  clear IHlib ext.

  destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
  inversion ext0 as [? ? ? ? ext'(*|? ? ? ? ext'|? ? ? ? ext'*)]; subst; clear ext0;
    try (unfold extend_choice_seq_vals_lawless_upto in *; exrepnd; subst);
    try (complete (eapply is_nat_if_compatible_and_correct; eauto)).
Qed.
Hint Resolve cs_entry_in_library_lawless_upto_implies_is_nat : slow.

Lemma extend_library_lawless_upto_implies_exists_nats {o} :
  forall C name (lib lib' : @plibrary o) entry k,
    compatible_choice_sequence_name 0 name
    -> entry_in_library entry lib
    -> entry2name entry = entry_name_cs name
    -> safe_library_entry entry
    -> extend_plibrary_lawless_upto C lib lib' name k
    -> exists vals restr,
        find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
        /\ k <= length vals
        /\ forall n v, select n vals = Some v -> is_nat n v.
Proof.
  introv isn ilib eqname safe ext.
  destruct entry; simpl in *; tcsp; ginv;[].
  destruct entry as [vals restr]; simpl in *; repnd.
  exists vals restr.
  dands; eauto 3 with slow.
Qed.

Hint Rewrite Znat.Nat2Z.id : slow.

Lemma choice_sequence_vals_extends_implies_select_some {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) m t,
    choice_sequence_vals_extend vals2 vals1
    -> select m vals1 = Some t
    -> select m vals2 = Some t.
Proof.
  introv h q; unfold choice_sequence_vals_extend in *; exrepnd; subst.
  rewrite select_app_l; eauto 3 with slow.
Qed.

Lemma choice_sequence_vals_extend_app {o} :
  forall (vals vals' : @ChoiceSeqVals o),
    choice_sequence_vals_extend (vals ++ vals') vals.
Proof.
  introv; unfold choice_sequence_vals_extend; eauto.
Qed.
Hint Resolve choice_sequence_vals_extend_app : slow.

(* MOVE *)
Lemma implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext {o} :
  forall lib lib' name vals restr m (v : @CTerm o),
    lib_extends lib' lib
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
    -> select m vals = Some v
    -> iscvalue v
    -> (mkc_apply (mkc_choice_seq name) (mkc_nat m)) ===>(lib') v.
Proof.
  introv ext findcs sel iscv xt.
  exists v; dands; spcast; eauto 2 with slow.

  unfold computes_to_valc; simpl.
  split; eauto 3 with slow.
  eapply reduces_to_if_split2;[csunf; simpl; reflexivity|].
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_eapply; simpl; boolvar; try lia;[].
  autorewrite with slow.

  assert (lib_extends lib'0 lib) as e by eauto 3 with slow.
  clear dependent lib'.

  eapply lib_extends_preserves_find_cs in findcs;[|eauto].
  exrepnd; simpl in *.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  unfold find_cs_value_at.
  allrw;simpl.
  rewrite find_value_of_cs_at_is_select.
  erewrite choice_sequence_vals_extends_implies_select_some; eauto; simpl; auto; eauto 3 with slow.
Qed.

Lemma lib_satisfies_default_add_cs_if_not_in {o} :
  forall name (lib : @library o),
    is_primitive_kind name
    -> safe_library lib
    -> lib_satisfies_default name (add_one_cs_if_not_in name lib) (choice_sequence_name2default name).
Proof.
  introv prim safe fcs; introv; simpl in *.
  unfold add_cs_if_not_in in fcs.
  remember (find_cs lib name) as fcs'; symmetry in Heqfcs'; destruct fcs'; simpl in *; tcsp.

  { rewrite fcs in *; ginv.
    apply find_cs_some_implies_entry_in_library in fcs.
    apply safe in fcs; simpl in *.
    destruct c as [vals restr]; simpl in *; repnd.
    destruct restr; simpl in *.
    destruct name as [name kind]; simpl in *.
    unfold correct_restriction, is_primitive_kind, choice_sequence_name2default in *; simpl in *.
    destruct kind; simpl in *; boolvar; subst; tcsp; repnd; try lia.
    { apply fcs0; eauto 3 with slow. }
    { apply fcs0; eauto 3 with slow. }
    { destruct (lt_dec n (length l)) as [dd|dd].
      { apply fcs1; auto; eauto 3 with slow. }
      { apply fcs0; eauto 3 with slow; try lia. } } }

  boolvar; subst; tcsp; GC.
  inversion fcs; simpl in *; subst; GC.
  unfold satisfies_restriction; simpl.
  destruct name as [name kind]; simpl in *.
  unfold is_primitive_kind, choice_sequence_name2restriction, choice_sequence_name2default in *; simpl in *.
  destruct kind; simpl in *; boolvar; subst; simpl in *; tcsp; eauto 3 with slow.
Qed.
Hint Resolve lib_satisfies_default_add_cs_if_not_in : slow.

Lemma is_primitive_kind_implies_lib_cond_sat {o} :
  forall (lib : @library o) name n,
    lib_cond_sat_def lib
    -> is_primitive_kind name
    -> lib_cond lib (get_cterm (choice_sequence_name2default name n)).
Proof.
  introv sat prim.
  unfold is_primitive_kind in prim.
  destruct name as [name k]; simpl in *.
  destruct k; simpl in *; tcsp; tcsp; try apply sat.
  unfold choice_sequence_name2default; simpl; boolvar; subst; apply sat.
Qed.
Hint Resolve is_primitive_kind_implies_lib_cond_sat : slow.

Lemma extend_library_lawless_upto_pres_name_in_library {o} :
  forall (lib1 lib2 : @library o) name k,
    extend_library_lawless_upto lib1 lib2 name k
    -> name_in_library name lib2
    -> name_in_library name lib1.
Proof.
  introv ext i; destruct lib1 as [lib1 c1], lib2 as [lib2 c2]; simpl in *.
  unfold extend_library_lawless_upto in *; simpl in *; repnd; eauto 3 with slow.
Qed.
Hint Resolve extend_library_lawless_upto_pres_name_in_library : slow.

Lemma name_in_library_add_one_cs_if_not_in {o} :
  forall name (lib : @library o),
    name_in_library name (add_one_cs_if_not_in name lib).
Proof.
  introv.
  unfold add_one_cs_if_not_in; simpl; eauto 3 with slow.
Qed.
Hint Resolve name_in_library_add_one_cs_if_not_in : slow.

Lemma extend_seq_to_ext {o} :
  forall (lib  : @library o)
         (norp : no_repeats_library lib)
         (safe : safe_library lib)
         (k    : nat)
         (name : choice_sequence_name)
         (isn  : is_primitive_kind name)
         (sat  : lib_cond_sat_def lib)
         (satr : sat_cond_name2restr lib name),
  exists (lib' : library),
    extend_library_lawless_upto lib' (add_one_cs_if_not_in name lib) name k.
Proof.
  introv norep safe isn sat satr.
  pose proof (exists_extend_library_lawless_upto name k (add_one_cs_if_not_in name lib) (choice_sequence_name2default name)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
  { introv; simpl; eauto 3 with slow. }
  exrepnd.
  exists lib'; dands; simpl in *; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_lib_cond_sat_def {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> lib_cond_sat_def lib2
    -> lib_cond_sat_def lib1.
Proof.
  introv ext sat.
  apply lib_extends_implies_same_conds in ext.
  unfold lib_cond_sat_def in *; try congruence.
Qed.
Hint Resolve lib_extends_preserves_lib_cond_sat_def : slow.

Lemma same_conds_preserves_extend_library_lawless_upto {o} :
  forall C1 C2 (lib1 lib2 : @plibrary o) name n,
    C1 = C2
    -> extend_plibrary_lawless_upto C1 lib1 lib2 name n
    -> extend_plibrary_lawless_upto C2 lib1 lib2 name n.
Proof.
  introv; congruence.
Qed.

Lemma lib_extends_preserves_sat_cond_restr {o} :
  forall r (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> sat_cond_restr lib1 r
    -> sat_cond_restr lib2 r.
Proof.
  introv ext sat.
  unfold sat_cond_restr in *; eauto 3 with slow.
  apply lib_extends_implies_same_conds in ext; rewrite ext; tcsp.
Qed.
Hint Resolve lib_extends_preserves_sat_cond_restr : slow.

Lemma lib_extends_preserves_sat_cond_name2restr {o} :
  forall name (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> sat_cond_name2restr lib1 name
    -> sat_cond_name2restr lib2 name.
Proof.
  introv ext sat.
  unfold sat_cond_name2restr in *; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_sat_cond_name2restr : slow.

Lemma mkc_choice_seq_in_natk2nat {o} :
  forall uk (lib : @library o) (name : choice_sequence_name) k,
    compatible_choice_sequence_name 0 name
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> sat_cond_name2restr lib name
    -> member uk lib (mkc_choice_seq name) (natk2nat (mkc_nat k)).
Proof.
  introv comp norep safe sat satr.
  apply implies_member_natk2nat_bar.
  applydup compatible_choice_sequence_name_0_implies_is_primitive_kind in comp as isn.

  (* first we need to add the sequence to the library *)
  introv ext.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  assert (sat_cond_name2restr lib' name) as satr' by eauto 3 with slow.
  pose proof (extend_seq_to_ext lib' norep' safe' k name isn sat' satr') as q; exrepnd.
  assert (lib_extends lib'0 lib') as xta.
  { apply extend_library_lawless_upto_implies_lib_extends in q0; eauto 3 with slow. }

  exists lib'0 xta.
  introv xtb ltm.
  simpl in * |-; exrepnd.
  assert (safe_library lib'0) as safe'' by eauto 3 with slow.
  assert (name_in_library name lib'0) as ilib by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in ilib; exrepnd.
  applydup safe'' in ilib1.

  pose proof (extend_library_lawless_upto_implies_exists_nats (lib_cond lib') name lib'0 (add_one_cs_if_not_in name lib') entry k) as q.
  repeat (autodimp q hyp); exrepnd.
  { unfold extend_library_lawless_upto in *; repnd.
    eapply same_conds_preserves_extend_library_lawless_upto;[|eauto].
    apply lib_extends_implies_same_conds in xta; tcsp. }
  pose proof (q2 m (nth m vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; lia|];[].
  unfold is_nat in w; exrepnd.
  assert (select m vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try lia. }

  exists i.
  spcast.
  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto.
Qed.

Lemma comp0_implies_sat_cond_name2restr {o} :
  forall (lib : @library o) name,
    compatible_choice_sequence_name 0 name
    -> lib_cond_sat_def lib
    -> sat_cond_name2restr lib name.
Proof.
  introv comp sat.
  unfold compatible_choice_sequence_name in *; simpl in *.
  unfold compatible_cs_kind in *; simpl in *.
  destruct name as [n k], k; simpl in *; subst; tcsp;
    unfold sat_cond_name2restr; simpl;
      unfold choice_sequence_name2restriction; simpl; auto; apply sat.
Qed.
Hint Resolve comp0_implies_sat_cond_name2restr : slow.

Lemma equality_in_csname_implies_equality_in_natk2nat {o} :
  forall uk (lib : library) (a b t : @CTerm o) k,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> ccomputes_to_valc_ext lib t (mkc_nat k)
    -> equality uk lib a b (mkc_csname 0)
    -> equality uk lib a b (natk2nat t).
Proof.
  introv norep safe sat comp ecs.
  apply equality_in_csname in ecs.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ecs]; clear ecs; introv y ecs; exrepnd; spcast.
  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe sat norep.
  rename lib' into lib.

  unfold equality_of_csname in ecs; exrepnd; spcast.

  eapply cequivc_preserving_equality;
    [|apply ccequivc_ext_sym; introv x; spcast;
      apply implies_cequivc_natk2nat;
      apply ccomputes_to_valc_ext_implies_cequivc; eauto 3 with slow].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym; introv x; spcast;
     apply ccomputes_to_valc_ext_implies_cequivc; eauto 3 with slow|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym; introv x; spcast;
     apply ccomputes_to_valc_ext_implies_cequivc; eauto 3 with slow|].

  rw @member_eq.
  clear dependent a.
  clear dependent b.
  clear dependent t.
  apply mkc_choice_seq_in_natk2nat; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_mkc_apply_ls1c_extract {o} :
  forall lib (a : @CTerm o) n f k,
    ccomputes_to_valc_ext lib a (mkc_nat k)
    -> ccequivc_ext lib (mkc_apply (ls1c_extract n f) a) (mkc_lam f (mkcv_ax _)).
Proof.
  introv comp ext; spcast.
  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|eauto].
  destruct_cterms.
  unfold computes_to_valc in *; simpl in *.
  unfold cequivc; simpl.
  eapply cequiv_trans;[apply cequiv_beta; eauto 3 with slow;compute; tcsp|];[].
  unfsubst; simpl; fold_terms.
  apply cequiv_refl; compute; fold_terms; dands; eauto 3 with slow.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.

Lemma ccequivc_ext_mkc_apply_mkc_lam_ax {o} :
  forall lib f (a : @CTerm o),
    ccequivc_ext lib (mkc_apply (mkc_lam f (mkcv_ax _)) a) mkc_axiom.
Proof.
  introv ext; spcast.
  destruct_cterms.
  unfold cequivc; simpl.
  eapply cequiv_trans;[apply cequiv_beta; eauto 3 with slow;compute; tcsp|];[].
  unfsubst; simpl; fold_terms.
Qed.

(*Lemma nat2all_in_ex_bar2bar {o} :
  forall (n   : nat)
         (lib : @library o)
         (f   : nat -> library -> Prop)
         (F   : forall m, m < n -> all_in_ex_bar lib (f m)),
    {b : BarLib lib , forall m, m < n -> all_in_bar b (f m)}.
Proof.
  induction n; introv F.

  { exists (trivial_bar lib); introv h; lia. }

  pose proof (IHn lib f) as q.
  autodimp q hyp;[].
  exrepnd.
  pose proof (F n) as w; autodimp w hyp.
  unfold all_in_ex_bar in w; exrepnd.
  exists (intersect_bars b bar).
  introv ltn br ext; simpl in *; exrepnd.
  destruct (lt_dec m n) as [d|d].

  { eapply q0; eauto 3 with slow. }

  { assert (m = n) as xx by lia; subst.
    eapply w0; eauto 3 with slow. }
Qed.*)

Lemma nat2in_open_bar2open {o} :
  forall (n   : nat)
         (lib : @library o)
         (f   : nat -> library -> Prop)
         (F   : forall m, m < n -> in_open_bar lib (f m)),
    in_open_bar lib (fun lib => forall m, m < n -> f m lib).
Proof.
  induction n; introv F.

  { apply in_ext_implies_in_open_bar; introv ext h; lia. }

  pose proof (IHn lib f) as q; clear IHn.
  autodimp q hyp;[].
  pose proof (F n) as w; autodimp w hyp; []; clear F.
  eapply in_open_bar_comb; try exact q; clear q.
  eapply in_open_bar_pres; try exact w; clear w; introv ext w q h.
  destruct (lt_dec m n) as [d|d]; eauto;[].
  assert (m = n) as xx by lia; subst; auto.
Qed.

Lemma equality_natk2nat_implies2 {o} :
  forall uk lib (f g : @CTerm o) n,
    equality uk lib f g (natk2nat (mkc_nat n))
    -> in_open_bar
         lib
         (fun lib =>
            forall m,
              m < n ->
              {k : nat
              , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
              # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)}).
Proof.
  introv mem.

  assert (forall m,
             m < n
             -> in_open_bar lib (fun lib => {k : nat
                , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
                # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})) as h.
  { introv ltn; eapply equality_natk2nat_implies; eauto. }
  clear mem.

  apply nat2in_open_bar2open in h; auto.
Qed.

Lemma all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar {o} :
  forall uk lib (A : @CTerm o),
    in_open_bar lib (fun lib => inhabited_type_bar uk lib A)
    -> inhabited_type_bar uk lib A.
Proof.
  introv h.
  unfold inhabited_type_bar in *.
  apply collapse_all_in_ex_bar in h; auto.
Qed.
Hint Resolve all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar : slow.

Lemma select_snoc_eq :
  forall {A} n (l : list A) x,
    select n (snoc l x) =
    if lt_dec n (length l)
    then select n l
    else if deq_nat n (length l) then Some x else None.
Proof.
  induction n; introv; simpl in *.

  { destruct l; simpl; auto. }

  destruct l; simpl in *; autorewrite with slow; auto.
  rewrite IHn.
  boolvar; tcsp; try lia.
Qed.

Hint Rewrite length_snoc : slow.

Lemma computes_upto_implies_exists_nat_seq {o} :
  forall lib (a1 a2 : @CTerm o) k,
    (forall m : nat,
        m < k ->
        exists k,
          ((mkc_apply a1 (mkc_nat m)) ===>(lib) (mkc_nat k))
            # (mkc_apply a2 (mkc_nat m)) ===>(lib) (mkc_nat k))
    ->
    exists l,
      length l = k /\
      forall n i,
        select n l = Some i
        -> ((mkc_apply a1 (mkc_nat n)) ===>(lib) (mkc_nat i))
             # (mkc_apply a2 (mkc_nat n)) ===>(lib) (mkc_nat i).
Proof.
  induction k; introv h.

  { exists ([] : list nat); simpl; dands; tcsp.
    introv; autorewrite with slow; introv w; ginv. }

  autodimp IHk hyp; exrepnd.
  pose proof (h k) as h; autodimp h hyp; try lia; exrepnd.

  exists (snoc l k0); autorewrite with slow; dands; auto.
  introv h; simpl in *.
  rewrite select_snoc_eq in h.
  boolvar; tcsp; ginv; auto.
Qed.

Lemma fresh_choice_seq_name_in_library {o} :
  forall (lib : @plibrary o) (l : list nat),
  exists (name : choice_sequence_name),
    find_cs lib name = None
    /\ csn_kind name = cs_kind_seq l.
Proof.
  introv.
  exists (MkChoiceSequenceName (fresh_cs_in_lib lib) (cs_kind_seq l)); simpl; dands; auto.
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

Lemma csn_kind_seq_implies_is_primitive_kind :
  forall name l,
    csn_kind name = cs_kind_seq l
    -> is_primitive_kind name.
Proof.
  introv h.
  unfold is_primitive_kind.
  allrw; simpl; auto.
Qed.
Hint Resolve csn_kind_seq_implies_is_primitive_kind : slow.

Lemma implies_equality_natk2nat_prop {o} :
  forall uk lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat
           , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
           # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality uk lib f g (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.

  { eapply type_mkc_natk_aux; rewrite mkc_nat_eq; eauto 3 with slow. }

  introv x e.
  eapply equality_in_natk_aux in e; exrepnd;[|rewrite mkc_nat_eq; eauto 3 with slow].

  eapply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv y e; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl
     |apply ccequivc_ext_sym;
      apply ccomputes_to_valc_ext_implies_ccequivc_ext;
      exact e1]
    |].

  eapply equality_respects_cequivc_right;
    [apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl
     |apply ccequivc_ext_sym;
      apply ccomputes_to_valc_ext_implies_ccequivc_ext;
      exact e2]
    |].

  clear dependent a.
  clear dependent a'.

  assert (m < n) as ltm by lia.
  clear e0.

  apply equality_in_tnat.
  pose proof (imp m ltm) as h; exrepnd.
  apply in_ext_implies_all_in_ex_bar; introv z.
  exists k; dands; spcast; eauto 4 with slow.
Qed.

Lemma satisfies_cs_kind_seq_implies_select_iff {o} :
  forall name l (vals : @ChoiceSeqVals o) restr n i,
    csn_kind name = cs_kind_seq l
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> length l <= length vals
    -> n < length l
    -> select n l = Some i <-> select n vals = Some (mkc_nat i).
Proof.
  introv ek cor sat len lenn.
  unfold correct_restriction in *.
  rewrite ek in *.
  unfold is_nat_seq_restriction in *.
  destruct restr; simpl in *; repnd; tcsp.
  split; intro h.

  - remember (select n vals) as s; symmetry in Heqs; destruct s.

    + applydup sat in Heqs.
      apply cor0 in Heqs0; auto.
      unfold cterm_is_nth in Heqs0; exrepnd.
      rewrite h in Heqs0; ginv.

    + apply nth_select2 in Heqs; lia.

  - applydup sat in h.
    apply cor0 in h0; auto.
    unfold cterm_is_nth in h0; exrepnd.
    apply mkc_nat_eq_implies in h1; subst; auto.
Qed.

Lemma prim_implies_sat_cond_name2restr {o} :
  forall (lib : @library o) name,
    is_primitive_kind name
    -> lib_cond_sat_def lib
    -> sat_cond_name2restr lib name.
Proof.
  introv comp sat.
  unfold compatible_choice_sequence_name in *; simpl in *.
  unfold compatible_cs_kind in *; simpl in *.
  destruct name as [n k], k; simpl in *; subst; tcsp;
    unfold sat_cond_name2restr; simpl;
      unfold choice_sequence_name2restriction; simpl; auto;
        boolvar; subst; try apply sat.
Qed.
Hint Resolve prim_implies_sat_cond_name2restr : slow.

Lemma exists_extend_library_lawless_upto_name_in {o} :
  forall name n (lib : @library o),
    is_primitive_kind name
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    ->
    exists lib'' lib',
      extend_library_lawless_upto lib'' lib' name n
      /\ lib_extends lib' lib
      /\ name_in_library name lib''.
Proof.
  introv isns norep safe sat.
  pose proof (extend_seq_to_ext lib) as h; repeat (autodimp h hyp).
  pose proof (h n name) as h; repeat (autodimp h hyp); exrepnd; eauto 3 with slow.
  exists lib' (add_one_cs_if_not_in name lib); dands; auto; eauto 3 with slow.
Qed.

Lemma name_in_library_if_entry_in_library {o} :
  forall name entry (lib : @plibrary o),
    entry_in_library entry lib
    -> entry2name entry = entry_name_cs name
    -> name_in_library name lib.
Proof.
  induction lib; introv h q; simpl in *; tcsp.
  destruct a; simpl in *; repndors; repnd; subst; tcsp; GC;
    simpl in *; ginv; tcsp.
  destruct (choice_sequence_name_deq name name0); subst; tcsp.
Qed.

Lemma entry_extends_implies_entry2name {o} :
  forall (entry1 entry2 : @library_entry o),
    entry_extends entry1 entry2
    -> entry2name entry1 = entry2name entry2.
Proof.
  introv h; inversion h; subst; tcsp.
Qed.

Lemma add_choice_preserves_name_in_library {o} :
  forall x name v (lib : @plibrary o) n r lib',
    add_choice x v lib = Some (n, r, lib')
    -> name_in_library name lib
    -> name_in_library name lib'.
Proof.
  induction lib; introv addc h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; repndors; repnd; subst; tcsp; GC.

  { destruct entry as [vals restr]; boolvar; subst; tcsp.
    { inversion addc; subst; simpl in *; tcsp. }
    remember (add_choice x v lib) as w; symmetry in Heqw; destruct w; repnd; tcsp.
    inversion addc; subst; simpl in *; tcsp. }

  { destruct entry as [vals restr]; boolvar; subst; tcsp.
    { inversion addc; subst; simpl in *; tcsp. }
    remember (add_choice x v lib) as w; symmetry in Heqw; destruct w; repnd; tcsp.
    inversion addc; subst; simpl in *; tcsp.
    pose proof (IHlib n r p) as IHlib; repeat (autodimp IHlib hyp). }

  { remember (add_choice x v lib) as w; symmetry in Heqw; destruct w; repnd; tcsp.
    inversion addc; subst; simpl in *; tcsp.
    pose proof (IHlib n r p) as IHlib; repeat (autodimp IHlib hyp). }
Qed.
Hint Resolve add_choice_preserves_name_in_library : slow.

Lemma add_one_choice_preserves_name_in_library {o} :
  forall x name v (lib : @library o) n r lib',
    add_one_choice x v lib = Some (n, r, lib')
    -> name_in_library name lib
    -> name_in_library name lib'.
Proof.
  introv addc i.
  destruct lib as [lib c]; simpl in *.
  remember (add_choice x v lib) as addc'; symmetry in Heqaddc';
    destruct addc'; repnd; ginv; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_preserves_name_in_library : slow.

Lemma lib_extends_preserves_name_in_library {o} :
  forall (lib lib' : @library o) name,
    lib_extends lib' lib
    -> name_in_library name lib
    -> name_in_library name lib'.
Proof.
  introv ext; lib_ext_ind ext Case; introv h; tcsp; eauto 3 with slow.
  destruct (choice_sequence_name_deq name name0); subst; tcsp.
Qed.
Hint Resolve lib_extends_preserves_name_in_library : slow.



Lemma implies_member_nat2nat_bar {o} :
  forall uk lib (f : @CTerm o),
    in_open_bar
      lib
      (fun lib => forall m, {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member uk lib f nat2nat.
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.
  introv ext ea.

  eapply lib_extends_preserves_all_in_ex_bar in imp;[|eauto].
  clear lib ext.
  rename lib' into lib.

  apply equality_in_tnat in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact imp]; clear ea imp; introv ext ea imp.

  clear lib ext.
  rename lib' into  lib.
  unfold equality_of_nat in ea; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].

  apply equality_in_tnat.
  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  unfold equality_of_nat.
  pose proof (imp n) as imp; exrepnd.
  exists k; dands; spcast; eauto 4 with slow.
Qed.

Lemma implies_member_nat2nat_bar2 {o} :
  forall uk lib (f : @CTerm o),
    in_open_bar
      lib
      (fun lib =>
         forall m,
           in_open_bar
             lib
             (fun lib => {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}))
    -> member uk lib f nat2nat.
Proof.
  introv imp.
  apply equality_in_fun; dands; eauto 3 with slow.
  introv ext ea.

  eapply lib_extends_preserves_all_in_ex_bar in imp;[|eauto].
  clear lib ext.
  rename lib' into lib.

  apply equality_in_tnat in ea.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;[|exact ea|exact imp]; clear ea imp; introv ext ea imp.

  clear lib ext.
  rename lib' into  lib.
  unfold equality_of_nat in ea; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].

  pose proof (imp n) as imp; exrepnd.
  apply equality_in_tnat.
  eapply all_in_ex_bar_modus_ponens1;[|exact imp]; clear imp; introv ext imo; exrepnd; spcast.
  unfold equality_of_nat.
  exists k; dands; spcast; eauto 3 with slow.
Qed.

Lemma implies_member_nat2nat_bar2_iff {o} :
  forall uk lib (f : @CTerm o),
    in_open_bar
      lib
      (fun lib =>
         forall m,
           in_open_bar
             lib
             (fun lib => {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}))
    <=> member uk lib f nat2nat.
Proof.
  introv.
  split; introv h; try apply implies_member_nat2nat_bar2; auto.
  apply equality_in_fun in h; repnd.

  clear h0 h1.
  apply in_ext_implies_in_open_bar; introv ext; introv.
  pose proof (h _ ext) as h.
  pose proof (h (mkc_nat m) (mkc_nat m)) as h.
  autodimp h hyp; eauto 3 with slow;[].

  apply equality_in_tnat in h.
  eapply all_in_ex_bar_modus_ponens1; eauto; clear h; introv xt h.
  unfold equality_of_nat in h; exrepnd; GC; eauto.
Qed.

Lemma implies_member_nat2nat_bar2_iff2 {o} :
  forall uk lib (f : @CTerm o),
    (forall m,
        in_open_bar
          lib
          (fun lib => {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}))
    <=> member uk lib f nat2nat.
Proof.
  introv.
  rw <- @implies_member_nat2nat_bar2_iff; split; introv h.

  { apply in_ext_implies_in_open_bar; introv ext; introv.
    pose proof (h m) as h; eauto 3 with slow. }

  { introv.
    apply collapse_all_in_ex_bar.
    eapply all_in_ex_bar_modus_ponens1; eauto; clear h.
    introv ext h.
    pose proof (h m) as h; auto. }
Qed.

Lemma mkc_choice_seq_in_nat2nat {o} :
  forall uk (lib : @library o) (name : choice_sequence_name),
    compatible_choice_sequence_name 0 name
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> member uk lib (mkc_choice_seq name) nat2nat.
Proof.
  introv comp norep safe sat.
  apply implies_member_nat2nat_bar2.
  apply in_ext_implies_all_in_ex_bar.
  introv ext; introv.
  applydup compatible_choice_sequence_name_0_implies_is_primitive_kind in comp as isn.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib safe sat norep ext.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.
  rename m into k.

  (* first we need to add the sequence to the library *)
  introv ext.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  pose proof (exists_extend_library_lawless_upto_name_in name (S k) lib') as q.
  repeat (autodimp q hyp); exrepnd.
  assert (lib_extends lib'' lib') as xta by eauto 4 with slow.
  exists lib'' xta.
  introv xtb.
  simpl in * |-; exrepnd.
  assert (safe_library lib'') as safe'' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in q1; exrepnd.
  applydup safe'' in q1.

  pose proof (extend_library_lawless_upto_implies_exists_nats (lib_cond lib'') name lib'' lib'0 entry (S k)) as q.
  repeat (autodimp q hyp); exrepnd; try (complete (unfold extend_library_lawless_upto in *; tcsp));[].
  pose proof (q6 k (nth k vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; try lia|];[].
  unfold is_nat in w; exrepnd.
  assert (select k vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try lia. }

  exists i.
  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto.
Qed.

Lemma equality_in_csname_implies_equality_in_nat2nat {o} :
  forall uk (lib : library) (a b : @CTerm o),
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality uk lib a b (mkc_csname 0)
    -> equality uk lib a b nat2nat.
Proof.
  introv norep safe sat ecs.
  apply equality_in_csname in ecs.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ecs]; clear ecs; introv y ecs; exrepnd; spcast.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe sat norep.
  rename lib' into lib.

  unfold equality_of_csname in ecs; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym; introv x; spcast;
     apply ccomputes_to_valc_ext_implies_cequivc; eauto 3 with slow|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym; introv x; spcast;
     apply ccomputes_to_valc_ext_implies_cequivc; eauto 3 with slow|].

  rw @member_eq.
  clear dependent a.
  clear dependent b.

  apply mkc_choice_seq_in_nat2nat; eauto 3 with slow.
Qed.
Hint Resolve equality_in_csname_implies_equality_in_nat2nat : slow.

Lemma non_shadowed_entry_implies_not_in_lib {o} :
  forall e (lib : @library o),
    non_shadowed_entry e lib
    -> !in_lib (entry2name e) lib.
Proof.
  introv nsh i.
  unfold in_lib, non_shadowed_entry in *.
  allrw forallb_forall; exrepnd.
  applydup nsh in i1.
  unfold diff_entry_names in *; boolvar; tcsp.
Qed.
Hint Resolve non_shadowed_entry_implies_not_in_lib : slow.

Lemma implies_lib_extends_cons_left {o} :
  forall e (lib : @library o),
    safe_library_entry e
    -> non_shadowed_entry e lib
    -> lib_cond_sat_entry lib e
    -> lib_extends (add_one_entry e lib) lib.
Proof.
  introv safee allt sat.
  applydup @non_shadowed_entry_implies_not_in_lib in allt as ni.

  destruct e; simpl in *; eauto;
    try (complete (apply lib_extends_new_abs; eauto));[].
  destruct entry as [vals restr]; simpl in *; repnd.
  induction vals using rev_list_ind; simpl in *; eauto.

  { eapply lib_extends_new_cs; auto. }

  repeat (autodimp IHvals hyp); eauto 3 with slow.
  { introv i; apply sat0; apply in_snoc; tcsp. }
  eapply lib_extends_trans;[|eauto]; clear IHvals.
  destruct restr; simpl in *.

  { apply (lib_extends_cs _ name a (length vals) typ); tcsp.
    { simpl; boolvar; tcsp. }
    { apply safee; rewrite select_snoc_eq; boolvar; try lia; auto. }
    simpl; apply sat0; apply in_snoc; tcsp. }

(*  { apply (lib_extends_law _ name a (length vals) f); tcsp.
    { simpl; boolvar; tcsp. }
    pose proof (safee (length vals)) as safee; autorewrite with slow in *.
    autodimp safee hyp.
    rewrite select_snoc_eq in safee; boolvar; try lia; auto; inversion safee; auto. }

  { apply (lib_extends_res _ name a (length vals) typ); tcsp.
    { simpl; boolvar; tcsp. }
    apply safee; rewrite select_snoc_eq; boolvar; try lia; auto. }*)
Qed.
Hint Resolve implies_lib_extends_cons_left : slow.
