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

Fixpoint lib_free_from_choice_seq_name {o} (lib : @library o) (name : choice_sequence_name) :=
  match lib with
  | [] => True
  | e :: es =>
    (entry_free_from_choice_seq_name e name)
      # lib_free_from_choice_seq_name es name
  end.

Definition sequent_true_ex_ext {o} lib (s : @csequent o) :=
  {lib' : library & lib_extends lib' lib # sequent_true lib' s}.

Definition rule_true_ex_ext {o} lib (R : @rule o) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  forall cargs: args_constraints (sargs R) (hyps (goal R)),
  forall hyps : (forall s : baresequent,
                   LIn s (subgoals R)
                   -> {c : wf_csequent s & sequent_true lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & sequent_true_ex_ext lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.


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
Lemma tequality_mkc_tnat {o} : forall lib, @tequality o lib mkc_tnat mkc_tnat.
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
  forall lib (f g : @CTerm o) n,
    in_open_bar
      lib
      (fun lib =>
         forall m,
           m < n
           -> {k : nat
               , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
               # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality lib f g (natk2nat (mkc_nat n)).
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

  assert (m < n) as ltm by omega.
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
  forall lib (f : @CTerm o) n,
    in_open_bar
      lib
      (fun lib =>
         forall m,
           m < n
           -> {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member lib f (natk2nat (mkc_nat n)).
Proof.
  introv imp.
  apply implies_equality_natk2nat_bar.
  eapply all_in_ex_bar_modus_ponens1;try exact imp; clear imp; introv ext imp; exrepnd; spcast.
  introv ltm.
  apply imp in ltm; exrepnd.
  exists k; auto.
Qed.

Lemma name_in_library_implies_entry_in_library {o} :
  forall name (lib : @library o),
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

Lemma is_nat_or_seq_kind_implies_compatible_choice_sequence_name_0 :
  forall name,
    is_nat_or_seq_kind name
    -> compatible_choice_sequence_name 0 name.
Proof.
  introv h; destruct name as [name k]; simpl in *.
  unfold is_nat_or_seq_kind in *; simpl in *.
  unfold compatible_choice_sequence_name; simpl.
  unfold compatible_cs_kind; boolvar; tcsp.
Qed.
Hint Resolve is_nat_or_seq_kind_implies_compatible_choice_sequence_name_0 : slow.

Lemma compatible_choice_sequence_name_0_implies_is_nat_or_seq_kind :
  forall name,
    compatible_choice_sequence_name 0 name
    -> is_nat_or_seq_kind name.
Proof.
  introv h; destruct name as [name k]; simpl in *.
  unfold is_nat_or_seq_kind in *; simpl in *.
  unfold compatible_choice_sequence_name in *; simpl.
  unfold compatible_cs_kind in *; boolvar; tcsp.
Qed.
Hint Resolve compatible_choice_sequence_name_0_implies_is_nat_or_seq_kind : slow.

Hint Resolve entry_in_library_implies_find_cs_some : slow.

Lemma cs_entry_in_library_lawless_upto_implies_length_ge {o} :
  forall (lib lib' : @library o) name k vals restr,
    is_nat_or_seq_kind name
    -> correct_restriction name restr
    -> extend_library_lawless_upto lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> k <= length vals.
Proof.
  induction lib; introv isn cor ext ilib; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto;[].

  destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
  inversion ext0; clear ext0; subst; tcsp.

  - rewrite length_app; allrw; omega.

  - unfold correct_restriction in *; simpl in *.
    unfold is_nat_or_seq_kind in *.
    destruct name0 as [name kd]; simpl in *.
    destruct kd; subst; boolvar; tcsp; inversion cor.

  - unfold correct_restriction in *; simpl in *.
    unfold is_nat_or_seq_kind in *.
    destruct name0 as [name kd]; simpl in *.
    destruct kd; subst; boolvar; tcsp; inversion cor.
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

Lemma natSeq2restrictionPred_is_nat {o} :
  forall l n (v : @ChoiceSeqVal o),
    natSeq2restrictionPred l n v
    -> is_nat n v.
Proof.
  introv h.
  unfold natSeq2restrictionPred in *.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; subst; eauto 3 with slow.
Qed.
Hint Resolve natSeq2restrictionPred_is_nat : slow.

Lemma cs_entry_in_library_lawless_upto_implies_is_nat {o} :
  forall (lib lib' : @library o) name k vals restr n v,
    is_nat_or_seq_kind name
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> extend_library_lawless_upto lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> select n vals = Some v
    -> is_nat n v.
Proof.
  induction lib; introv isn cor sat ext ilib sel; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto;[].

  clear IHlib ext.

  destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
  inversion ext0; subst; clear ext0; tcsp.

  - unfold correct_restriction in *; simpl in *.
    destruct name0 as [name0 kd]; simpl in *.
    destruct kd; boolvar; tcsp; subst; GC; repnd.

    + unfold is_nat_restriction in *; inversion cor; subst; tcsp.

    + unfold is_nat_seq_restriction in *; inversion cor; subst; simpl in *.
      applydup sat in sel.
      destruct (lt_dec n (length l)) as [dd|dd]; eauto 3 with slow.

  - unfold correct_restriction in *.
    unfold is_nat_or_seq_kind in *.
    destruct name0 as [name kd]; simpl in *.
    destruct kd; subst; boolvar; tcsp; inversion cor.

  - unfold correct_restriction in *.
    subst.
    unfold is_nat_or_seq_kind in *.
    destruct name0 as [name kd]; simpl in *.
    destruct kd; subst; boolvar; tcsp; inversion cor.
Qed.
Hint Resolve cs_entry_in_library_lawless_upto_implies_is_nat : slow.

Lemma extend_library_lawless_upto_implies_exists_nats {o} :
  forall name (lib lib' : @library o) entry k,
    is_nat_or_seq_kind name
    -> entry_in_library entry lib
    -> entry2name entry = entry_name_cs name
    -> safe_library_entry entry
    -> extend_library_lawless_upto lib lib' name k
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

Hint Rewrite Nat2Z.id : slow.

Lemma choice_sequence_vals_extends_implies_select_some {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) m t,
    choice_sequence_vals_extend vals2 vals1
    -> select m vals1 = Some t
    -> select m vals2 = Some t.
Proof.
  introv h q; unfold choice_sequence_vals_extend in *; exrepnd; subst.
  rewrite select_app_l; eauto 3 with slow.
Qed.

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
  unfold compute_step_eapply; simpl; boolvar; try omega;[].
  autorewrite with slow.

  assert (lib_extends lib'0 lib) as e by eauto 3 with slow.
  clear dependent lib'.

  eapply lib_extends_preserves_find_cs in findcs;[|eauto].
  exrepnd; simpl in *.
  destruct entry2; simpl in *.
  unfold find_cs_value_at.
  allrw;simpl.
  rewrite find_value_of_cs_at_is_select.
  erewrite choice_sequence_vals_extends_implies_select_some; eauto; simpl; auto.
Qed.

Lemma extend_seq_to_ext {o} :
  forall (lib  : @library o)
         (norp : no_repeats_library lib)
         (safe : safe_library lib)
         (k    : nat)
         (name : choice_sequence_name)
         (isn  : is_nat_or_seq_kind name),
  exists lib' lib'',
    lib_extends lib' lib
    /\ name_in_library name lib''
    /\ extend_library_lawless_upto lib'' lib' name k.
Proof.
  introv norep safe isn.
  exists (add_cs_if_not_in name lib).
  pose proof (exists_extend_library_lawless_upto name k (add_cs_if_not_in name lib)) as q.
  repeat (autodimp q hyp); eauto 3 with slow;[].
  exrepnd.
  exists lib'; dands; eauto 3 with slow.
Qed.

Lemma mkc_choice_seq_in_natk2nat {o} :
  forall (lib : @library o) (name : choice_sequence_name) k,
    is_nat_or_seq_kind name
    -> no_repeats_library lib
    -> safe_library lib
    -> member lib (mkc_choice_seq name) (natk2nat (mkc_nat k)).
Proof.
  introv isn norep safe.
  apply implies_member_natk2nat_bar.

  (* first we need to add the sequence to the library *)
  introv ext.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (extend_seq_to_ext lib' norep' safe' k name isn) as q; exrepnd.
  assert (lib_extends lib'' lib') as xta by eauto 4 with slow.
  exists lib'' xta.
  introv xtb ltm.
  simpl in * |-; exrepnd.
  assert (safe_library lib'') as safe'' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in q2; exrepnd.
  applydup safe'' in q2.

  pose proof (extend_library_lawless_upto_implies_exists_nats name lib'' lib'0 entry k) as q.
  repeat (autodimp q hyp); exrepnd.
  pose proof (q6 m (nth m vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; omega|];[].
  unfold is_nat in w; exrepnd.
  assert (select m vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try omega. }

  exists i.
  spcast.
  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto.
Qed.


Lemma equality_in_csname_implies_equality_in_natk2nat {o} :
  forall lib (a b t : @CTerm o) k,
    safe_library lib
    -> no_repeats_library lib
    -> ccomputes_to_valc_ext lib t (mkc_nat k)
    -> equality lib a b (mkc_csname 0)
    -> equality lib a b (natk2nat t).
Proof.
  introv safe norep comp ecs.
  apply equality_in_csname in ecs.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ecs]; clear ecs; introv y ecs; exrepnd; spcast.
  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe norep.
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
  apply cequiv_refl; compute; fold_terms; dands; eauto 3 with slow.
Qed.

(*Lemma nat2all_in_ex_bar2bar {o} :
  forall (n   : nat)
         (lib : @library o)
         (f   : nat -> library -> Prop)
         (F   : forall m, m < n -> all_in_ex_bar lib (f m)),
    {b : BarLib lib , forall m, m < n -> all_in_bar b (f m)}.
Proof.
  induction n; introv F.

  { exists (trivial_bar lib); introv h; omega. }

  pose proof (IHn lib f) as q.
  autodimp q hyp;[].
  exrepnd.
  pose proof (F n) as w; autodimp w hyp.
  unfold all_in_ex_bar in w; exrepnd.
  exists (intersect_bars b bar).
  introv ltn br ext; simpl in *; exrepnd.
  destruct (lt_dec m n) as [d|d].

  { eapply q0; eauto 3 with slow. }

  { assert (m = n) as xx by omega; subst.
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

  { apply in_ext_implies_in_open_bar; introv ext h; omega. }

  pose proof (IHn lib f) as q; clear IHn.
  autodimp q hyp;[].
  pose proof (F n) as w; autodimp w hyp; []; clear F.
  eapply in_open_bar_comb; try exact q; clear q.
  eapply in_open_bar_pres; try exact w; clear w; introv ext w q h.
  destruct (lt_dec m n) as [d|d]; eauto;[].
  assert (m = n) as xx by omega; subst; auto.
Qed.

Lemma equality_natk2nat_implies2 {o} :
  forall lib (f g : @CTerm o) n,
    equality lib f g (natk2nat (mkc_nat n))
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
  forall lib (A : @CTerm o),
    in_open_bar lib (fun lib => inhabited_type_bar lib A)
    -> inhabited_type_bar lib A.
Proof.
  introv h.
  unfold inhabited_type_bar in *.
  apply collapse_all_in_ex_bar in h; auto.
Qed.
Hint Resolve all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar : slow.


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
  pose proof (h k) as h; autodimp h hyp; try omega; exrepnd.

  exists (snoc l k0); autorewrite with slow; dands; auto.
  introv h; simpl in *.
  rewrite select_snoc_eq in h.
  boolvar; tcsp; ginv; auto.
Qed.

Lemma fresh_choice_seq_name_in_library {o} :
  forall (lib : @library o) (l : list nat),
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

Lemma csn_kind_seq_implies_is_nat_or_seq_kind :
  forall name l,
    csn_kind name = cs_kind_seq l
    -> is_nat_or_seq_kind name.
Proof.
  introv h.
  unfold is_nat_or_seq_kind.
  allrw; simpl; auto.
Qed.
Hint Resolve csn_kind_seq_implies_is_nat_or_seq_kind : slow.

Lemma implies_equality_natk2nat_prop {o} :
  forall lib (f g : @CTerm o) n,
    (forall m,
       m < n
       -> {k : nat
           , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
           # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})
    -> equality lib f g (natk2nat (mkc_nat n)).
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

  assert (m < n) as ltm by omega.
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
  unfold is_nat_seq_restriction in *; subst; simpl in *.
  split; intro h.

  - remember (select n vals) as s; symmetry in Heqs; destruct s.

    + applydup sat in Heqs.
      unfold natSeq2restrictionPred in Heqs0.
      rewrite h in Heqs0; subst; auto.

    + apply nth_select2 in Heqs; omega.

  - applydup sat in h.
    unfold natSeq2restrictionPred in h0.
    remember (select n l) as sel; symmetry in Heqsel; destruct sel; tcsp.
    { apply mkc_nat_eq_implies in h0; subst; auto. }
    apply nth_select2 in Heqsel; try omega.
Qed.

Lemma exists_extend_library_lawless_upto_name_in {o} :
  forall name n (lib : @library o),
    is_nat_or_seq_kind name
    -> safe_library lib
    ->
    exists lib'' lib',
      extend_library_lawless_upto lib'' lib' name n
      /\ lib_extends lib' lib
      /\ name_in_library name lib''.
Proof.
  introv isns safe.
  pose proof (exists_extend_library_with_name (library2inf lib inf_lib_entry_0) name lib) as h.
  repeat (autodimp h hyp); eauto 3 with slow;[].
  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (exists_extend_library_lawless_upto_following_infinite (library2inf lib' inf_lib_entry_0) name n lib') as q.
  repeat (autodimp q hyp); eauto 3 with slow;[].
  exrepnd.
  exists lib'0 lib'; dands; eauto 3 with slow.
Qed.

Lemma name_in_library_if_entry_in_library {o} :
  forall name entry (lib : @library o),
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
  introv h.
  destruct entry1, entry2; simpl in *; repnd; subst; tcsp; ginv.
  inversion h; subst; tcsp.
Qed.

Lemma in_lib_cs_cons_iff {o} :
  forall name e (lib : @library o),
    in_lib (entry_name_cs name) (e :: lib)
    <-> (entry2name e = entry_name_cs name \/ in_lib (entry_name_cs name) lib).
Proof.
  introv; unfold in_lib; simpl; split; intro h; exrepnd; repndors; subst; tcsp.

  { destruct e0; simpl in *; subst; tcsp. }

  { destruct e0; simpl in *; subst; tcsp.
    right; eexists; dands; eauto; simpl; auto. }

  { exists e; dands; tcsp.
    destruct e; simpl in *; ginv; auto. }

  { exrepnd; eexists; dands; eauto. }
Qed.

Lemma name_in_library_as_in_lib {o} :
  forall name (lib : @library o),
    name_in_library name lib <-> in_lib (entry_name_cs name) lib.
Proof.
  induction lib; introv; split; intro h; simpl in *; tcsp.
  { unfold in_lib in h; simpl in *; exrepnd; tcsp. }
  { apply in_lib_cs_cons_iff.
    repndors; repnd; tcsp.
    { destruct a; simpl in *; subst; tcsp. }
    { apply IHlib in h; tcsp. } }
  { apply in_lib_cs_cons_iff in h; repndors; subst; tcsp.
    { allrw; tcsp. }
    { apply IHlib in h; destruct a; simpl in *; tcsp.
      destruct (choice_sequence_name_deq name name0); subst; tcsp. } }
Qed.

Lemma entry_extends_preserves_same_entry_name_right {o} :
  forall (e1 e2 : @library_entry o) name,
    entry_extends e2 e1
    -> same_entry_name (entry_name_cs name) (entry2name e1)
    -> same_entry_name (entry_name_cs name) (entry2name e2).
Proof.
  introv ext same.
  destruct e1, e2; simpl in *; repnd; subst; tcsp; ginv.
Qed.

Lemma lib_extends_preserves_name_in_library {o} :
  forall (lib lib' : @library o) name,
    lib_extends lib' lib
    -> name_in_library name lib
    -> name_in_library name lib'.
Proof.
  introv ext i.
  allrw @name_in_library_as_in_lib; eauto 3 with slow.
  apply implies_lib_extends_sub in ext.
  unfold in_lib in *; exrepnd.
  apply ext in i1; exrepnd.
  eexists; dands; eauto.
  eapply entry_extends_preserves_same_entry_name_right; eauto.
Qed.
Hint Resolve lib_extends_preserves_name_in_library : slow.



Lemma implies_member_nat2nat_bar {o} :
  forall lib (f : @CTerm o),
    in_open_bar
      lib
      (fun lib => forall m, {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)})
    -> member lib f nat2nat.
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
  forall lib (f : @CTerm o),
    in_open_bar
      lib
      (fun lib =>
         forall m,
           in_open_bar
             lib
             (fun lib => {k : nat , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)}))
    -> member lib f nat2nat.
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

Lemma mkc_choice_seq_in_nat2nat {o} :
  forall (lib : @library o) (name : choice_sequence_name),
    is_nat_or_seq_kind name
    -> no_repeats_library lib
    -> safe_library lib
    -> member lib (mkc_choice_seq name) nat2nat.
Proof.
  introv isn norep safe.
  apply implies_member_nat2nat_bar2.
  apply in_ext_implies_all_in_ex_bar.
  introv ext; introv.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib safe norep ext.
  rename lib' into lib; rename safe' into safe; rename norep' into norep.
  rename m into k.

  (* first we need to add the sequence to the library *)
  introv ext.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (extend_seq_to_ext lib' norep' safe' (S k) name isn) as q; exrepnd.
  assert (lib_extends lib'' lib') as xta by eauto 4 with slow.
  exists lib'' xta.
  introv xtb.
  simpl in * |-; exrepnd.
  assert (safe_library lib'') as safe'' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in q2; exrepnd.
  applydup safe'' in q2.

  pose proof (extend_library_lawless_upto_implies_exists_nats name lib'' lib'0 entry (S k)) as q.
  repeat (autodimp q hyp); exrepnd;[].
  pose proof (q6 k (nth k vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; try omega|];[].
  unfold is_nat in w; exrepnd.
  assert (select k vals = Some (mkc_nat i)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try omega. }

  exists i.
  eapply implies_mkc_apply_mkc_choice_seq_ccomputes_to_valc_ext; eauto.
Qed.

Lemma equality_in_csname_implies_equality_in_nat2nat {o} :
  forall lib (a b : @CTerm o),
    safe_library lib
    -> no_repeats_library lib
    -> equality lib a b (mkc_csname 0)
    -> equality lib a b nat2nat.
Proof.
  introv safe norep ecs.
  apply equality_in_csname in ecs.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact ecs]; clear ecs; introv y ecs; exrepnd; spcast.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  clear lib y safe norep.
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
