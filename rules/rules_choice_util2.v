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



Definition nat2bool {o} := @mkc_fun o mkc_tnat mkc_bool.

Definition mk_nat2bool {o} : @NTerm o := mk_fun mk_tnat mk_bool.

Lemma lsubstc_mk_nat2bool {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_nat2bool w s c) nat2bool.
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 2 with slow.

  simpl.

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  fold_terms.
  auto.
Qed.

Lemma type_nat2bool {o} :
  forall (lib : @library o), type lib nat2bool.
Proof.
  introv.
  unfold nat2bool.
  apply type_mkc_fun; dands; eauto 3 with slow.
  introv ext inh; apply tequality_bool.
Qed.
Hint Resolve type_nat2bool : slow.

Lemma tequality_nat2bool {o} :
  forall (lib : @library o),
    tequality lib nat2bool nat2bool.
Proof.
  introv.
  apply type_nat2bool.
Qed.
Hint Resolve tequality_nat2bool : slow.

Lemma equality_nat2bool_apply {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2bool
    -> equality lib a b mkc_tnat
    -> equality lib (mkc_apply f a) (mkc_apply g b) mkc_bool.
Proof.
  introv eqf eqn.
  unfold nat2bool in eqf.
  apply equality_in_fun in eqf; repnd.
  apply eqf in eqn; auto; eauto 3 with slow.
Qed.

Ltac aeq_lsubstc_vars_not h :=
  match goal with
  | [ |- context[lsubstc_vars (mk_fun ?t1 ?t2) ?w ?s ?vs ?c] ] =>
    let w1 := fresh "w1" in
    let w2 := fresh "w2" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    pose proof (lsubstc_vars_mk_fun_as_mkcv t1 t2 w s vs c) as h;
    destruct h as [w1 h];
    destruct h as [w2 h];
    destruct h as [c1 h];
    destruct h as [c2 h]

  | [ H : context[lsubstc_vars (mk_fun ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
    let w1 := fresh "w1" in
    let w2 := fresh "w2" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    pose proof (lsubstc_vars_mk_fun_as_mkcv t1 t2 w s vs c) as h;
    destruct h as [w1 h];
    destruct h as [w2 h];
    destruct h as [c1 h];
    destruct h as [c2 h]
  end.

Lemma substc2_not {o} :
  forall (v x : NVar) (w : @CTerm o) (a : CVTerm [v, x]),
    substc2 v w x (mkcv_not [v, x] a)
    = mkcv_not [v] (substc2 v w x a).
Proof.
  introv; destruct_cterms; simpl.
  apply cvterm_eq; simpl.
  repeat unfsubst; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @substc2_not : slow.

Lemma substc2_assert {o} :
  forall (v x : NVar) (w : @CTerm o) (a : CVTerm [v, x]),
    substc2 v w x (mkcv_assert [v, x] a)
    = mkcv_assert [v] (substc2 v w x a).
Proof.
  introv; destruct_cterms; simpl.
  apply cvterm_eq; simpl.
  repeat unfsubst; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @substc2_assert : slow.

Hint Rewrite @mkcv_apply_substc : slow.
Hint Rewrite @substc2_apply : slow.

Lemma mkcv_assert_substc {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_assert [v] a)
    = mkc_assert (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfold mk_assert.
  repeat unfsubst; simpl; fold_terms.
  allrw @sub_filter_nil_r.
  repeat (rw memvar_singleton; boolvar; allsimpl; tcsp).
  boolvar; tcsp.
Qed.
Hint Rewrite @mkcv_assert_substc : slow.

Lemma ccequivc_ext_mkc_inl_if {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_inl a) (mkc_inl b).
Proof.
  introv ceq ext.
  apply ceq in ext; spcast.
  apply cequivc_mkc_inl_if; auto.
Qed.
Hint Resolve ccequivc_ext_mkc_inl_if : slow.

Lemma ccequivc_ext_mkc_inr_if {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_inr a) (mkc_inr b).
Proof.
  introv ceq ext.
  apply ceq in ext; spcast.
  apply cequivc_mkc_inr_if; auto.
Qed.
Hint Resolve ccequivc_ext_mkc_inr_if : slow.

Lemma equality_in_bool_ext {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_bool
             <=>
             all_in_ex_bar lib (fun lib =>
                                  (ccequivc_ext lib a tt # ccequivc_ext lib b tt)
                                    {+}
                                    (ccequivc_ext lib a ff # ccequivc_ext lib b ff)
                               ).
Proof.
  introv.
  allrw <- @fold_mkc_bool.
  rw @equality_mkc_union; split; intro k; repnd; dands; eauto 3 with slow;[|].

  - apply collapse_all_in_ex_bar.
    eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast.
    exrepnd; repndors; exrepnd; spcast.

    + allrw @equality_in_unit; repnd.
      eapply all_in_ex_bar_modus_ponens1;try exact k3; clear k3; introv y k3; exrepnd; spcast.
      eapply lib_extends_preserves_computes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_computes_to_valc in k4;[|exact y].
      left; dands; spcast.

      * allapply @computes_to_valc_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 a (mkc_inl a1) tt); eauto 3 with slow.

      * allapply @computes_to_valc_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 b (mkc_inl a2) tt); eauto 3 with slow.

    + allrw @equality_in_unit; repnd.
      eapply all_in_ex_bar_modus_ponens1;try exact k3; clear k3; introv y k3; exrepnd; spcast.
      eapply lib_extends_preserves_computes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_computes_to_valc in k4;[|exact y].
      right; dands; spcast.

      * allapply @computes_to_valc_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 a (mkc_inr b1) ff); eauto 3 with slow.

      * allapply @computes_to_valc_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 b (mkc_inr b2) ff); eauto 3 with slow.

  - eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast.
    repndors; repnd; spcast;[left|right].

    + apply ccequivc_ext_sym in k0.
      apply ccequivc_ext_sym in k.
      pose proof (k0 _ (lib_extends_refl _)) as k0.
      pose proof (k _ (lib_extends_refl _)) as k.
      simpl in *; spcast.
      apply cequivc_mkc_inl_implies in k0.
      apply cequivc_mkc_inl_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply implies_equality_in_unit; spcast; apply cequivc_axiom_implies; sp.

    + apply ccequivc_ext_sym in k0.
      apply ccequivc_ext_sym in k.
      pose proof (k0 _ (lib_extends_refl _)) as k0.
      pose proof (k _ (lib_extends_refl _)) as k.
      simpl in *; spcast.
      apply cequivc_mkc_inr_implies in k0.
      apply cequivc_mkc_inr_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply implies_equality_in_unit; spcast; apply cequivc_axiom_implies; sp.
Qed.

Lemma implies_ccequivc_ext_assert {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_assert a) (mkc_assert b).
Proof.
  introv ceq ext; apply ceq in ext; spcast; clear ceq.
  repeat (rw @mkc_assert_eq).
  repeat (rw @mkc_ite_eq_mkc_decide).
  destruct_cterms; unfold cequivc in *; simpl in *.
  apply cequiv_congruence; fold_terms;
    try (complete (apply isprogram_decide_iff2; dands; eauto 3 with slow));[].

  {
    unfold cequiv_bts, lblift; simpl; dands; auto.
    introv h.
    repeat (destruct n; tcsp; try omega); unfold selectbt; simpl.

    - unfold blift.
      exists ([] : list NVar) x0 x; dands; eauto 3 with slow.
      apply cequiv_implies_cequiv_open; auto.

    - exists [nvarx] (@mk_unit o) (@mk_unit o); dands; eauto 3 with slow.

    - exists [nvarx] (@mk_void o) (@mk_void o); dands; eauto 3 with slow.
  }
Qed.
Hint Resolve implies_ccequivc_ext_assert : slow.

Lemma mkc_assert_ff {o} :
  forall (lib : @library o), cequivc lib (mkc_assert ff) mkc_void.
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_mk_assert.
  apply isprogram_inr; eauto with slow.
Qed.

Lemma ccequivc_mkc_assert_tt {o} :
  forall (lib : @library o),
    ccequivc_ext lib (mkc_assert tt) mkc_unit.
Proof.
  introv ext; spcast; apply mkc_assert_tt.
Qed.

Lemma ccequivc_mkc_assert_ff {o} :
  forall (lib : @library o),
    ccequivc_ext lib (mkc_assert ff) mkc_void.
Proof.
  introv ext; spcast; apply mkc_assert_ff.
Qed.

Lemma equality_in_bool_implies_tequality {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_bool
    -> tequality lib (mkc_assert a) (mkc_assert b).
Proof.
  introv eb.
  apply equality_in_bool_ext in eb.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply all_in_ex_bar_modus_ponens1;[|exact eb]; clear eb; introv y eb; exrepnd; spcast.
  repndors; repnd; spcast.

  { eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_assert;eauto|].
    eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_assert;eauto|].
    eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym;apply ccequivc_mkc_assert_tt|].
    eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_mkc_assert_tt|].
    eauto 3 with slow. }

  { eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_assert;eauto|].
    eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_assert;eauto|].
    eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym;apply ccequivc_mkc_assert_ff|].
    eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_mkc_assert_ff|].
    eauto 3 with slow. }
Qed.
Hint Resolve equality_in_bool_implies_tequality : slow.

Lemma tequality_assert_apply_nat2bool {o} :
  forall lib (f g a b : @CTerm o),
    equality lib f g nat2bool
    -> equality lib a b mkc_tnat
    -> tequality lib (mkc_assert (mkc_apply f a)) (mkc_assert (mkc_apply g b)).
Proof.
  introv ef en.
  eapply equality_nat2bool_apply in ef;[|exact en]; eauto 3 with slow.
Qed.
Hint Resolve tequality_assert_apply_nat2bool : slow.

Definition bool_choice_seq_entry {o} : @ChoiceSeqEntry o :=
  MkChoiceSeqEntry _ [] csc_bool.

Definition bool_choice_sequence_entry {o} (name : choice_sequence_name) : @library_entry o :=
  lib_cs name bool_choice_seq_entry.

Lemma fresh_choice_seq_name_in_library_nat {o} :
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

Lemma find_cs_none_implies_diff_entry_names_bool {o} :
  forall name (e : @library_entry o) lib,
    find_cs lib name = None
    -> List.In e lib
    -> diff_entry_names (bool_choice_sequence_entry name) e = true.
Proof.
  induction lib; introv f i; simpl; tcsp.
  simpl in *; repndors; subst; tcsp.

  - destruct e; simpl in *; ginv.
    boolvar; subst; tcsp.
    unfold diff_entry_names; simpl; boolvar;tcsp.

  - destruct a; simpl in *; tcsp.
    boolvar; subst; tcsp.
Qed.
Hint Resolve find_cs_none_implies_diff_entry_names_bool : slow.

Lemma find_cs_none_implies_non_shadowed_entry_bool_choice_sequence_entry {o} :
  forall name (lib : @library o),
    find_cs lib name = None
    -> non_shadowed_entry (bool_choice_sequence_entry name) lib.
Proof.
  introv f.
  unfold non_shadowed_entry.
  rewrite forallb_forall; introv i; eauto 3 with slow.
Qed.
Hint Resolve find_cs_none_implies_non_shadowed_entry_bool_choice_sequence_entry : slow.

Lemma correct_restriction_csc_bool {o} :
  forall name,
    csn_kind name = cs_kind_nat 1
    -> @correct_restriction o name csc_bool.
Proof.
  introv csk; unfold correct_restriction; simpl; allrw; simpl; auto; dands; tcsp.
Qed.
Hint Resolve correct_restriction_csc_bool : slow.

Lemma safe_library_entry_bool_choice_sequence_entry {o} :
  forall name,
    csn_kind name = cs_kind_nat 1
    -> @safe_library_entry o (bool_choice_sequence_entry name).
Proof.
  introv csk.
  unfold safe_library_entry; simpl; dands; eauto 3 with slow; tcsp.
  introv h; autorewrite with slow in *; ginv.
Qed.
Hint Resolve safe_library_entry_bool_choice_sequence_entry : slow.

Lemma lib_extends_cons_bool_choice_sequence_entry {o} :
  forall name (lib : @library o),
    csn_kind name = cs_kind_nat 1
    -> find_cs lib name = None
    -> lib_extends (bool_choice_sequence_entry name :: lib) lib.
Proof.
  introv csk fcs.
  apply implies_lib_extends_cons_left; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_cons_bool_choice_sequence_entry : slow.

Definition mkcv_bool {o} vs : @CVTerm o vs := mk_cv _ mkc_bool.
Definition mkcv_ff {o} vs : @CVTerm o vs := mk_cv _ ff.

Definition exists_ff_choice {o} (a : choice_sequence_name) (n : NVar) : @CTerm o :=
  mkc_exists
    mkc_bool
    n
    (mkcv_equality
       _
       (mkcv_apply _ (mkcv_choice_seq _ a) (mkc_var n))
       (mkcv_ff _)
       (mkcv_bool _)).

Lemma type_bool {o} : forall lib, @type o lib mkc_bool.
Proof.
  introv; apply tequality_bool.
Qed.
Hint Resolve type_bool : slow.

Lemma implies_member_nat2bool_bar2 {o} :
  forall lib (f : @CTerm o),
    all_in_ex_bar
      lib
      (fun lib =>
         forall m,
           all_in_ex_bar
             lib
             (fun lib => {b : bool , ccomputes_to_valc lib (mkc_apply f (mkc_nat m)) (mkc_boolean b)}))
    -> member lib f nat2bool.
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
  unfold per_props_nat.equality_of_nat in ea; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply computes_to_valc_implies_ccequivc_ext;eauto]
    |].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply computes_to_valc_implies_ccequivc_ext;eauto]
    |].

  pose proof (imp k) as imp; exrepnd.
  apply equality_in_bool.
  eapply all_in_ex_bar_modus_ponens1;[|exact imp]; clear imp; introv ext imo; exrepnd; spcast.
  unfold equality_of_nat.
  destruct b; simpl in *;[left|right]; dands; spcast; eauto 3 with slow;
    try (complete (apply computes_to_valc_implies_cequivc; auto)).
Qed.

Lemma compatible_choice_sequence_name_1_implies_is_primitive_kind :
  forall name,
    compatible_choice_sequence_name 1 name
    -> is_primitive_kind name.
Proof.
  introv h; destruct name as [name k]; simpl in *.
  unfold is_primitive_kind in *; simpl in *.
  unfold compatible_choice_sequence_name in *; simpl.
  unfold compatible_cs_kind in *; boolvar; tcsp.
  simpl in *; GC; destruct k; subst; tcsp.
Qed.
Hint Resolve compatible_choice_sequence_name_1_implies_is_primitive_kind : slow.

Lemma cs_entry_in_library_bool_seq_upto_implies_is_bool {o} :
  forall (lib lib' : @library o) name k vals restr n v,
    compatible_choice_sequence_name 1 name
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> extend_library_lawless_upto lib lib' name k
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals restr)) lib
    -> select n vals = Some v
    -> is_bool n v.
Proof.
  induction lib; introv isn cor sat ext ilib sel; simpl in *; tcsp.
  destruct lib'; simpl in *; tcsp; repnd.
  repndors; repnd; subst; simpl in *; eauto;[].

  clear IHlib ext.

  destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; GC.
  destruct restr; tcsp.

  - destruct entry.
    destruct cse_restriction; repnd; exrepnd; subst; ginv;[].
    unfold correct_restriction in *; simpl in *.
    destruct name0 as [name0 kd]; simpl in *.
    destruct kd; boolvar; tcsp; subst; GC; repnd.

    + unfold compatible_choice_sequence_name in *; simpl in *.
      unfold compatible_cs_kind in *; simpl in *; ginv.

    + apply sat in sel.
      apply cor in sel; auto.

    + apply sat in sel.
      destruct (lt_dec n (length l)) as [dd|dd].

      * unfold compatible_choice_sequence_name in *; simpl in *.
        unfold compatible_cs_kind in *; simpl in *; ginv; tcsp.

      * unfold compatible_choice_sequence_name in *; simpl in *.
        unfold compatible_cs_kind in *; simpl in *; ginv; tcsp.

  - unfold correct_restriction in *.
    subst.
    unfold is_primitive_kind in *.
    destruct name0 as [name kd]; simpl in *.
    destruct kd; subst; boolvar; tcsp.
Qed.
Hint Resolve cs_entry_in_library_bool_seq_upto_implies_is_bool : slow.

Lemma extend_library_bool_seq_upto_implies_exists_nats {o} :
  forall name (lib lib' : @library o) entry k,
    compatible_choice_sequence_name 1 name
    -> entry_in_library entry lib
    -> entry2name entry = entry_name_cs name
    -> safe_library_entry entry
    -> extend_library_lawless_upto lib lib' name k
    -> exists vals restr,
        find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
        /\ k <= length vals
        /\ forall n v, select n vals = Some v -> is_bool n v.
Proof.
  introv isn ilib eqname safe ext.
  destruct entry; simpl in *; tcsp; ginv;[].
  destruct entry as [vals restr]; simpl in *; repnd.
  exists vals restr.
  dands; eauto 3 with slow.
Qed.

Lemma iscvalue_get_cterm_mkc_boolean {o} :
  forall b, @isvalue o (get_cterm (mkc_boolean b)).
Proof.
  introv; destruct b; repeat constructor; simpl; introv h; repndors; subst; tcsp;
    repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_get_cterm_mkc_boolean : slow.

Lemma mkc_choice_seq_in_nat2bool {o} :
  forall (lib : @library o) (name : choice_sequence_name),
    compatible_choice_sequence_name 1 name
    -> safe_library lib
    -> member lib (mkc_choice_seq name) nat2bool.
Proof.
  introv isn safe.
  apply implies_member_nat2bool_bar2.
  apply in_ext_implies_all_in_ex_bar.
  introv ext; introv.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.
  rename m into k.

  (* first we need to add the sequence to the library *)
  exists (extend_seq_to_bar lib safe (S k) name (compatible_choice_sequence_name_1_implies_is_primitive_kind _ isn)).

  introv br ext.
  simpl in * |-; exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  apply name_in_library_implies_entry_in_library in br2; exrepnd.
  applydup safe' in br2.

  pose proof (extend_library_bool_seq_upto_implies_exists_nats name lib' lib'' entry (S k)) as q.
  repeat (autodimp q hyp); exrepnd;[].
  pose proof (q1 k (nth k vals mkc_zero)) as w.
  autodimp w hyp;[apply nth_select1; try omega|];[].
  unfold is_bool in w; exrepnd.
  assert (select k vals = Some (mkc_boolean b)) as xx.
  { eapply nth_select3; eauto; unfold ChoiceSeqVal in *; try omega. }

  exists b.
  spcast.
  unfold computes_to_valc; simpl.
  split; eauto 3 with slow.
  eapply reduces_to_if_split2;[csunf; simpl; reflexivity|].
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_eapply; simpl; boolvar; try omega;[].
  autorewrite with slow.

  eapply lib_extends_preserves_find_cs in q0;[|eauto].
  exrepnd; simpl in *.
  destruct entry2; simpl in *.
  unfold find_cs_value_at.
  allrw;simpl.
  rewrite find_value_of_cs_at_is_select.
  erewrite choice_sequence_vals_extends_implies_select_some; eauto; simpl; auto.
Qed.
Hint Resolve mkc_choice_seq_in_nat2bool : slow.

Lemma mkc_choice_seq_equality_in_nat2bool {o} :
  forall (lib : @library o) (name : choice_sequence_name),
    compatible_choice_sequence_name 1 name
    -> safe_library lib
    -> equality lib (mkc_choice_seq name) (mkc_choice_seq name) nat2bool.
Proof.
  introv comp safe; apply mkc_choice_seq_in_nat2bool; auto.
Qed.
Hint Resolve mkc_choice_seq_equality_in_nat2bool : slow.

Lemma implies_compatible_choice_sequence_name :
  forall name,
    csn_kind name = cs_kind_nat 1
    -> compatible_choice_sequence_name 1 name.
Proof.
  introv h.
  unfold compatible_choice_sequence_name; simpl.
  unfold compatible_cs_kind; simpl; allrw; auto.
Qed.
Hint Resolve implies_compatible_choice_sequence_name : slow.

Lemma extends_bool_choice_sequence_entry {o} :
  forall (lib lib' : @library o) name,
    safe_library lib
    -> lib_extends lib' lib
    -> entry_in_library (bool_choice_sequence_entry name) lib
    -> exists (bs : list bool) restr,
        same_restrictions restr csc_bool
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean bs) restr)) lib'.
Proof.
  introv safe ext i.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  apply ext in i; clear ext.
  clear dependent lib.
  apply entry_in_library_extends_implies_entry_in_library in i; exrepnd.
  eapply entry_in_library_implies_safe_library_entry in safe';[|eauto].
  unfold entry_extends in i0.
  destruct entry'; simpl in *; tcsp; ginv;[].
  repnd; subst.
  unfold choice_sequence_entry_extend in *; repnd; simpl in *.
  unfold choice_sequence_vals_extend in *; simpl in *; exrepnd; subst; simpl in *.
  destruct entry as [vals restr]; simpl in *.
  repnd.
  unfold same_restrictions in i2.
  destruct restr; simpl in *; tcsp;[].
  repnd.

  assert (forall v, LIn v vals -> exists (b : bool), v = mkc_boolean b) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe' n v) as q.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    eapply i2; eauto.
  }
  clear safe' safe'0.

  assert (exists l, vals = map mkc_boolean l) as h.
  {
    clear i1.
    induction vals; simpl in *; tcsp.
    - exists ([] : list bool); simpl; auto.
    - autodimp IHvals hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (b :: l); simpl; auto.
  }

  exrepnd; subst.
  exists l (csc_type d typ typd); simpl; dands; tcsp.
Qed.

Lemma is_bool_mkc_boolean {o} :
  forall n b, @is_bool o n (mkc_boolean b).
Proof.
  introv; exists b; auto.
Qed.
Hint Resolve is_bool_mkc_boolean : slow.

Lemma eq_maps_entry2name_implies_eq_forallb_diff {o} :
  forall (lib lib' : @library o) a,
    map entry2name lib = map entry2name lib'
    -> forallb (diff_entry_names a) lib = forallb (diff_entry_names a) lib'.
Proof.
  induction lib; introv h; simpl in *; destruct lib'; simpl in *; ginv.
  inversion h.
  pose proof (IHlib lib' a0) as IHlib; autodimp IHlib hyp; allrw.
  unfold diff_entry_names; allrw; tcsp.
Qed.
Hint Resolve eq_maps_entry2name_implies_eq_forallb_diff : slow.

Lemma extends_bool_choice_sequence_entry2 {o} :
  forall (lib : @library o) name restr bs,
    safe_library lib
    -> correct_restriction name restr
    -> same_restrictions restr csc_bool
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean bs) restr)) lib
    -> exists lib',
        lib_extends lib' lib
        /\ map entry2name lib' = map entry2name lib
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean (snoc bs true)) restr)) lib'.
Proof.
  induction lib using rev_list_ind; introv safe cor same i; simpl in *; tcsp.

  apply entry_in_library_snoc_implies in i; repndors; repnd.

  {
    apply IHlib in i; auto; exrepnd; eauto 3 with slow.
    exists (snoc lib' a); dands; simpl; tcsp; eauto 3 with slow.

    - remember (forallb (diff_entry_names a) lib') as b; symmetry in Heqb.
      destruct b.

      + apply implies_lib_extends_snoc_lr_if_all_diff; auto.

      + apply lib_extends_snoc_lr_if_all_diff_false; auto.
        unfold shadowed_entry.
        rewrite <- Heqb; symmetry; eauto 3 with slow.

    - allrw map_snoc; allrw; auto.
  }

  {
    exists (snoc lib (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean (snoc bs true)) restr))).
    simpl; dands; tcsp; eauto 3 with slow; allrw map_snoc; simpl; subst; simpl in *; tcsp.

    apply implies_lib_extends_snoc; simpl; auto; dands; auto.

    - unfold choice_sequence_satisfies_restriction; simpl.
      destruct restr; simpl in *; repnd; introv j; tcsp;[].

      apply same.
      rewrite select_snoc_eq in j.
      allrw map_length; boolvar; tcsp; ginv; eauto 3 with slow.

      rewrite select_map in j.
      remember (select n bs) as sel; symmetry in Heqsel; destruct sel; ginv.
      boolvar; tcsp; eauto 3 with slow.

    - unfold choice_sequence_entry_extend; simpl; dands; eauto 3 with slow.
      unfold choice_sequence_vals_extend.
      exists [@mkc_boolean o true].
      rewrite snoc_as_append; auto.
  }
Qed.

Lemma iscvalue_tt {o} : @iscvalue o tt.
Proof.
  repeat constructor; simpl; introv h; repndors; tcsp; subst; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_tt : slow.

Lemma entry_extends_bool_choice_sequence_entry {o} :
  forall (entry : @library_entry o) name,
    safe_library_entry entry
    -> csn_kind name = cs_kind_nat 1
    -> entry_extends entry (bool_choice_sequence_entry name)
    -> exists l restr,
        entry = lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean l) restr)
        /\ same_restrictions restr csc_bool.
Proof.
  introv safe ck ext.
  unfold entry_extends in ext.
  destruct entry; simpl in *; repnd; ginv; subst.
  destruct entry as [vals restr]; simpl in *.
  unfold choice_sequence_entry_extend in *; simpl in *; repnd.
  unfold same_restrictions in ext0.
  destruct name; simpl in *; subst.
  destruct restr; simpl in *; tcsp; ginv; repnd.
  unfold choice_sequence_vals_extend in ext; exrepnd; simpl in *; subst.
  unfold correct_restriction in *; simpl in *; repnd.

  assert (forall v, LIn v vals0 -> exists (b : bool), v = mkc_boolean b) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe n v) as q.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    apply safe0 in q; auto; try omega.
  }
  clear safe.

  assert (exists l, vals0 = map mkc_boolean l) as h.
  {
    induction vals0; simpl in *; tcsp.
    - exists ([] : list bool); simpl; auto.
    - autodimp IHvals0 hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (b :: l); simpl; auto.
  }

  exrepnd; subst.
  exists l (csc_type d typ typd); dands; auto.
  unfold same_restrictions; simpl; dands; auto.
Qed.

Lemma map_mkc_bool_ntimes {o} :
  forall n k,
    map mkc_boolean (ntimes n k)
    = ntimes n (@mkc_boolean o k).
Proof.
  induction n; introv; simpl; auto.
  allrw; simpl; auto.
Qed.

Lemma entry_extends_bool_choice_sequence_entry_implies {o} :
  forall (lib : @library o) name name0 lib' entry',
    name <> name0
    -> safe_library_entry entry'
    -> csn_kind name = cs_kind_nat 1
    -> inf_lib_extends (library2inf lib (simple_inf_choice_seq name0)) lib'
    -> entry_in_library (bool_choice_sequence_entry name) lib
    -> entry_in_library entry' lib'
    -> entry_extends entry' (bool_choice_sequence_entry name)
    -> exists restr n,
        entry' = lib_cs name (MkChoiceSeqEntry _ (ntimes n tt) restr)
        /\ same_restrictions restr csc_bool.
Proof.
  introv dname safe ck iext ilib ilib' ext.

  apply entry_extends_bool_choice_sequence_entry in ext; auto; exrepnd; subst.
  simpl in *; repnd.
  exists restr.

  assert (exists n, l = ntimes n true) as h;
    [|exrepnd; subst; exists n; dands; auto;
      rewrite map_mkc_bool_ntimes;auto];[].

  applydup iext in ilib'.
  repndors; simpl in *.

  - exrepnd.
    apply entry_in_inf_library_extends_library2inf_implies in ilib'1; simpl in *.
    repndors; exrepnd; subst; tcsp;[].
    applydup @inf_entry_extends_lib_cs_implies_matching in ilib'0; simpl in *.
    autorewrite with slow in *.

    dup ilib'1 as m.
    eapply two_entries_in_library_with_same_name in m; try exact ilib; simpl; eauto.
    subst e; simpl in *; repnd; GC.
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
    unfold inf_choice_sequence_vals_extend in *; simpl in *.
    unfold choice_seq_vals2inf in *; simpl in *.
    destruct restr; simpl in *; tcsp; repnd.

    assert (forall v, LIn v l -> v = true) as h.
    {
      introv q.
      apply in_nth in q; exrepnd.
      pose proof (ilib'0 n0 (mkc_boolean v)) as q.
      rewrite select_map in q.
      autodimp q hyp.
      { erewrite nth_select1; auto; unfold option_map; rewrite q0 at 1; eauto. }
      autorewrite with slow in q.
      destruct v; ginv.
    }

    clear ilib'0 ilib'.
    exists (length l); eauto 3 with slow.

  - unfold entry_in_inf_library_default in ilib'0; simpl in *; repnd; GC.
    unfold correct_restriction in *.
    rewrite ck in *; simpl in *.

    unfold is_default_choice_sequence in *.
    destruct restr; simpl in *; repnd; tcsp.
    exists (length l).
    apply implies_list_eq_ntimes.
    introv i.
    apply in_nth in i; exrepnd.
    pose proof (ilib'0 n (mkc_boolean v)) as q.
    rewrite select_map in q.
    autodimp q hyp.
    { erewrite nth_select1; auto; unfold option_map; rewrite i0 at 1; eauto. }
    destruct v; auto; simpl in *.
    rewrite safe1 in q; ginv.
Qed.

Lemma extends_bool_choice_sequence_entry3 {o} :
  forall (lib lib' : @library o) name bs restr,
    safe_library lib
    -> lib_extends lib' lib
    -> same_restrictions restr csc_bool
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean bs) restr)) lib
    -> exists (bs' : list bool) restr',
        same_restrictions restr' restr
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean (bs ++ bs')) restr')) lib'.
Proof.
  introv safe ext same i.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  apply ext in i; clear ext.
  clear dependent lib.
  apply entry_in_library_extends_implies_entry_in_library in i; exrepnd.
  eapply entry_in_library_implies_safe_library_entry in safe';[|eauto].
  unfold entry_extends in i0.
  destruct entry'; simpl in *; tcsp; ginv;[].
  repnd; subst.
  unfold choice_sequence_entry_extend in *; repnd; simpl in *.
  unfold choice_sequence_vals_extend in *; simpl in *; exrepnd; subst; simpl in *.
  destruct entry as [vals1 restr1]; simpl in *; subst; simpl in *; repnd.
  unfold same_restrictions in i2, same.
  destruct restr1, restr; simpl in *; tcsp;[]; repnd.

  assert (forall v, LIn v vals -> exists (b : bool), v = mkc_boolean b) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe' (length bs + n) v) as q.
    rewrite select_app_r in q; autorewrite with slow in *; try omega.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    eapply same; eapply i2; eauto.
  }
  clear safe' safe'0.

  assert (exists l, vals = map mkc_boolean l) as h.
  {
    clear i1.
    induction vals; simpl in *; tcsp.
    - exists ([] : list bool); simpl; auto.
    - autodimp IHvals hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (b :: l); simpl; auto.
  }

  exrepnd; subst.
  exists l (csc_type d typ typd); simpl; dands; tcsp.
  rewrite map_app; tcsp.
Qed.

Definition choice_seq_entry2inf_def {o} (e : @ChoiceSeqEntry o) v : InfChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkInfChoiceSeqEntry
      _
      (choice_seq_vals2inf vals (fun n => v))
      restr
  end.

Definition library_entry2inf_def {o} (e : @library_entry o) nm v : inf_library_entry :=
  match e with
  | lib_cs name entry =>
    if choice_sequence_name_deq name nm
    then inf_lib_cs name (choice_seq_entry2inf_def entry v)
    else inf_lib_cs name (choice_seq_entry2inf entry)
  | lib_abs abs vars rhs correct => inf_lib_abs abs vars rhs correct
  end.

Definition library2inf_def {o} (lib : @library o) (d : inf_library_entry) name v : inf_library :=
  fun n =>
    match select n lib with
    | Some entry => library_entry2inf_def entry name v
    | None => d
    end.

Lemma inf_choice_sequence_entry_extend_choice_seq_entry2inf_def {o} :
  forall (entry : @ChoiceSeqEntry o) v,
    inf_choice_sequence_entry_extend (choice_seq_entry2inf_def entry v) entry.
Proof.
  introv; destruct entry; simpl.
  unfold inf_choice_sequence_entry_extend; simpl.
  dands; auto; eauto 3 with slow;[].
  introv i.
  unfold choice_seq_vals2inf.
  allrw; auto.
Qed.
Hint Resolve inf_choice_sequence_entry_extend_choice_seq_entry2inf_def : slow.

Lemma inf_matching_entries_library_entry2inf_def_implies {o} :
  forall (entry1 entry2 : @library_entry o) name v,
    inf_matching_entries (library_entry2inf_def entry1 name v) entry2
    -> matching_entries entry1 entry2.
Proof.
  introv h.
  destruct entry1; simpl in *; unfold inf_matching_entries in h; simpl in *;
    destruct entry2; simpl in *; tcsp; boolvar; subst; simpl in *; subst; simpl in *;
      eauto 3 with slow; tcsp.
Qed.
Hint Resolve inf_matching_entries_library_entry2inf_def_implies : slow.

Lemma matching_entries_implies_matching_inf_def_entries {o} :
  forall (e1 e2 : @library_entry o) name1 name2 v1 v2,
    matching_entries e1 e2
    -> matching_inf_entries (library_entry2inf_def e1 name1 v1) (library_entry2inf_def e2 name2 v2).
Proof.
  introv m.
  destruct e1, e2; simpl in *; tcsp; boolvar; simpl; tcsp.
Qed.
Hint Resolve matching_entries_implies_matching_inf_def_entries : slow.

Lemma entry_in_inf_library_n_library2inf_def_implies {o} :
  forall n entry d (lib : @library o) name v,
    entry_in_inf_library_n n entry (library2inf_def lib d name v)
    -> entry = d
       \/ exists e, entry_in_library e lib /\ entry = library_entry2inf_def e name v.
Proof.
  induction n; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  { unfold library2inf_def; simpl.
    destruct lib; simpl; tcsp.
    right; exists l; tcsp. }

  destruct lib; simpl in *; autorewrite with slow in *.

  { unfold shift_inf_lib, library2inf_def in i; simpl in i.
    apply entry_in_inf_library_n_const in i; tcsp. }

  unfold library2inf_def in i0; simpl in i0.
  apply IHn in i; clear IHn.

  repndors; exrepnd; subst; tcsp.
  right; exists e; dands; tcsp.
  right; dands; auto.
  introv m; apply matching_entries_sym in m; destruct i0; eauto 2 with slow.
Qed.

Definition is_primitive_nat_kind (name : choice_sequence_name) :=
  match csn_kind name with
  | cs_kind_nat n => n <= 1
  | cs_kind_seq _ => False
  end.

Lemma implies_safe_inf_choice_sequence_entry2inf_def {o} :
  forall name (entry : @ChoiceSeqEntry o) r v,
    is_primitive_nat_kind name
    -> correct_restriction name r
    -> choice_sequence_satisfies_restriction [v] r
    -> safe_choice_sequence_entry name entry
    -> safe_inf_choice_sequence_entry name (choice_seq_entry2inf_def entry v).
Proof.
  introv prim cor sat h; destruct entry as [vals restr]; simpl in *; repnd; dands; auto.

  destruct restr; simpl in *; auto; GC; introv.

  - unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.
    unfold correct_restriction in *.
    destruct name as [name kind]; simpl in *.
    unfold choice_sequence_satisfies_restriction in *.
    unfold is_primitive_nat_kind in *; simpl in *.
    destruct kind; boolvar; subst; simpl in *; repnd; try omega.

    + destruct r; simpl in *; tcsp; repnd.
      apply h0.
      apply (cor 0); apply sat; simpl; auto.

    + destruct r; simpl in *; tcsp; repnd.
      apply h0.
      apply (cor 0); apply sat; simpl; auto.

  - unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.

    { rewrite (h n) in Heqs;[inversion Heqs; auto|].
      eapply select_lt; eauto. }

    unfold correct_restriction in *.
    destruct name as [name kind]; simpl in *.
    unfold choice_sequence_satisfies_restriction in *.
    unfold is_primitive_nat_kind in *; simpl in *.
    destruct kind; boolvar; subst; simpl in *; repnd; try omega.
Qed.
Hint Resolve implies_safe_inf_choice_sequence_entry2inf_def : slow.

Lemma implies_safe_inf_library_library2inf_def {o} :
  forall (lib : @library o) d name v r,
    is_primitive_nat_kind name
    -> correct_restriction name r
    -> choice_sequence_satisfies_restriction [v] r
    -> safe_library lib
    -> safe_inf_library_entry d
    -> safe_inf_library (library2inf_def lib d name v).
Proof.
  introv prim cor sat sl sd i.
  unfold entry_in_inf_library in i; repndors; exrepnd.

  - apply entry_in_inf_library_n_library2inf_def_implies in i0.
    repndors; exrepnd; subst; auto.

    apply sl in i0.
    destruct e; simpl in *; eauto 2 with slow; boolvar; subst; simpl; eauto 3 with slow.

  - unfold inf_entry_in_inf_library_default in *; tcsp.
Qed.
Hint Resolve implies_safe_inf_library_library2inf_def : slow.

Lemma inf_lib_extends_library2inf_def {o} :
  forall (lib : @library o) d name v r,
    is_primitive_nat_kind name
    -> correct_restriction name r
    -> choice_sequence_satisfies_restriction [v] r
    -> safe_inf_library_entry d
    -> inf_lib_extends (library2inf_def lib d name v) lib.
Proof.
  introv prim cor sat safed.
  split; eauto 2 with slow;[].

  {
    introv i.
    left.
    exists (length lib).
    induction lib; simpl in *; tcsp.

    repndors; subst; tcsp.

    - left.
      destruct a; simpl; tcsp.
      dands; auto; eauto 2 with slow.
      unfold inf_entry_extends, library2inf_def; simpl; boolvar; subst; dands; tcsp; eauto 3 with slow.

    - repnd.
      autodimp IHlib hyp.
      right.
      dands; auto.
      intro h; destruct i0.
      unfold library2inf_def in h; simpl in h; eauto 3 with slow.
  }
Qed.
Hint Resolve inf_lib_extends_library2inf_def : slow.

Lemma csn_kind_nat_1_implies_is_primitive_nat_kind :
  forall (name : choice_sequence_name),
    csn_kind name = cs_kind_nat 1
    -> is_primitive_nat_kind name.
Proof.
  introv h; destruct name as [name restr]; simpl in *; subst; tcsp.
Qed.
Hint Resolve csn_kind_nat_1_implies_is_primitive_nat_kind : slow.

Lemma is_bool_ff {o} :
  forall n, @is_bool o n ff.
Proof.
  introv; exists false; auto.
Qed.
Hint Resolve is_bool_ff : slow.

Lemma csn_kind_nat_1_implies_satisfies_restriction_ff {o} :
  forall (name : choice_sequence_name),
    csn_kind name = cs_kind_nat 1
    -> @choice_sequence_satisfies_restriction o [ff] (choice_sequence_name2restriction name).
Proof.
  introv h; destruct name as [name restr]; simpl in *; subst; simpl.
  introv h.
  destruct n; simpl in *; ginv; simpl; auto; eauto 3 with slow.
  autorewrite with slow in *; ginv.
Qed.
Hint Resolve csn_kind_nat_1_implies_satisfies_restriction_ff : slow.

Lemma matching_entries_preserves_inf_matching_entries_library_entry2inf_def {o} :
  forall (e1 e2 : @library_entry o) e name v,
    matching_entries e1 e2
    -> inf_entry_extends (library_entry2inf_def e2 name v) e
    -> inf_matching_entries (library_entry2inf_def e1 name v) e.
Proof.
  introv m i.
  unfold inf_entry_extends in i.
  unfold matching_entries in m.
  destruct e1, e2, e; simpl in *; repnd; subst; tcsp; boolvar; repnd; subst; tcsp.
Qed.
Hint Resolve matching_entries_preserves_inf_matching_entries_library_entry2inf_def : slow.

Lemma entry_in_inf_library_extends_library2inf_def_implies {o} :
  forall n entry d (lib : @library o) name v,
    entry_in_inf_library_extends entry n (library2inf_def lib d name v)
    -> inf_entry_extends d entry
       \/ exists e, entry_in_library e lib /\ inf_entry_extends (library_entry2inf_def e name v) entry.
Proof.
  induction n; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  { unfold library2inf_def in *; simpl in *.
    destruct lib; simpl; tcsp.
    right; exists l; tcsp. }

  destruct lib; simpl in *; autorewrite with slow in *.

  { unfold shift_inf_lib, library2inf_def in i; simpl in i.
    apply entry_in_inf_library_extends_const in i; tcsp. }

  unfold library2inf_def in i0; simpl in i0.
  apply IHn in i; clear IHn.

  repndors; exrepnd; subst; tcsp.
  right; exists e; dands; tcsp.
  right; dands; auto.
  introv m; apply matching_entries_sym in m; destruct i0; eauto 2 with slow.
Qed.

Lemma inf_entry2name_library_entry2inf_def {o} :
  forall (e : @library_entry o) name v,
    inf_entry2name (library_entry2inf_def e name v)
    = entry2name e.
Proof.
  introv; destruct e; simpl; auto; boolvar; simpl; tcsp.
Qed.
Hint Rewrite @inf_entry2name_library_entry2inf_def : slow.

Lemma find_cs_implies_select {o} :
  forall (lib : @library o) name e,
    find_cs lib name = Some e
    -> exists n, select n lib = Some (lib_cs name e).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; tcsp; ginv.

  - exists 0; simpl; auto.

  - apply IHlib in h; exrepnd.
    exists (S n0); simpl; auto.

  - apply IHlib in h; exrepnd.
    exists (S n); simpl; auto.
Qed.

Lemma entry_extends_bool_choice_sequence_entry_implies_def {o} :
  forall (lib : @library o) name name0 lib' entry' b,
    name <> name0
    -> safe_library_entry entry'
    -> csn_kind name = cs_kind_nat 1
    -> inf_lib_extends (library2inf_def lib (simple_inf_choice_seq name0) name (mkc_boolean b)) lib'
    -> entry_in_library (bool_choice_sequence_entry name) lib
    -> entry_in_library entry' lib'
    -> entry_extends entry' (bool_choice_sequence_entry name)
    -> exists restr n,
        entry' = lib_cs name (MkChoiceSeqEntry _ (ntimes n (mkc_boolean b)) restr)
        /\ same_restrictions restr csc_bool.
Proof.
  introv dname safe ck iext ilib ilib' ext.

  apply entry_extends_bool_choice_sequence_entry in ext; auto; exrepnd; subst.
  simpl in *; repnd.
  exists restr.

  assert (exists n, l = ntimes n b) as h;
    [|exrepnd; subst; exists n; dands; auto;
      rewrite map_mkc_bool_ntimes;auto];[].

  applydup iext in ilib'.
  repndors; simpl in *.

  - exrepnd.
    apply entry_in_inf_library_extends_library2inf_def_implies in ilib'1; simpl in *.
    repndors; exrepnd; subst; tcsp;[].
    applydup @inf_entry_extends_lib_cs_implies_matching in ilib'0; simpl in *.
    autorewrite with slow in *.

    dup ilib'1 as m.
    eapply two_entries_in_library_with_same_name in m; try exact ilib; simpl; eauto.
    subst e; simpl in *; repnd; GC.
    boolvar; tcsp; simpl in *; repnd; GC;[].
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
    unfold inf_choice_sequence_vals_extend in *; simpl in *.
    unfold choice_seq_vals2inf in *; simpl in *.
    destruct restr; simpl in *; tcsp; repnd.

    assert (forall v, LIn v l -> v = b) as h.
    {
      introv q.
      apply in_nth in q; exrepnd.
      pose proof (ilib'0 n0 (mkc_boolean v)) as q.
      rewrite select_map in q.
      autodimp q hyp.
      { erewrite nth_select1; auto; unfold option_map; rewrite q0 at 1; eauto. }
      autorewrite with slow in q.
      destruct v, b; ginv.
    }

    clear ilib'0 ilib'.
    exists (length l); eauto 3 with slow.

  - unfold entry_in_inf_library_default in ilib'0; simpl in *; repnd; GC.
    apply entry_in_library_implies_find_cs_some in ilib.
    apply find_cs_implies_select in ilib; exrepnd.
    pose proof (ilib'1 n) as ilib'1; destruct ilib'1.
    unfold inf_matching_entries; simpl.
    unfold library2inf_def; allrw; simpl; boolvar; simpl; auto.
Qed.

Lemma entry_extends_bool_choice_sequence_entry2 {o} :
  forall (entry : @library_entry o) name l restr,
    safe_library_entry entry
    -> csn_kind name = cs_kind_nat 1
    -> same_restrictions restr csc_bool
    -> entry_extends entry (lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean l) restr))
    -> exists k restr',
        entry = lib_cs name (MkChoiceSeqEntry _ (map mkc_boolean (l ++ k)) restr')
        /\ same_restrictions restr' csc_bool.
Proof.
  introv safe ck same ext.
  unfold entry_extends in ext.
  destruct entry; simpl in *; repnd; ginv; subst.
  destruct entry as [vals restr']; simpl in *.
  unfold choice_sequence_entry_extend in *; simpl in *; repnd.
  unfold same_restrictions in ext0, same.
  destruct name; simpl in *; subst.
  destruct restr, restr'; simpl in *; tcsp; ginv; repnd;[].
  unfold choice_sequence_vals_extend in ext; exrepnd; simpl in *; subst.
  unfold correct_restriction in *; simpl in *; repnd.

  assert (forall v, LIn v vals0 -> exists (b : bool), v = mkc_boolean b) as vn.
  {
    introv q.
    apply in_nth in q; exrepnd.
    pose proof (safe (length l + n) v) as q.
    rewrite select_app_r in q; autorewrite with slow in *; try omega.
    autodimp q hyp.
    { erewrite nth_select1; auto; rewrite q0 at 1; eauto. }
    apply safe0 in q; auto; try omega.
  }
  clear safe.

  assert (exists l, vals0 = map mkc_boolean l) as h.
  {
    induction vals0; simpl in *; tcsp.
    - exists ([] : list bool); simpl; auto.
    - autodimp IHvals0 hyp; tcsp.
      exrepnd; subst.
      pose proof (vn a) as vn; autodimp vn hyp; exrepnd; subst.
      exists (b :: l0); simpl; auto.
  }

  exrepnd; subst.
  exists l0 (csc_type d0 typ0 typd0); dands; auto.
  { rewrite map_app; auto. }
  { unfold same_restrictions; simpl; dands; auto. }
Qed.

Lemma ntimes_plus {o} :
  forall n m (t : @CTerm o),
    ntimes (n + m) t = ntimes n t ++ ntimes m t.
Proof.
  induction n; introv; simpl; auto.
  rewrite IHn; auto.
Qed.

Lemma entry_extends_bool_choice_sequence_entry_implies_def2 {o} :
  forall (lib : @library o) name name0 lib' entry' b restr n,
    name <> name0
    -> safe_library_entry entry'
    -> csn_kind name = cs_kind_nat 1
    -> same_restrictions restr csc_bool
    -> inf_lib_extends (library2inf_def lib (simple_inf_choice_seq name0) name (mkc_boolean b)) lib'
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n (mkc_boolean b)) restr)) lib
    -> entry_in_library entry' lib'
    -> entry_extends entry' (lib_cs name (MkChoiceSeqEntry _ (ntimes n (mkc_boolean b)) restr))
    -> exists restr' n,
        entry' = lib_cs name (MkChoiceSeqEntry _ (ntimes n (mkc_boolean b)) restr')
        /\ same_restrictions restr' csc_bool.
Proof.
  introv dname safe ck same iext ilib ilib' ext.

  pose proof (@map_mkc_bool_ntimes o n b) as xx.
  simpl in xx; rewrite <- xx in ext; clear xx.
  apply entry_extends_bool_choice_sequence_entry2 in ext; auto; exrepnd; subst.
  simpl in *; repnd.
  exists restr'.

  assert (exists n, k = ntimes n b) as h;
    [|exrepnd; subst;
      exists (n + n0); rewrite map_app;
      repeat rewrite map_mkc_bool_ntimes;auto;
      rewrite ntimes_plus;dands;auto].

  applydup iext in ilib'.
  repndors; simpl in *.

  - exrepnd.
    apply entry_in_inf_library_extends_library2inf_def_implies in ilib'1; simpl in *.
    repndors; exrepnd; subst; tcsp;[].
    applydup @inf_entry_extends_lib_cs_implies_matching in ilib'0; simpl in *.
    autorewrite with slow in *.

    dup ilib'1 as m.
    eapply two_entries_in_library_with_same_name in m; try exact ilib; simpl; eauto.
    subst e; simpl in *; repnd; GC.
    boolvar; tcsp; simpl in *; repnd; GC;[].
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
    unfold inf_choice_sequence_vals_extend in *; simpl in *.
    unfold choice_seq_vals2inf in *; simpl in *.
    destruct restr, restr'; simpl in *; tcsp; repnd.

    assert (forall v, LIn v k -> v = b) as h.
    {
      introv q.
      apply in_nth in q; exrepnd.
      pose proof (ilib'0 (n + n0) (mkc_boolean v)) as q.
      rewrite map_app in q.
      rewrite select_app_r in q; autorewrite with slow in *; try omega.
      rewrite (select_none (n + n0)) in q; autorewrite with slow; try omega.
      rewrite select_map in q.
      autodimp q hyp.
      { erewrite nth_select1; auto; unfold option_map; rewrite q0 at 1; eauto. }
      autorewrite with slow in q.
      destruct v, b; ginv.
    }

    clear ilib'0 ilib'.
    exists (length k); eauto 3 with slow.

  - unfold entry_in_inf_library_default in ilib'0; simpl in *; repnd; GC.
    apply entry_in_library_implies_find_cs_some in ilib.
    apply find_cs_implies_select in ilib; exrepnd.
    pose proof (ilib'1 n0) as ilib'1; destruct ilib'1.
    unfold inf_matching_entries; simpl.
    unfold library2inf_def; allrw; simpl; boolvar; simpl; auto.
Qed.

Lemma safe_library_entry_ff {o} :
  forall name n (restr : @ChoiceSeqRestriction o),
    csn_kind name = cs_kind_nat 1
    -> same_restrictions restr csc_bool
    -> safe_library_entry (lib_cs name (MkChoiceSeqEntry _ (ntimes n ff) restr)).
Proof.
  introv ck srestr.
  unfold safe_library_entry; simpl; dands; auto.

  {
    unfold correct_restriction.
    allrw; eauto 3 with slow.
  }

  {
    unfold choice_sequence_satisfies_restriction.
    unfold same_restrictions in *.
    destruct restr; simpl in *; repnd; tcsp.
    introv h.
    apply srestr.
    unfold natSeq2restrictionPred; autorewrite with slow.
    destruct (lt_dec n0 n) as [xx|xx].

    - rewrite select_ntimes in h; boolvar; tcsp; try omega; ginv; eauto 3 with slow.

    - rewrite select_none in h; ginv; autorewrite with slow; try omega.
  }
Qed.
Hint Resolve safe_library_entry_ff : slow.

Lemma entry_add_ff_extends {o} :
  forall name n k (restr : @ChoiceSeqRestriction o),
    entry_extends
      (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) ff) restr))
      (lib_cs name (MkChoiceSeqEntry _ (ntimes n ff) restr)).
Proof.
  introv.
  unfold entry_extends; simpl.
  dands; auto.
  unfold choice_sequence_entry_extend; simpl; dands; eauto 3 with slow.
  unfold choice_sequence_vals_extend.
  exists (ntimes k (@ff o)); auto.
  rewrite ntimes_plus; auto.
Qed.
Hint Resolve entry_add_ff_extends : slow.

Lemma extend_bool_choice_sequence_ff {o} :
  forall (lib : @library o) name n restr k,
    csn_kind name = cs_kind_nat 1
    -> same_restrictions restr csc_bool
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n ff) restr)) lib
    -> exists lib',
        map entry2name lib' = map entry2name lib
        /\ lib_extends lib' lib
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) ff) restr)) lib'.
Proof.
  induction lib using rev_list_ind; introv csk same i; simpl in *; tcsp.
  apply entry_in_library_snoc_implies in i.
  repndors; repnd; subst.

  - pose proof (IHlib name n restr k) as IHlib.
    repeat (autodimp IHlib hyp); exrepnd; eauto 3 with slow.
    exists (snoc lib' a); dands; eauto 3 with slow.

    { allrw map_snoc; allrw; auto. }

    { apply implies_lib_extends_snoc_lr_same_names; auto. }

  - exists (snoc lib (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) ff) restr))); simpl; dands; tcsp; eauto 3 with slow.

    { allrw map_snoc; allrw; auto. }

    { apply implies_lib_extends_snoc; eauto 3 with slow. }
Qed.

Lemma iscvalue_ff {o} : @iscvalue o ff.
Proof.
  repeat constructor; simpl; introv h; repndors; tcsp; subst.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_ff : slow.
