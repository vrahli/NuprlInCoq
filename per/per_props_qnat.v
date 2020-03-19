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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Abhishek Anand

*)


Require Export per_props_util.


Lemma dest_nuprl_qnat {o} :
  forall (lib : @library o) eq,
    nuprl lib mkc_qnat mkc_qnat eq
    -> per_bar (per_qnat nuprl) lib mkc_qnat mkc_qnat eq.
Proof.
  introv cl.
  eapply dest_close_per_qnat_l in cl; eauto 3 with slow.
  unfold per_qnat_bar in *; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib).
  dands; auto; simpl.

  {
    apply in_ext_ext_implies_in_open_bar_ext; introv ext.
    unfold per_qnat; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym;apply per_bar_eq_equality_of_qnat_bar_lib_per.
  }
Qed.

Lemma dest_nuprl_qnat2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_qnat mkc_qnat eq
    -> eq <=2=> (equality_of_qnat_bar lib).
Proof.
  introv u.
  apply dest_nuprl_qnat in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply per_bar_eq_equality_of_qnat_bar_lib_per].
  apply implies_eq_term_equals_per_bar_eq.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold per_qnat in *; exrepnd; spcast; auto.
Qed.

Lemma nuprl_qnat {p} :
  forall lib, @nuprl p lib mkc_qnat mkc_qnat (equality_of_qnat_bar lib).
Proof.
  sp.
  apply CL_qnat.
  unfold per_qnat; sp; spcast; eauto 3 with slow.
Qed.
Hint Resolve nuprl_qnat : slow.

Lemma equality_in_qnat {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_qnat <=> equality_of_qnat_bar lib t1 t2.
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_qnat2 in e1.
    apply e1 in e0; auto.

  - exists (equality_of_qnat_bar lib); dands; auto; eauto 3 with slow.
Qed.

Lemma tequality_qnat {p} : forall lib, @tequality p lib mkc_qnat mkc_qnat.
Proof.
  introv.
  exists (@equality_of_qnat_bar p lib).
  apply CL_qnat; split; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve tequality_qnat : slow.

Lemma implies_cequivc_last_cs {o} :
  forall lib (a b u v : @CTerm o),
    cequivc lib a b
    -> cequivc lib u v
    -> cequivc lib (mkc_last_cs a u) (mkc_last_cs b v).
Proof.
  unfold cequivc; introv ceqa ceqb; destruct_cterms; simpl in *.
  repnud ceqa.
  repnud ceqb.
  split; apply approx_congruence; fold_terms;
    try (apply implies_isprogram_last_cs; apply isprog_implies; auto).

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try omega); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try omega); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }
Qed.

Lemma implies_ccequivc_ext_last_cs {o} :
  forall lib (a b u v : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib (mkc_last_cs a u) (mkc_last_cs b v).
Proof.
  introv ceqa ceqb ext; applydup ceqa in ext; applydup ceqb in ext; spcast.
  apply implies_cequivc_last_cs; auto.
Qed.

Lemma last_cs_entry_implies_in {o} :
  forall vals (v : @ChoiceSeqVal o),
    last_cs_entry vals = Some v -> LIn v vals.
Proof.
  induction vals; introv h; simpl in *; tcsp.
  destruct vals; ginv; tcsp.
Qed.

Lemma in_implies_select :
  forall {A} (a : A) l,
    LIn a l -> {n : nat & select n l = Some a}.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; tcsp.
  { exists 0; simpl; tcsp. }
  { apply IHl in i; exrepnd.
    exists (S n); simpl; tcsp. }
Qed.

Lemma is_nat_mkc_nat {o} :
  forall n i, @is_nat o n (mkc_nat i).
Proof.
  introv; unfold is_nat; eexists; eauto.
Qed.
Hint Resolve is_nat_mkc_nat : slow.

Lemma compatible_cs_kind_0_implies_is_nat_restriction {o} :
  forall name (restr : @ChoiceSeqRestriction o) vals v,
    compatible_cs_kind 0 (csn_kind name)
    -> correct_restriction name restr
    -> LIn v vals
    -> choice_sequence_satisfies_restriction vals restr
    -> {n : nat & is_nat n v}.
Proof.
  introv comp cor iv sat.
  unfold correct_restriction in *.
  unfold compatible_cs_kind in *; boolvar; tcsp; GC.
  destruct name as [nm kd]; simpl in *.
  destruct kd; subst; boolvar; tcsp; GC.

  {
    unfold is_nat_restriction in *.
    unfold choice_sequence_satisfies_restriction in *.
    destruct restr; repnd; dands; tcsp.

    { apply in_implies_select in iv; exrepnd.
      apply sat in iv0; apply cor in iv0; exists n; auto. }

(*
    { apply in_implies_select in iv; exrepnd.
      rewrite sat in iv0; eauto 3 with slow; inversion iv0; subst.
      exists n; auto. }

    { apply in_implies_select in iv; exrepnd.
      apply sat in iv0; apply cor in iv0; exists n; auto. }*)
  }

(*  {
    unfold is_nat_seq_restriction in *.
    unfold choice_sequence_satisfies_restriction in *.
    destruct restr; repnd; dands; tcsp.
    apply in_implies_select in iv; exrepnd.
    exists n.
    applydup sat in iv0.
    destruct (lt_dec n (length l)).
    { apply cor0 in iv1; auto.
      unfold cterm_is_nth in iv1; exrepnd; exrepnd.
      pose proof (cor0 n v) as q; autodimp q hyp; subst; eauto 2 with slow. }
    { apply cor in iv1; auto; try omega. }
  }*)
Qed.

Lemma compatible_cs_kind_0_implies_find_nat {o} :
  forall (lib : @library o) name e v,
    compatible_cs_kind 0 (csn_kind name)
    -> safe_library lib
    -> find_cs lib name = Some e
    -> last_cs_entry e = Some v
    -> exists (n : nat), CSVal2term v = mk_nat n.
Proof.
  introv comp safe find lcs.
  assert (entry_in_library (lib_cs name e) lib) as i by eauto 2 with slow.
  clear find.
  apply safe in i; simpl in *.
  destruct e as [vals restr]; simpl in *; repnd.
  apply last_cs_entry_implies_in in lcs.
  eapply compatible_cs_kind_0_implies_is_nat_restriction in comp; eauto; exrepnd.
  unfold is_nat in comp0; exrepnd; subst.
  exists i1; simpl; auto.
Qed.

Lemma in_ext_exists_ccomputes_to_valc_mkc_last_cs_choice_seq {o} :
  forall (lib : @library o) name k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> in_ext lib (fun lib => exists n, ccomputes_to_valc lib (mkc_last_cs (mkc_choice_seq name) (mkc_nat k)) (mkc_nat n)).
Proof.
  introv safe comp ext.

  assert (compute_step lib' (mk_last_cs (mk_choice_seq name) (mk_nat k)) = csuccess (find_last_entry_default lib' name (mk_nat k))) as w.
  { csunf; simpl; auto. }

  assert (exists (n : nat), find_last_entry_default lib' name (mk_nat k) = mk_nat n) as z.
  {
    unfold find_last_entry_default.
    remember (find_cs lib' name) as fcs; symmetry in Heqfcs; destruct fcs;[|eexists; eauto].
    remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs;[|eexists; eauto].
    unfold compatible_choice_sequence_name in *.
    eapply compatible_cs_kind_0_implies_find_nat in Heqfcs; eauto; eauto 3 with slow.
  }

  exrepnd.
  exists n.
  rewrite z0 in w; clear z0.
  spcast.
  unfold computes_to_valc, computes_to_value; simpl; dands; eauto 2 with slow.
Qed.
Hint Resolve in_ext_exists_ccomputes_to_valc_mkc_last_cs_choice_seq : slow.

Lemma exists_ccomputes_to_valc_mkc_last_cs_choice_seq {o} :
  forall (lib : @library o) name k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> exists n, ccomputes_to_valc lib (mkc_last_cs (mkc_choice_seq name) (mkc_nat k)) (mkc_nat n).
Proof.
  introv safe comp.

  assert (compute_step lib (mk_last_cs (mk_choice_seq name) (mk_nat k)) = csuccess (find_last_entry_default lib name (mk_nat k))) as w.
  { csunf; simpl; auto. }

  assert (exists (n : nat), find_last_entry_default lib name (mk_nat k) = mk_nat n) as z.
  {
    unfold find_last_entry_default.
    remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs;[|eexists; eauto].
    remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs;[|eexists; eauto].
    unfold compatible_choice_sequence_name in *.
    eapply compatible_cs_kind_0_implies_find_nat in Heqfcs; eauto; eauto 3 with slow.
  }

  exrepnd.
  exists n.
  rewrite z0 in w; clear z0.
  spcast.
  unfold computes_to_valc, computes_to_value; simpl; dands; eauto 2 with slow.
Qed.
Hint Resolve exists_ccomputes_to_valc_mkc_last_cs_choice_seq : slow.

Lemma in_ext_exists_ccomputes_to_valc_nat {o} :
  forall (lib : @library o) k,
    in_ext lib (fun lib => exists n, ccomputes_to_valc lib (mkc_nat k) (mkc_nat n)).
Proof.
  introv ext; exists k; spcast; eauto 3 with slow.
Qed.
Hint Resolve in_ext_exists_ccomputes_to_valc_nat : slow.

Lemma equality_nat_in_qnat {o} :
  forall (lib : @library o) k, equality lib (mkc_nat k) (mkc_nat k) mkc_qnat.
Proof.
  introv.
  apply equality_in_qnat; eauto 2 with slow.
  unfold equality_of_qnat_bar.
  apply in_ext_implies_in_open_bar; introv xt.
  unfold equality_of_qnat.
  eexists; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve equality_nat_in_qnat : slow.
