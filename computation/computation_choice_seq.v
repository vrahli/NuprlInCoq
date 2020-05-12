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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export computation_seq.



Lemma eapply_wf_def_mk_choice_seq {o} :
  forall name, @eapply_wf_def o (mk_choice_seq name).
Proof.
  introv; unfold eapply_wf_def.
  left.
  eexists; eauto.
Qed.
Hint Resolve eapply_wf_def_mk_choice_seq : slow.

Hint Rewrite Nat2Z.id : slow.

Lemma implies_reduces_to_eapply_choice_seq {o} :
  forall lib (f a : @NTerm o) (name : choice_sequence_name) n v,
    find_cs_value_at lib name n = Some v
    -> f =v>( lib) (mk_choice_seq name)
    -> a =v>(lib) (mk_nat n)
    -> reduces_to lib (mk_eapply f a) ((*apply_swaps name*) (CSVal2term v)).
Proof.
  introv fcs compf compa.
  eapply reduces_to_trans;
    [apply implies_eapply_red;
       [|apply computes_to_value_implies_reduces_to;eauto
        |apply computes_to_value_implies_reduces_to;eauto];
       eauto 3 with slow
    |].
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; simpl.
  boolvar; try omega.
  autorewrite with slow; allrw; auto.
Qed.
Hint Resolve implies_reduces_to_eapply_choice_seq : slow.

Lemma eapply_choice_seq_exception_implies {o} :
  forall lib (t : @NTerm o) name a n e,
    (t =v>(lib) (mk_choice_seq name))
    -> (a =e>(n,lib) e)
    -> ((mk_eapply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  unfold computes_to_value in comp1; repnd.
  allunfold @computes_to_exception.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |];
    eauto 3 with slow.
Qed.
Hint Resolve eapply_choice_seq_exception_implies : slow.

Lemma reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue_like {o} :
  forall lib name v k (a : @NTerm o),
    reduces_in_atmost_k_steps lib (mk_eapply (mk_choice_seq name) a) v k
    -> isvalue_like v
    -> {val : ChoiceSeqVal
        & {n : nat
        & {i : nat
        & {j : nat
        & i + j < k
        # reduces_in_atmost_k_steps lib a (mk_nat n) i
        # reduces_in_atmost_k_steps lib ((*apply_swaps name*) (CSVal2term val)) v j
        # find_cs_value_at lib name n = Some val }}}}
       [+] {j : nat & j < k # reduces_in_atmost_k_steps lib a v j # isexc v}.
Proof.
  induction k; introv comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    apply compute_step_eapply_success in comp1; exrepnd; ginv.
    repndors; exrepnd; subst.

    + apply compute_step_eapply2_success in comp1; repnd; GC.
      repndors; exrepnd; ginv.
      left.
      exists v0 n 0 k; dands; eauto 3 with slow.
      apply reduces_in_atmost_k_steps_0; auto.

    + apply isexc_implies2 in comp2; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      right; exists 0; dands; eauto 3 with slow; try omega.
      apply reduces_in_atmost_k_steps_refl; eauto 3 with slow.

    + apply IHk in comp0; auto.
      repndors; exrepnd.

      * left; exists val n (S i) j; dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

      * right; exists (S j); dands; auto; try omega.
        rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma implies_isprog_apply_swaps {o} :
  forall l (t : @NTerm o),
    isprog t -> isprog (apply_swaps l t).
Proof.
  introv isp.
  allrw @isprog_eq.
  apply implies_isprogram_apply_swaps;auto.
Qed.
Hint Resolve implies_isprog_apply_swaps : slow.

(*Lemma implies_isvalue_apply_swaps {o} :
  forall l (t : @NTerm o),
    isvalue t -> isvalue (apply_swaps l t).
Proof.
  introv isv.
  inversion isv as [? isp isc]; subst.
  split; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_apply_swaps : slow.*)

Definition apply_swapsc {o} (l : cs_swaps) (t : @CTerm o) : CTerm :=
  let (a,p) := t in
  mk_ct (apply_swaps l a) (implies_isprog_apply_swaps l a p).

Definition push_swap_cs_oterm {o} sw (t : @NTerm o) : NTerm :=
  match t with
  | oterm (Can can) bs => push_swap_cs_can sw can bs
  | _ => t
  end.

Fixpoint push_swap_cs_oterms {o} (l : cs_swaps) (t : @NTerm o) : NTerm :=
  match l with
  | [] => t
  | sw :: sws => push_swap_cs_oterms sws (push_swap_cs_oterm sw t)
  end.

Lemma implies_isprog_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isprog t
    -> isprog (push_swap_cs_oterm sw t).
Proof.
  introv isp.
  destruct t as [v|op bs]; simpl; auto.
  destruct op; simpl; auto; simpl in *.
  unfold push_swap_cs_can; simpl.
  allrw @isprog_ot_iff; repnd; unfold OpBindings; simpl; autorewrite with slow.
  dands; auto.
  introv i; apply in_map_iff in i; exrepnd; subst.
  destruct a; simpl in *.
  apply isp in i1.
  allrw <- @isprogram_bt_eq.
  unfold isprogram_bt in *; repnd; simpl in *.
  unfold closed_bt in *; simpl in *; autorewrite with slow; dands; auto.
  allrw @bt_wf_iff; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_push_swap_cs_oterm : slow.

Definition push_swap_cs_otermc {o} sw (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (push_swap_cs_oterm sw a) (implies_isprog_push_swap_cs_oterm sw a x).

Lemma implies_isprog_push_swap_cs_oterms {o} :
  forall l (t : @NTerm o),
    isprog t
    -> isprog (push_swap_cs_oterms l t).
Proof.
  induction l; introv isp; simpl in *; auto.
  apply IHl; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_push_swap_cs_oterms : slow.

Definition push_swap_cs_otermsc {o} l (t : @CTerm o) : CTerm :=
  let (a,x) := t in
  exist isprog (push_swap_cs_oterms l a) (implies_isprog_push_swap_cs_oterms l a x).

Lemma implies_isprogram_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isprogram t
    -> isprogram (push_swap_cs_oterm sw t).
Proof.
  introv isp.
  allrw @isprogram_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprogram_push_swap_cs_oterm : slow.

Lemma implies_iscan_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    iscan t
    -> iscan (push_swap_cs_oterm sw t).
Proof.
  introv isc.
  destruct t as [|op bs]; simpl in *; tcsp.
  destruct op; simpl in *; auto.
Qed.
Hint Resolve implies_iscan_push_swap_cs_oterm : slow.

Lemma implies_isvalue_push_swap_cs_oterm {o} :
  forall sw (t : @NTerm o),
    isvalue t
    -> isvalue (push_swap_cs_oterm sw t).
Proof.
  introv isv.
  destruct isv as [? isp isc].
  split; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_push_swap_cs_oterm : slow.

Lemma implies_isvalue_push_swap_cs_oterms {o} :
  forall l (t : @NTerm o),
    isvalue t
    -> isvalue (push_swap_cs_oterms l t).
Proof.
  induction l; introv isv; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_isvalue_push_swap_cs_oterms : slow.

Lemma implies_reduces_to_apply_choice_seq {o} :
  forall lib (a : @CTerm o) (name : choice_sequence_name) n v,
    computes_to_valc lib a (mkc_nat n)
    -> find_cs_value_at lib name n = Some v
    -> iscvalue v
    -> reduces_toc lib (mkc_apply (mkc_choice_seq name) a) ((*apply_swapsc name*) v).
Proof.
  introv comp find iscv.
  unfold ChoiceSeqVal, iscvalue in *; destruct_cterms.
  unfold reduces_toc, computes_to_valc in *; simpl in *.
  eapply reduces_to_if_split2;[csunf; simpl; reflexivity|].
  eapply implies_reduces_to_eapply_choice_seq in find; eauto; eauto 3 with slow.
Qed.

Lemma implies_reduces_in_atmost_k_steps_mk_swap_cs2 {o} :
  forall k lib sw (t u : @NTerm o),
    reduces_in_atmost_k_steps lib (swap_cs_term sw t) u k
    -> {k' : nat
        & k' <= k
        # reduces_in_atmost_k_steps lib (mk_swap_cs2 sw t) (mk_swap_cs2 sw (swap_cs_term sw u)) k' }.
Proof.
  induction k; introv comp; simpl in *.

  { exists 0; allrw @reduces_in_atmost_k_steps_0; subst; autorewrite with slow; auto. }

  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  destruct t as [v|op bs]; simpl in *.

  { csunf comp1; simpl in *; ginv. }

  destruct op as [can|ncan|nsw|exc|abs]; simpl in *.

  { csunf comp1; simpl in *; ginv.
    apply reduces_atmost_can in comp0; subst; simpl in *; autorewrite with slow.
    exists 0; dands; try omega; allrw @reduces_in_atmost_k_steps_0; auto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }

  { csunf comp1; simpl in *; ginv.
    apply reduces_atmost_exc in comp0; subst; simpl in *; autorewrite with slow.
    exists 0; dands; try omega; allrw @reduces_in_atmost_k_steps_0; auto. }

  { rewrite <- (swap_cs_term_idem sw u0) in comp0.
    rewrite <- (swap_cs_term_idem sw u) in comp0.
    eapply IHk in comp0; exrepnd.
    autorewrite with slow in *.
    exists (S k'); dands; try omega.
    allrw @reduces_in_atmost_k_steps_S.
    csunf; simpl.
    allrw; simpl; eexists; dands; eauto. }
Qed.

Lemma implies_reduces_to_mk_swap_cs2 {o} :
  forall lib sw (t u : @NTerm o),
    reduces_to lib (swap_cs_term sw t) u
    -> reduces_to lib (mk_swap_cs2 sw t) (mk_swap_cs2 sw (swap_cs_term sw u)).
Proof.
  introv comp; unfold reduces_to in *; exrepnd.
  apply implies_reduces_in_atmost_k_steps_mk_swap_cs2 in comp0; exrepnd.
  exists k'; auto.
Qed.

(*Lemma apply_swaps_reduces_to_push_swap_cs_oterms {o} :
  forall lib l (t : @NTerm o),
    iscan t
    -> reduces_to lib (apply_swaps l t) (push_swap_cs_oterms l t).
Proof.
  induction l; introv isc; simpl; eauto 3 with slow.
  eapply reduces_to_trans;[|apply IHl]; eauto 3 with slow.
SearchAbout reduces_to mk_swap_cs2.
Qed.*)

Lemma implies_compute_to_valc_apply_choice_seq {o} :
  forall lib (a : @CTerm o) (name : choice_sequence_name) n v,
    computes_to_valc lib a (mkc_nat n)
    -> find_cs_value_at lib name n = Some v
    -> iscvalue v
    -> computes_to_valc lib (mkc_apply (mkc_choice_seq name) a) v.
Proof.
  introv comp find iscv.
  eapply implies_reduces_to_apply_choice_seq in find; eauto.
  unfold ChoiceSeqVal, computes_to_valc, reduces_toc in *; destruct_cterms; simpl in *.
  split; simpl; eauto 3 with slow.
Qed.
