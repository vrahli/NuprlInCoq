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

Lemma implies_reduces_to_eapply_choice_seq {o} {lv} :
  forall (lib : @library o lv) (f a : @NTerm o) name n v,
    find_cs_value_at lib name n = Some v
    -> f =v>( lib) (mk_choice_seq name)
    -> a =v>(lib) (mk_nat n)
    -> reduces_to lib (mk_eapply f a) (CSVal2term v).
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

Lemma eapply_choice_seq_exception_implies {o} {lv} :
  forall (lib : @library o lv) (t : @NTerm o) name a n e,
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

Lemma reduces_in_atmost_k_steps_eapply_choice_seq_to_isvalue_like {o} {lv} :
  forall (lib : @library o lv) name v k (a : @NTerm o),
    reduces_in_atmost_k_steps lib (mk_eapply (mk_choice_seq name) a) v k
    -> isvalue_like v
    -> {val : ChoiceSeqVal
        & {n : nat
        & {i : nat
        & {j : nat
        & i + j < k
        # reduces_in_atmost_k_steps lib a (mk_nat n) i
        # reduces_in_atmost_k_steps lib (CSVal2term val) v j
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

Lemma implies_compute_to_valc_apply_choice_seq {o} {lv} :
  forall (lib : @library o lv) (a : @CTerm o) name n v,
    computes_to_valc lib a (mkc_nat n)
    -> find_cs_value_at lib name n = Some v
    -> iscvalue v
    -> computes_to_valc lib (mkc_apply (mkc_choice_seq name) a) v.
Proof.
  introv comp find iscv.
  destruct_cterms.
  unfold computes_to_valc in *; simpl in *.
  eapply computes_to_value_step;[|csunf; simpl; reflexivity].
  split; eauto 2 with slow.
  eapply implies_reduces_to_eapply_choice_seq;[eauto| |eauto].
  apply computes_to_value_isvalue_refl; eauto 2 with slow.
Qed.
