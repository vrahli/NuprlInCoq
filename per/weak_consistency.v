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


Require Export sequents.
Require Export sequents_lib.


(* ========= CONSISTENCY ========= *)

(* end hide *)

(**

  Using our definition of [mk_false] and the meaning of sequents, we
  can prove that the following sequent is not true, is this for any
  extract [t]:
<<
      |- False ext t
>>

 *)

Lemma not_VR_sequent_true_false {o} :
  forall lib (t : @NTerm o) c,
    !VR_sequent_true lib (mk_wcseq ([]) ||- (mk_concl mk_false t) c).
Proof.
  introv st.
  rw @VR_sequent_true_ex in st; allsimpl.
  pose proof (st [] []) as st.
  repeat (autodimp st hyp); eauto 3 with slow; exrepnd.
  allrewrite @lsubstc_mk_false.
  proof_irr.
  allapply @equality_refl.
  allapply @false_not_inhabited; sp.
Qed.

Lemma not_sequent_true_ext_lib_false {o} :
  forall lib (t : @NTerm o) c,
    !sequent_true_ext_lib lib (mk_wcseq ([]) ||- (mk_concl mk_false t) c).
Proof.
  introv st.
  pose proof (st lib (lib_extends_refl lib)) as st.
  apply not_VR_sequent_true_false in st; auto.
Qed.

Lemma weak_consistency {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> !rule_true lib (mk_rule (mk_baresequent [] (mk_concl mk_false t)) [] []).
Proof.
  introv wft rt; unfold rule_true in rt; allsimpl.
  assert (wf_sequent (mk_baresequent [] (mk_concl mk_false t))) as wg
         by (repeat constructor; simpl; sp).
  assert (closed_type_baresequent
            (mk_baresequent [] (mk_concl mk_false t))) as cg
         by (unfold closed_type_baresequent, closed_type; simpl; sp).
  pose proof (rt wg cg) as rt.
  repeat (autodimp rt hyp); tcsp; exrepnd.
  rw @sequent_true_eq_VR in rt0.
  apply not_VR_sequent_true_false in rt0; auto.
Qed.

Lemma weak_consistency_ext_lib {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> !rule_true_ext_lib lib (mk_rule (mk_baresequent [] (mk_concl mk_false t)) [] []).
Proof.
  introv wf rt.
  unfold rule_true_ext_lib in *; simpl in *.
  repeat (autodimp rt hyp); eauto 3 with slow;
    try (complete (repeat constructor; simpl; tcsp));[].
  unfold sequent_true_ext_lib_wf in *; exrepnd.
  apply not_sequent_true_ext_lib_false in rt0; auto.
Qed.
