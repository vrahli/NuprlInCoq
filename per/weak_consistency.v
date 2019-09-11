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


Lemma hyps_functionality_ext_nil {o} :
  forall (lib : @library o),
    hyps_functionality_ext lib [] [].
Proof.
  introv ext; eauto 3 with slow.
Qed.
Hint Resolve hyps_functionality_ext_nil : slow.



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

Lemma weak_consistency {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> rule_true lib (mk_rule (mk_baresequent [] (mk_concl mk_false t)) [] [])
    -> False.
Proof.
  introv wft rt; unfold rule_true in rt; allsimpl.
  assert (wf_sequent (mk_baresequent [] (mk_concl mk_false t))) as wg
         by (repeat constructor; simpl; sp).
  generalize (rt wg); clear rt; intro rt.
  assert (closed_type_baresequent
            (mk_baresequent [] (mk_concl mk_false t))) as cg
         by (unfold closed_type_baresequent, closed_type; simpl; sp).
  generalize (rt cg); clear rt; intro rt.
  repeat (dest_imp rt hyp; sp).
  rw @sequent_true_eq_VR in s.
  rw @VR_sequent_true_ex in s; allsimpl.
  generalize (s lib (lib_extends_refl lib) [] []); clear s; intro s.
  dest_imp s hyp; sp; eauto 3 with slow.
  dest_imp s hyp; sp; allsimpl.
  allrewrite @lsubstc_mk_false.
  proof_irr.
  allapply @equality_refl.
  allapply @false_not_inhabited; sp.
Qed.

(*
(* get a universe inconsistency error *)
Lemma weak_consistency2 {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> !(rule_true lib (mk_rule (mk_baresequent [] (mk_concl mk_false t)) [] [])).
Proof.
Qed.
 *)
