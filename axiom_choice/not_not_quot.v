 (*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)

Require Export substc_more.
Require Export per_props4.
Require Export cnterm.


Definition rule_not_not_quot {o}
           (P : @NTerm o)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_squash P)))
      [ mk_baresequent H (mk_conclax (mk_not (mk_not P))) ]
      [].

Lemma rule_not_not_quot_true {p} :
  forall lib
         (P : NTerm)
         (H : @barehypotheses p),
    rule_true lib (rule_not_not_quot P H).
Proof.
  unfold rule_not_not_quot, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hh; exrepnd; clear hyp1.

  lsubst_tac.

Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
