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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_equality.


(*
   H |- Ax = Ax in (a = b in T)

     By axiomEquality

     H |- a = b in T
 *)
Definition rule_axiom_equality {o}
           (H : @bhyps o) (a b T : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member mk_axiom (mk_equality a b T))))
    [
      mk_baresequent H (mk_conclax (mk_equality a b T))
    ]
    [].

Lemma rule_axiom_equality_true3 {o} :
  forall lib (H : @bhyps o) a b T,
    rule_true3 lib (rule_axiom_equality H a b T).
Proof.
  intros.
  unfold rule_axiom_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member mk_axiom (mk_equality a b T)))) as wfc.
  { clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv i; allrw in_app_iff; repndors; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @tequality_mkc_member_sp.
  rw <- @member_member_iff.
  rewrite member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2) as q; clear hyp1.
  repeat (autodimp q hyp); exrepnd.
  lsubst_tac; auto.

  dands; auto.
  rw <- @member_equality_iff in q1; auto.
Qed.