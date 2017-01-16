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
Require Export per_props_uni.
Require Export per_props_halts.


(*
   H |- A = B in Type(i)

     By equalityUniverse

     H |- (a1 = a2 in A) = (b1 = b2 in B) in Type(i)
 *)
Definition rule_equality_universe {o}
           (H : @bhyps o)
           (A B a1 a2 b1 b2 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i))))
    [
      mk_baresequent H (mk_conclax (mk_equality
                                      (mk_equality a1 a2 A)
                                      (mk_equality b1 b2 B)
                                      (mk_uni i)))
    ]
    [].

Lemma rule_equality_universe_true3 {o} :
  forall lib (H : @bhyps o) A B a1 a2 b1 b2 i,
    rule_true3 lib (rule_equality_universe H A B a1 a2 b1 b2 i).
Proof.
  intros.
  unfold rule_equality_universe, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv j; allrw in_app_iff; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.
  pose proof (teq_and_eq_if_equality lib (mk_uni i) A B s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0) as q.
  lsubst_tac.
  repeat (autodimp q hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.
  introv hf sim.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in h1.
  apply equality_commutes in h0; auto;[].
  apply equality_mkc_equality2_sp_in_uni in h0; sp.
Qed.
