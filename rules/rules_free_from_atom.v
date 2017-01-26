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
Require Export per_props_ffatom.


(*
   H |- (free_from_atom T1 t1 a1) = (free_from_atom T2 t2 a2) in Type(i)

     By freeFromAtomEquality

     H |- T1 = T2 in Type(i)
     H |- t1 = t2 in T1
     H |- a1 = a2 in Name
 *)
Definition rule_free_from_atom_equality {o}
           (H : @bhyps o)
           (T1 T2 t1 t2 a1 a2 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_free_from_atom T1 t1 a1) (mk_free_from_atom T2 t2 a2) (mk_uni i))))
    [
      mk_baresequent H (mk_conclax (mk_equality T1 T2 (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_equality t1 t2 T1)),
      mk_baresequent H (mk_conclax (mk_equality a1 a2 mk_uatom))
    ]
    [].

Lemma rule_free_from_atom_equality_true3 {o} :
  forall lib (H : @bhyps o) T1 T2 t1 t2 a1 a2 i,
    rule_true3 lib (rule_free_from_atom_equality H T1 T2 t1 t2 a1 a2 i).
Proof.
  intros.
  unfold rule_free_from_atom_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destruct Hyp1 as [ ws3 hyp3 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { clear hyp1 hyp2 hyp3.
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
  pose proof (teq_and_eq_if_equality
                lib (mk_uni i) (mk_free_from_atom T1 t1 a1) (mk_free_from_atom T2 t2 a2)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2) as q.
  lsubst_tac.
  repeat (autodimp q hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.
  introv hf sim.

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 hf sim) as q; clear hyp2; exrepnd.
  pose proof (hyp3 s1 s2 hf sim) as z; clear hyp3; exrepnd.
  lsubst_tac.

  allrw <- @member_equality_iff.
  apply equality_commutes in h0; auto;[].
  apply equality_commutes in z0; auto;[].
  apply equality_commutes4 in q0; auto;[].

  apply equality_free_from_atom_in_uni.
  dands; auto.
Qed.
