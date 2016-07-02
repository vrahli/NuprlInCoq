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


Lemma int_in_uni {p} :
  forall lib i, @member p lib mkc_int (mkc_uni i).
Proof.
  introv.
  unfold member, equality.
  exists (fun A A' => {eqa : per , close lib (univi lib i) A A' eqa}).
  unfold nuprl.
  dands.

  { apply mkc_uni_in_nuprl. }

  { exists (equality_of_int lib).
    apply CL_int.
    unfold per_int; dands; spcast; auto;
      apply computes_to_valc_refl; eauto 3 with slow. }
Qed.


(*
   H |- n = n in Int

     By natural_numberEquality
 *)
Definition rule_natural_number_equality {o}
           (H : @bhyps o)
           (i : Z) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_integer i) (mk_integer i) mk_int)))
    []
    [].

Lemma rule_natural_number_equality_true3 {o} :
  forall lib (H : @bhyps o) i,
    rule_true3 lib (rule_natural_number_equality H i).
Proof.
  intros.
  unfold rule_natural_number_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.
  pose proof (teq_and_eq_if_equality
                lib mk_int (mk_integer i) (mk_integer i)
                s1 s2 H wT w1 w1 c1 c0 cT cT0 cT cT0) as q.
  lsubst_tac.
  apply q; auto; clear q.

  { apply tequality_int. }

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.

  apply @equality_in_int.
  exists i; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.


(*
   H |- Int = Int in Type(i)

     By intEquality
 *)
Definition rule_int_equality {o}
           (H : @bhyps o)
           (i : nat) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality mk_int mk_int (mk_uni i))))
    []
    [].

Lemma rule_int_equality_true3 {o} :
  forall lib (H : @bhyps o) i,
    rule_true3 lib (rule_int_equality H i).
Proof.
  intros.
  unfold rule_int_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.
  pose proof (teq_and_eq_if_equality
                lib (mk_uni i) mk_int mk_int
                s1 s2 H wT w1 w1 c1 c0 cT cT0 cT cT0) as q.
  lsubst_tac.
  apply q; auto; clear q.

  { apply tequality_mkc_uni. }

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply int_in_uni.
Qed.
