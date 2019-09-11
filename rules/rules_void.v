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


Lemma lsubstc_mk_void {o} :
  forall w s c, @lsubstc o mk_void w s c = mkc_void.
Proof.
  introv; apply cterm_eq; simpl.
  unfold csubst; unflsubst; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_mk_void : slow.

Lemma void_in_uni {p} :
  forall lib i, @member p lib mkc_void (mkc_uni i).
Proof.
  introv.
  rewrite mkc_void_eq_mkc_false.
  rw @mkc_false_eq.
  apply mkc_approx_equality_in_uni; tcsp.
Qed.
Hint Resolve void_in_uni : slow.


(*
   H |- Void = Void in Type(i)

     By voidEquality
 *)
Definition rule_void_equality {o}
           (H : @bhyps o)
           (i : nat) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member mk_void (mk_uni i))))
    []
    [].

Lemma rule_void_equality_true3 {o} :
  forall lib (H : @bhyps o) (i : nat),
    rule_true3 lib (rule_void_equality H i).
Proof.
  intros.
  unfold rule_void_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member mk_void (mk_uni i)))) as wfc.
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
  pose proof (teq_and_member_if_member lib (mk_uni i) mk_void s1 s2 H wT wt ct ct0 cT cT0) as q.
  rw <- @member_member_iff.
  lsubst_tac.
  autorewrite with slow in *.
  apply q; auto.
  { apply tequality_mkc_uni. }
  clear dependent s1; clear dependent s2.
  introv hf sim.
  lsubst_tac; autorewrite with slow.
  apply void_in_uni.
Qed.


(*
   H, x : Void, J |- C

     By voidElimination
 *)
Definition rule_void_elimination {o}
           (H J : @bhyps o)
           (C : NTerm)
           (x : NVar) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp x mk_void) ++ J) (mk_conclax C))
    []
    [].

Lemma rule_void_elimination_true {o} :
  forall lib (H J : @bhyps o) C x,
    rule_true lib (rule_void_elimination H J C x).
Proof.
  intros.
  unfold rule_void_elimination, rule_true, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract (snoc H (mk_hyp x mk_void) ++ J) (mk_conclax C)) as ce.
  { unfold closed_extract; simpl; apply covered_axiom. }

  exists ce.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  clear eqh.
  apply similarity_app in sim; exrepnd; subst.
  apply similarity_snoc in sim5; exrepnd; subst; allsimpl.
  autorewrite with slow in *.
  apply equality_in_void in sim2; tcsp.
Qed.
