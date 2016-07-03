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


Lemma lsubstc_eq_nil {o} :
  forall (t : @NTerm o) w s c c',
    lsubstc t w s c = lsubstc t w [] c'.
Proof.
  introv.
  apply cterm_eq; simpl.
  rewrite csubst_nil.
  rewrite csubst_trivial; auto.
  rw @cover_vars_eq in c'; simpl in c'.
  rw subvars_eq in c'.
  introv i j; apply c' in j; simpl in j; tcsp.
Qed.

(*
   H |- C ext t

     By closedConclusion

     |- C ext t
 *)
Definition rule_closed_conclusion {o}
           (H : @bhyps o)
           (C t : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_concl C t))
    [
      mk_baresequent [] (mk_concl C t)
    ]
    [].

Lemma rule_closed_conclusion_true3 {o} :
  forall lib (H : @bhyps o) C t,
    rule_true3 lib (rule_closed_conclusion H C t).
Proof.
  intros.
  unfold rule_closed_conclusion, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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
    introv i; tcsp.
    apply ce in i; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 [] []) as h; clear hyp1; exrepnd.
  repeat (autodimp h hyp); try (apply sim_nil);[].
  exrepnd.
  lsubst_tac.
  proof_irr.
  rewrite (lsubstc_eq_nil _ _ s1 _ pC0).
  rewrite (lsubstc_eq_nil _ _ s2 _ pC0).
  rewrite (lsubstc_eq_nil _ _ s1 _ pt0).
  rewrite (lsubstc_eq_nil _ _ s2 _ pt0).
  auto.
Qed.
