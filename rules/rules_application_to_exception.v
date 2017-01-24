(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export chalts.
Require Export sequents_tacs2.
Require Export cequiv_props.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export per_props_ffatom.
Require Export per_can.
Require Export computation_cbv.
Require Export cequiv_props2.
Require Export cequiv_props5.



Lemma hasvaluec_iff_reduces_toc_iscvalue {o} :
  forall lib (t : @CTerm o),
    hasvaluec lib t <=> {u : CTerm & reduces_toc lib t u # iscvalue u}.
Proof.
  introv; split; intro h;
    [|exrepnd; eapply reduces_toc_iscvalue_implies_hasvaluec; eauto].
  destruct_cterms.
  unfold hasvaluec in h; simpl in h.
  unfold reduces_toc, iscvalue; simpl.
  unfold hasvalue in h; exrepnd.
  destruct h0 as [rt isv].
  applydup @reduces_to_preserves_program in rt; eauto 3 with slow.
  allrw @isprogram_eq.
  exists (mk_ct t' rt0); simpl.
  dands; auto.
Qed.

Lemma reduces_to_apply_if_free_from_token {o} :
  forall lib (f t n d v : @CTerm o) u,
    computes_to_valc lib n (mkc_utoken u)
    -> !LIn u (getc_utokens f)
    -> reduces_toc lib (mkc_apply f (mkc_exception n d)) v
    -> iscvalue v
    -> reduces_toc lib (mkc_apply f t) v.
Proof.
Qed.


(*
   H |- f t ~ f exception(n,d)

     By ApplicationToUnusedException

     H |- (f exception(n,d))↓
     H |- free-from_atom(Base,f,n)
     H |- f ∈ Base
     H |- t ∈ Base
     H |- n ∈ Base
     H |- d ∈ Base
 *)
Definition rule_application_to_unused_function {o}
           (H : barehypotheses)
           (f t n d : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv (mk_apply f t) (mk_apply f (mk_exception n d)))))
    [
      mk_baresequent H (mk_conclax (mk_halts (mk_apply f (mk_exception n d)))),
      mk_baresequent H (mk_conclax (mk_free_from_atom mk_base f n)),
      mk_baresequent H (mk_conclax (mk_member f mk_base)),
      mk_baresequent H (mk_conclax (mk_member t mk_base)),
      mk_baresequent H (mk_conclax (mk_member n mk_base)),
      mk_baresequent H (mk_conclax (mk_member d mk_base))
    ]
    [].


Lemma rule_application_to_unused_function_true {o} :
  forall lib
         (f t n d : NTerm)
         (H : @barehypotheses o),
    rule_true lib (rule_application_to_unused_function H f t n d).
Proof.
  unfold rule_application_to_unused_function, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp_halts.
  rename Hyp1 into hyp_ffa.
  rename Hyp2 into hyp_fbase.
  rename Hyp3 into hyp_tbase.
  rename Hyp4 into hyp_nbase.
  rename Hyp5 into hyp_dbase.

  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_cequiv (mk_apply f t) (mk_apply f (mk_exception n d))))) as cs.
  {
    unfold closed_extract; simpl.
    apply covered_axiom.
  }

  exists cs.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.

  rw @tequality_mkc_cequiv.
  rw <- @member_cequiv_iff.

  vr_seq_true in hyp_fbase.
  pose proof (hyp_fbase s1 s2 eqh sim) as hyp_fbase.
  exrepnd.

  vr_seq_true in hyp_tbase.
  pose proof (hyp_tbase s1 s2 eqh sim) as hyp_tbase.
  exrepnd.

  vr_seq_true in hyp_nbase.
  pose proof (hyp_nbase s1 s2 eqh sim) as hyp_nbase.
  exrepnd.

  vr_seq_true in hyp_dbase.
  pose proof (hyp_dbase s1 s2 eqh sim) as hyp_dbase.
  exrepnd.

  clear hyp_fbase1 hyp_tbase1 hyp_nbase1 hyp_dbase1.
  lsubst_tac.
  apply tequality_mkc_member_base in hyp_fbase0.
  apply tequality_mkc_member_base in hyp_tbase0.
  apply tequality_mkc_member_base in hyp_nbase0.
  apply tequality_mkc_member_base in hyp_dbase0.
  spcast.

  dands.

  {
    split; intro h; spcast.

    - eapply cequivc_trans;
        [apply implies_cequivc_apply;
         apply cequivc_sym;
         [apply hyp_fbase0
         |apply hyp_tbase0]
        |].

      eapply cequivc_trans;[exact h|clear h].
      apply implies_cequivc_apply; auto.
      apply implies_cequivc_exception; auto.

    - eapply cequivc_trans;
        [apply implies_cequivc_apply;
         [apply hyp_fbase0
         |apply hyp_tbase0]
        |].

      eapply cequivc_trans;[exact h|clear h].
      apply cequivc_sym.
      apply implies_cequivc_apply; auto.
      apply implies_cequivc_exception; auto.
  }

  vr_seq_true in hyp_halts.
  pose proof (hyp_halts s1 s2 eqh sim) as hyp_halts.
  exrepnd.

  vr_seq_true in hyp_ffa.
  pose proof (hyp_ffa s1 s2 eqh sim) as hyp_ffa.
  exrepnd.

  lsubst_tac.

  apply equality_in_halts in hyp_halts1; repnd.
  apply equality_in_free_from_atom in hyp_ffa1; exrepnd.
  apply equality_in_base_iff in hyp_ffa6.
  clear hyp_halts0 hyp_halts3 hyp_halts1 hyp_ffa0 hyp_ffa2 hyp_ffa3 hyp_ffa5.

  spcast.

  eapply cequivc_trans;
    [apply sp_implies_cequivc_apply;exact hyp_ffa6|].
  eapply cequivc_trans;
    [|apply sp_implies_cequivc_apply;apply cequivc_sym;exact hyp_ffa6].
  eapply hasvaluec_cequivc in hyp_halts2;
    [|apply sp_implies_cequivc_apply;exact hyp_ffa6].

  clear hyp_ffa6.

  apply hasvaluec_iff_reduces_toc_iscvalue in hyp_halts2; exrepnd.

Qed.