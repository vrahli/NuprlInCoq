(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export computation_minus.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.
Require Export integer_type.

(*
   H |- a = b in T

     By ArithExceptionCases

     H |- isexc(u op v)
     H, x : u in Int, y: isexc(v) |- a = b in T
     H, x : isexc(u) |- a = b in T
     H |- u in Base
     H |- v in Base
 *)
Definition rule_arith_exception_cases {o}
           (H : barehypotheses)
           (op: ArithOp )
           (a b T u v: @NTerm o)
           (x y : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_arithop op u v))),
      mk_baresequent (snoc (snoc H (mk_hyp x (mk_member u mk_int)))
                                   (mk_hyp y (mk_isexc v)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc H (mk_hyp x (mk_isexc u)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent H (mk_conclax (mk_member u mk_base)), 
      mk_baresequent H (mk_conclax (mk_member v mk_base))
    ]
    [].

(*
   H |- a = b in T

     By minusExceptionCases

     H |- isexc(-t)
     H, x : isexc(t) |- a = b in T
     H |- t in Base
 *)
Definition rule_minus_exception_cases {o}
           (H : barehypotheses)
           (a b T t: @NTerm o)
           (x : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_minus t))),
      mk_baresequent (snoc H (mk_hyp x (mk_isexc t)))
                     (mk_conclax (mk_equality a b T)), 
      mk_baresequent H (mk_conclax (mk_member t mk_base))
    ]
    [].


Lemma rule_arith_exception_cases_true {o} :
  forall lib (H : barehypotheses)
         op
         (a b T u v : @NTerm o)
         (x y : NVar),
    rule_true lib (rule_arith_exception_cases H op a b T u v x y).
Proof.
  unfold rule_arith_exception_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  rename Hyp4 into hyp5.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality a b T))) as cs.
  clear hyp1 hyp2 hyp3 hyp4 hyp5.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars u)
          # !LIn x (free_vars v)
          # !LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (vars_hyps H)
          # x <> y
          # !LIn y (free_vars u)
          # !LIn y (free_vars v)
          # !LIn y (free_vars T)
          # !LIn y (free_vars b)
          # !LIn y (free_vars a)
          # !LIn y (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4 hyp5.
   dwfseq.
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nxu vhyps ].
  destruct vhyps as [ nxv vhyps ].
  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nyu vhyps ].
  destruct vhyps as [ nyv vhyps ].
  destruct vhyps as [ nyT vhyps ].
  destruct vhyps as [ nyb vhyps ].
  destruct vhyps as [ nya nyH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.
  
  lsubst_tac.
  allrw @tequality_mkc_isexc.
  allrw <- @member_isexc_iff.
  applydup hyp0 in hyp1.
  clear hyp0.
  rw <- @member_equality_iff.
  rw @tequality_mkc_equality_sp.

  apply if_raises_exceptionc_arithop in hyp1.
  repndors; exrepnd.

  - vr_seq_true in hyp3.
    pose proof (hyp3 (snoc s1 (x,mkc_axiom)) (snoc s2 (x,mkc_axiom))) as hyp.
    clear hyp3.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      apply tequality_mkc_isexc.
      split; intro h; auto. GC;[].

      vr_seq_true in hyp4.

      pose proof (hyp4 s1 s') as hyp; clear hyp4.
      repeat (autodimp hyp hyp');[].
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp0.
      apply cequiv_stable in hyp0.
      eapply raises_exceptionc_preserves_cequivc;[exact hyp0|]; auto.
    }

    { assert (wf_term (mk_isexc u)) as wit.
      { apply wf_isexc; auto. }
      assert (cover_vars (mk_isexc u) s1) as cvit.
      { apply cover_vars_isexc; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      apply member_isexc_iff; auto.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp3.
    rw @tequality_mkc_equality_sp in hyp0; repnd.
    sp.

  -  vr_seq_true in hyp2.
    pose proof (hyp2 (snoc (snoc s1 (x,mkc_axiom)) (y,mkc_axiom))
                    (snoc (snoc s2 (x,mkc_axiom)) (y,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').
     dands.

    { (* Hyp Functionality *)
      apply hyps_functionality_snoc2; simpl; auto.
      -  introv equ' sim'.
        lsubst_tac.
        (* have to use 
          rw (@similarity_snoc o) in sim'.
          while goal is still tequality.
          Because after apply tequality_mkc_isexc the
          exrepnd won't destruct the existential.
        *)
        apply (@similarity_snoc o) in sim'. simpl in sim'. exrepnd.
        apply tequality_mkc_isexc; split; auto.
        vr_seq_true in hyp5.       
        pose proof (hyp5 s1 s2a) as hyp. clear hyp5.
        repeat (autodimp hyp hyp');
        apply snoc_inj in sim'0; sp; subst; auto.
        lsubst_tac.
        apply tequality_mkc_member_base in p1.
        apply cequiv_stable in p1.
        eapply raises_exceptionc_preserves_cequivc.
        exact p1.
        auto.
     - apply hyps_functionality_snoc2; simpl; auto.
       introv equ' sim'.
        lsubst_tac.
        vr_seq_true in hyp4.
          pose proof (hyp4 s1 s') as hyp; clear hyp4.
          repeat (autodimp hyp hyp');[].
          exrepnd.
         lsubst_tac.
         apply tequality_mkc_member_base in hyp2.
         apply cequiv_stable in hyp2.
         eapply cequiv_member_int; eauto.
    } 

    { (* Similarity *) 
      assert (wf_term (mk_isexc v)) as wit. apply wf_isexc; auto.
      assert (cover_vars (mk_isexc v) (snoc s1 (x, mkc_axiom))) as cvit.
      { apply cover_vars_isexc; dands; auto.
       apply cover_vars_snoc_weak. auto. }
      assert (wf_term (mk_member u mk_int)) as wit2 by auto.
      assert (cover_vars (mk_member u mk_int) s1) as cvit2.
      { apply cover_vars_member; dands; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      sim_snoc.
      dands; auto.
      lsubst_tac.
      rw <- @member_member_iff.
      - eapply computes_to_integer_member_int; eauto.
      - lsubst_tac.
      apply member_isexc_iff. auto.
    }

   { (* Functionality and Truth *)
    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp7.
    rw @tequality_mkc_equality_sp in hyp2; repnd.
    sp.
   } 

Qed.

Lemma rule_minus_exception_cases_true {o} :
  forall lib (H : barehypotheses)
         (a b T t : @NTerm o)
         (x : NVar),
    rule_true lib (rule_minus_exception_cases H a b T t x).
Proof.
 unfold rule_minus_exception_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars t)
          # !LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3.
   dwfseq.
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nxu vhyps ].
  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa nxH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.
  
  lsubst_tac.
  allrw @tequality_mkc_isexc.
  allrw <- @member_isexc_iff.
  applydup hyp0 in hyp1.
  clear hyp0.
  rw <- @member_equality_iff.
  rw @tequality_mkc_equality_sp.

  apply @if_raises_exceptionc_minus  in hyp1.
  apply @if_raises_exceptionc_minus  in hyp4.
  
 - vr_seq_true in hyp2.
    pose proof (hyp2 (snoc s1 (x,mkc_axiom)) (snoc s2 (x,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      apply tequality_mkc_isexc.
      split; intro h; auto. GC;[].

      vr_seq_true in hyp3.

      pose proof (hyp3 s1 s') as hyp; clear hyp4.
      repeat (autodimp hyp hyp');[].
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp0.
      apply cequiv_stable in hyp0.
      eapply raises_exceptionc_preserves_cequivc;[exact hyp0|]; auto.
    }

    { assert (wf_term (mk_isexc t)) as wit.
      { apply wf_isexc; auto. }
      assert (cover_vars (mk_isexc t) s1) as cvit.
      { apply cover_vars_isexc; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      apply member_isexc_iff; auto.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp2.
    rw @tequality_mkc_equality_sp in hyp0; repnd.
    sp.
Qed.
  
(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
