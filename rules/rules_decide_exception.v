(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export computation_injections.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.


(*
   H |- a = b in T

     By DecideExceptionCases

     H |- isexc(case t inl(x) => u; inr(y) => v)
     H, z : t in Top + Top |- a = b in T
     H, z : isexc(t) |- a = b in T
     H |- t in Base
 *)
Definition rule_decide_exception_cases {o}
           (H : barehypotheses)
           (a b T t u v: @NTerm o)
           (x y z : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_decide t x u y v))),
      mk_baresequent (snoc H (mk_hyp z (mk_member t (mk_union mk_top mk_top))))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc H (mk_hyp z (mk_isexc t)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent H (mk_conclax (mk_member t mk_base))
    ]
    [].

Lemma rule_decide_exception_cases_true {o} :
  forall lib (H : barehypotheses)
         (a b T t u v : @NTerm o)
         (x y z : NVar),
    rule_true lib (rule_decide_exception_cases H a b T t u v x y z).
Proof.
  unfold rule_decide_exception_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality a b T))) as cs.
  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn z (free_vars t)
          # !LIn z (free_vars T)
          # !LIn z (free_vars b)
          # !LIn z (free_vars a)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nzt vhyps ].
  destruct vhyps as [ nzT vhyps ].
  destruct vhyps as [ nzb vhyps ].
  destruct vhyps as [ nza nzH ].
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
  rw @tequality_mkc_equality.

  apply if_raises_exceptionc_decide0 in hyp1.
  repndors; exrepnd.

  - vr_seq_true in hyp3.
    pose proof (hyp3 (snoc s1 (z,mkc_axiom)) (snoc s2 (z,mkc_axiom))) as hyp.
    clear hyp3.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      clear equ'.
      apply tequality_mkc_isexc.
      split; intro h; auto; GC;[].

      vr_seq_true in hyp4.

      pose proof (hyp4 s1 s') as hyp; clear hyp4.
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
    rw <- @member_equality_iff in hyp3.
    rw @tequality_mkc_equality in hyp0; repnd.
    sp.

  - vr_seq_true in hyp2.
    pose proof (hyp2 (snoc s1 (z,mkc_axiom)) (snoc s2 (z,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      vr_seq_true in hyp4.
        pose proof (hyp4 s1 s') as hyp; clear hyp4.
        repeat (autodimp hyp hyp').
        exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp2; spcast.
        repeat (rw <- @fold_mkc_member).
        apply tequality_equality_if_cequivc; auto;
        apply tequality_mkc_union; split;
        rw @fold_type;
        apply type_mkc_top.
    }

    { assert (wf_term (mk_member t (mk_union mk_top mk_top))) as wit by auto.
      assert (cover_vars (mk_member t (mk_union mk_top mk_top)) s1) as cvit.
      { apply cover_vars_member; dands; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      rw <- @member_member_iff.
      apply equality_mkc_union; dands; eauto 3 with slow.
      left. exists a0 a0. dands; spcast; eauto 3 with slow.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp6.
    rw @tequality_mkc_equality in hyp2; repnd.
    sp.

  - vr_seq_true in hyp2.
    pose proof (hyp2 (snoc s1 (z,mkc_axiom)) (snoc s2 (z,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      vr_seq_true in hyp4.
        pose proof (hyp4 s1 s') as hyp; clear hyp4.
        repeat (autodimp hyp hyp').
        exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp2; spcast.
        repeat (rw <- @fold_mkc_member).
        apply tequality_equality_if_cequivc; auto;
        apply tequality_mkc_union; split;
        rw @fold_type;
        apply type_mkc_top.
      
    }

    { assert (wf_term (mk_member t (mk_union mk_top mk_top))) as wit by auto.
      assert (cover_vars (mk_member t (mk_union mk_top mk_top)) s1) as cvit.
      { apply cover_vars_member; dands; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      rw <- @member_member_iff.
      apply equality_mkc_union; dands; eauto 3 with slow.
      right. exists a0 a0. dands; spcast; eauto 3 with slow.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp6.
    rw @tequality_mkc_equality in hyp2; repnd.
    sp.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
