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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export computation_pair.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.


(*
   H |- C

     By ExceptionNotBottom

     H |- exc(a,b) <= bot
 *)
Definition rule_exception_not_bottom {o}
           (H : barehypotheses)
           (C a b : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax C))
    [ mk_baresequent H (mk_conclax (mk_approx (mk_exception a b) mk_bot))
    ]
    [].

Lemma rule_exception_not_bottom_true {o} :
  forall lib (H : barehypotheses)
         (C a b : @NTerm o),
    rule_true lib (rule_exception_not_bottom H C a b).
Proof.
  unfold rule_exception_not_bottom, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax C)) as cs.
  clear hyp1.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.

  provefalse.
  lsubst_tac.
  allrw <- @equality_in_approx; repnd; spcast.
  apply not_value_like_approxc_bot in hyp2; eauto 3 with slow.
Qed.


(*
   H |- C

     By ExceptionNotAxiom

     H |- Ax <= exc(a,b)
 *)
Definition rule_exception_not_axiom {o}
           (H : barehypotheses)
           (C a b : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax C))
    [ mk_baresequent H (mk_conclax (mk_approx mk_axiom (mk_exception a b)))
    ]
    [].

Lemma rule_exception_not_axiom_true {o} :
  forall lib (H : barehypotheses)
         (C a b : @NTerm o),
    rule_true lib (rule_exception_not_axiom H C a b).
Proof.
  unfold rule_exception_not_axiom, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax C)) as cs.
  clear hyp1.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.

  provefalse.
  lsubst_tac.
  allrw <- @equality_in_approx; repnd; spcast.
  apply approxc_decomp_axiom0 in hyp2.
  apply computes_to_valc_exception in hyp2; sp.
Qed.


(*
   H |- C ext c

     By ExceptionSqequal

     H |- exc(n,e) <= t
     H, [u : Base], [v : Base], [x : t ~ exc(u,v)] |- C ext c
     H, u : Base, v : Base, |- t ~ exc(u,v) in Type(i)
 *)
Definition rule_exception_sqequal {o}
           (H : barehypotheses)
           (C c n e t : @NTerm o)
           (u v x : NVar)
           (i : nat) :=
  mk_rule
    (mk_baresequent H (mk_concl C c))
    [ mk_baresequent H (mk_conclax (mk_approx (mk_exception n e) t)),
      mk_baresequent (snoc (snoc (snoc H (mk_hhyp u mk_base))
                                 (mk_hhyp v mk_base))
                           (mk_hhyp x (mk_cequiv t (mk_exception (mk_var u) (mk_var v)))))
                     (mk_concl C c),
      mk_baresequent (snoc (snoc H (mk_hyp u mk_base)) (mk_hyp v mk_base))
                     (mk_conclax (mk_member (mk_cequiv t (mk_exception (mk_var u) (mk_var v))) (mk_uni i)))
    ]
    [].

Lemma rule_exception_sqequal_true {o} :
  forall lib (H : barehypotheses)
         (C c n e t : @NTerm o)
         (u v x : NVar)
         (i : nat),
    rule_true lib (rule_exception_sqequal H C c n e t u v x i).
Proof.
  unfold rule_exception_sqequal, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_concl C c)) as cs.
  clear hyp1 hyp2 hyp3.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn u (free_vars t)
          # !LIn v (free_vars t)
          # !LIn x (free_vars t)
          # !LIn u (free_vars n)
          # !LIn v (free_vars n)
          # !LIn x (free_vars n)
          # !LIn u (free_vars e)
          # !LIn v (free_vars e)
          # !LIn x (free_vars e)
          # !LIn u (free_vars C)
          # !LIn v (free_vars C)
          # !LIn x (free_vars C)
          # !LIn u (free_vars c)
          # !LIn v (free_vars c)
          # !LIn x (free_vars c)
          # !LIn u (vars_hyps H)
          # !LIn v (vars_hyps H)
          # !LIn x (vars_hyps H)
          # u <> v
          # u <> x
          # v <> x) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nut vhyps ].
  destruct vhyps as [ nvt vhyps ].
  destruct vhyps as [ nxt vhyps ].
  destruct vhyps as [ nun vhyps ].
  destruct vhyps as [ nvn vhyps ].
  destruct vhyps as [ nxn vhyps ].
  destruct vhyps as [ nue vhyps ].
  destruct vhyps as [ nve vhyps ].
  destruct vhyps as [ nxe vhyps ].
  destruct vhyps as [ nuC vhyps ].
  destruct vhyps as [ nvC vhyps ].
  destruct vhyps as [ neC vhyps ].
  destruct vhyps as [ nuc vhyps ].
  destruct vhyps as [ nvc vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nuH vhyps ].
  destruct vhyps as [ nvH vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nuv vhyps ].
  destruct vhyps as [ nux nvx ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.

  lsubst_tac.
  allrw <- @member_approx_iff.
  allrw @tequality_mkc_approx.
  applydup hyp0 in hyp1.
  clear hyp0.
  spcast.

  allrw <- @member_equality_iff.
  applydup @approxc_exc_implies_ex in hyp1.
  applydup @approxc_exc_implies_ex in hyp4.
  exrepnd.

  vr_seq_true in hyp2.
  pose proof (hyp2 (snoc (snoc (snoc s1 (u,a0)) (v,b0)) (x,mkc_axiom))
                   (snoc (snoc (snoc s2 (u,a0)) (v,b0)) (x,mkc_axiom))
             ) as hyp; clear hyp2.

  repeat autodimp hyp hyp'.

  { apply hyps_functionality_snoc2; simpl; auto.

    - introv equ' sim'.
      lsubst_tac.
      apply similarity_snoc in sim';
 simpl in sim'. exrepnd. subst; ginv; cpx.
      apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; subst; ginv; cpx.
      lsubst_tac.

      vr_seq_true in hyp3.
      pose proof (hyp3 (snoc (snoc s1a  (u,t0)) (v,t1))
                       (snoc (snoc s2a0 (u,t3)) (v,t2))
                 ) as hyp; clear hyp3.

      repeat autodimp hyp hyp'.

      { apply hyps_functionality_snoc2; simpl; auto.

        - introv equ'' sim''.
          lsubst_tac; eauto 3 with slow.

        - apply hyps_functionality_snoc2; simpl; auto.
          introv equ''' sim'''.
          lsubst_tac; eauto 3 with slow.
      }

      { apply similarity_snoc; simpl.
        exists (snoc s1a (u,t0)) (snoc s2a0 (u,t3)) t1 t2 w7 p.
        dands; auto.

        - apply similarity_snoc; simpl.
          exists s1a s2a0 t0 t3 w7 p0.
          dands; auto.
          lsubst_tac; auto.

        - lsubst_tac; auto.
      }

      { exrepnd.
        lsubst_tac.
        dup hyp3 as h3.
        apply inhabited_implies_tequality in hyp3.
        apply tequality_mkc_cequiv.
        apply tequality_in_uni_implies_tequality in hyp2.
       rw @tequality_mkc_cequiv in hyp2; auto.
       apply member_member_iff. auto.
       
       }

    - apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        lsubst_tac; auto. }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        lsubst_tac; auto. }
  }

  { assert (wf_term (mk_cequiv t (mk_exception (mk_var u) (mk_var v)))) as wc.
    { apply wf_cequiv; auto. }

    assert (cover_vars (mk_cequiv t (mk_exception (mk_var u) (mk_var v)))
                       (snoc (snoc s1 (u, a0)) (v, b0))) as cvc.
    { apply cover_vars_cequiv; dands; eauto 3 with slow.
      - repeat (apply cover_vars_snoc_weak); auto.
      - apply cover_vars_exception; dands; eauto 3 with slow;
        apply cover_vars_var; allrw @dom_csub_snoc; simpl;
        apply in_snoc; tcsp.
        left; apply in_snoc; tcsp.
    }

    sim_snoc.
    dands; auto.

    - pose proof (@wf_base o) as wb.
      pose proof (cover_vars_base (snoc s1 (u,a0))) as cb.
      sim_snoc.
      dands; auto.

      + pose proof (cover_vars_base s1) as cb2.
        sim_snoc.
        dands; auto.
        lsubst_tac.
        apply member_base.

      + lsubst_tac.
        apply member_base.

    - lsubst_tac.
      apply member_cequiv_iff; spcast.
      apply reduces_toc_implies_cequivc; auto.
  }

  exrepnd.
  lsubst_tac.
  dands; auto.
Qed.


(*
   H |- n + exc(a,b) ~ exc(a,b)

     By AddException

     H |- n in Int
 *)
Definition rule_add_exception {o}
           (H : barehypotheses)
           (n a b : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv (mk_add n (mk_exception a b)) (mk_exception a b))))
    [ mk_baresequent H (mk_conclax (mk_member n mk_int))
    ]
    [].

Lemma rule_add_exception_true {o} :
  forall lib (H : barehypotheses)
         (n a b : @NTerm o),
    rule_true lib (rule_add_exception H n a b).
Proof.
  unfold rule_add_exception, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_cequiv (mk_add n (mk_exception a b)) (mk_exception a b)))) as cs.
  clear hyp1.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd.

  lsubst_tac.
  rw <- @member_cequiv_iff.
  rw @tequality_mkc_cequiv.
  allrw <- @member_member_iff.
  allrw @tequality_mkc_member.
  repnd.
(*
  allrw @fold_equorsq.
  eapply cequorsq_equality_trans2 in hyp0;[|exact hyp1].
  clear hyp1 hyp2. *)

  assert (ccequivc
            lib
            (mkc_add (lsubstc n wt s1 ct0)
                     (mkc_exception (lsubstc a w0 s1 c0) (lsubstc b w3 s1 c3)))
            (mkc_exception (lsubstc a w0 s1 c0) (lsubstc b w3 s1 c3))) as ceq1.
  { apply equality_in_int in hyp0; auto.
    unfold equality_of_int in hyp0; exrepnd; spcast.
    eapply cequivc_trans;
      [apply implies_cequivc_mkc_add;
        [apply computes_to_valc_implies_cequivc;exact hyp0
        |apply cequivc_refl]
      |].
    apply reduces_toc_implies_cequivc.
    apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  }

  assert (ccequivc
            lib
            (mkc_add (lsubstc n wt s2 ct1)
                     (mkc_exception (lsubstc a w0 s2 c6) (lsubstc b w3 s2 c7)))
            (mkc_exception (lsubstc a w0 s2 c6) (lsubstc b w3 s2 c7))) as ceq2.
  { apply equality_in_int in hyp0; auto.
    unfold equality_of_int in hyp0; exrepnd; spcast.
    eapply cequivc_trans;
      [apply implies_cequivc_mkc_add;
        [apply computes_to_valc_implies_cequivc;exact hyp4
        |apply cequivc_refl]
      |].
    apply reduces_toc_implies_cequivc.
    apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  }

  dands; auto.
  split; sp.
Qed.

(* !!Move *)
Lemma wf_top {o} : @wf_term o mk_top.
Proof. sp. Qed.


(*
   H |- a = b in T

     By SpreadExceptionCases

     H |- isexc(let x,y = t in u)
     H, z : t in Top x Top |- a = b in T
     H, z : isexc(t) |- a = b in T
     H |- t in Base
 *)
Definition rule_spread_exception_cases {o}
           (H : barehypotheses)
           (a b T t u : @NTerm o)
           (x y z : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_spread t x y u))),
      mk_baresequent (snoc H (mk_hyp z (mk_member t (mk_prod mk_top mk_top))))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc H (mk_hyp z (mk_isexc t)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent H (mk_conclax (mk_member t mk_base))
    ]
    [].

Lemma rule_spread_exception_cases_true {o} :
  forall lib (H : barehypotheses)
         (a b T t u  : @NTerm o)
         (x y z : NVar),
    rule_true lib (rule_spread_exception_cases H a b T t u x y z).
Proof.
  unfold rule_spread_exception_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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

  apply if_raises_exceptionc_spread0 in hyp1.
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
      apply tequality_mkc_member_if_cequivc.

      dands.

      - eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;
          apply (lsubstc_mk_prod mk_top mk_top s1 wf_top wf_top wT0 (cover_vars_top s1) (cover_vars_top s1) cT1)
        |].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;
            apply (lsubstc_mk_prod mk_top mk_top s' wf_top wf_top wT0 (cover_vars_top s') (cover_vars_top s') cT2)
           |].
        allrw @lsubstc_mk_top.
        apply type_mkc_prod; dands; eauto 3 with slow.

      - vr_seq_true in hyp4.
        pose proof (hyp4 s1 s') as hyp; clear hyp4.
        repeat (autodimp hyp hyp').
        exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp2.
        apply cequiv_stable. auto.
    }

    { assert (wf_term (mk_member t (mk_prod mk_top mk_top))) as wit by auto.
      assert (cover_vars (mk_member t (mk_prod mk_top mk_top)) s1) as cvit.
      { apply cover_vars_member; dands; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      rw <- @member_member_iff.
      eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;
           apply (lsubstc_mk_prod mk_top mk_top s1 wf_top wf_top wT0 (cover_vars_top s1) (cover_vars_top s1) cT1)
        ].
      allrw @lsubstc_mk_top.
      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp0|].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp0|].
      apply equality_in_prod; dands; eauto 3 with slow.
      exists a0 a0 b0 b0; dands; eauto 3 with slow;
      spcast; apply computes_to_valc_refl; eauto 3 with slow.
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
