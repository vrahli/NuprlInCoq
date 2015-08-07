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


Require Export chalts.
Require Export sequents_tacs2.
Require Export cequiv_props.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export per_can.
Require Export computation_cbv.
Require Export cequiv_props2.


(* [18] ============ CALLBYVALUE EXCEPTION CASES ============ *)

(*   H |- a = b in T

     By callbyvalueExceptionCases

     H |- isexc(eval y = t in u)
     H, x : has_value(t) |- a = b in T
     H, x : isexc(t) |- a = b in T
     H |- t in Base
 *)
Definition rule_cbv_exception_cases {o}
           (H : barehypotheses)
           (a b T t u : @NTerm o)
           (x y: NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_cbv  t y u))),
      mk_baresequent (snoc H (mk_hyp x ( mk_halts t)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc H (mk_hyp x (mk_isexc t)))
                     (mk_conclax (mk_equality a b T)), 
      mk_baresequent H (mk_conclax (mk_member t mk_base))
    ]
    [].


Lemma rule_cbv_exception_cases_true {o} :
  forall lib  (a b T t u : NTerm),
  forall x y : NVar,
  forall H : @barehypotheses o,
    rule_true lib (rule_cbv_exception_cases H a b T t u x y).
Proof.
  unfold rule_cbv_exception_cases, rule_true, closed_type_baresequent,
                closed_extract_baresequent; simpl.
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
  assert (!LIn x (remove_nvars [y] (free_vars u))
          # !LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4.
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

  apply if_raises_exceptionc_cbv in hyp1.
  repndors; exrepnd.

  - (* t raises exception *) 
    vr_seq_true in hyp3.
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

    { assert (wf_term (mk_isexc t))as wit.
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
    rw @tequality_mkc_equality_sp in hyp0; repnd.
    sp.

  - (* t has a value,  so we use hyp2 *)
    vr_seq_true in hyp2.
     pose proof (hyp2 (snoc s1 (x,mkc_axiom)) (snoc s2 (x,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').
     { (* Hyp Functionality *)
      apply hyps_functionality_snoc2; simpl; auto.
      -  introv equ' sim'.
        lsubst_tac.
     (* because by hyp4, t in Base,  halts(t) is well formed *)

      vr_seq_true in hyp4.

      pose proof (hyp4 s1 s') as hyp; clear hyp4.
      repeat (autodimp hyp hyp');[].
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp0.
      apply cequiv_stable in hyp0.
      generalize_lsubstc_terms t1.
      generalize_lsubstc_terms t2.
       apply tequality_mkc_halts.
      split; introv hlts.
      apply cequivc_preserves_chaltsc in hyp0; auto.
      apply cequivc_sym in hyp0.
      apply cequivc_preserves_chaltsc in hyp0; auto.
      } 
    { (* Similarity *) 
      assert (wf_term (mk_halts t)) as wit. apply wf_halts; auto.
      assert (cover_vars (mk_halts t) s1) as cvit.
      { apply cover_vars_halts; dands; auto.
      }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      apply equality_in_halts.
      sp; spcast; try (apply computes_to_valc_refl); eauto 3 with slow.
    }

   { (* Functionality and Truth *)
    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp2.
    rw @tequality_mkc_equality_sp in hyp0; repnd.
    sp.
   }  
Qed.
   
    

 

(* begin hide *)

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
