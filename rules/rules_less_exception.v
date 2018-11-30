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


Require Export sequents_tacs2.
Require Export cequiv_props.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export per_can.
Require Export computation_less.
Require Export integer_type.



(* [18] ============ LESS EXCEPTION CASES ============ *)

(*   H |- a = b in T

     By ispairExceptionCases

     H |- isexc(if n < m then u else v )
     H, x : n in Z, y: m in Z |- a = b in T
     H, x : n in Z, y: is-exception(m) |- a = b in T
     H, x : is-exception(n) |- a = b in T
     H |- n in Base
     H |- m in Base
 *)
Definition rule_less_exception_cases {o}
           (H : barehypotheses)
           (a b T n m u v: @NTerm o)
           (x y: NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_isexc (mk_less n m u v))),
      mk_baresequent (snoc (snoc H (mk_hyp x (mk_member n mk_int)))
                                   (mk_hyp y (mk_member m mk_int) ))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc (snoc H (mk_hyp x (mk_member n mk_int)))
                                   (mk_hyp y (mk_isexc m)))
                     (mk_conclax (mk_equality a b T)),
      mk_baresequent (snoc H (mk_hyp x (mk_isexc n)))
                     (mk_conclax (mk_equality a b T)), 
      mk_baresequent H (mk_conclax (mk_member n mk_base)),
      mk_baresequent H (mk_conclax (mk_member m mk_base))
    ]
    [].     
   


Lemma rule_less_exception_cases_true {o} :
  forall lib (a b T n m u v : NTerm),
  forall x y : NVar,
  forall H : @barehypotheses o,
    rule_true lib (rule_less_exception_cases H a b T n m u v x y).
Proof.
  unfold rule_less_exception_cases, rule_true, closed_type_baresequent,
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
  rename Hyp4 into hyp5.
  rename Hyp5 into hyp6.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality a b T))) as cs.
  clear hyp1 hyp2 hyp3 hyp4 hyp5 hyp6.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars n)
          # !LIn x (free_vars m)
          # !LIn x (free_vars u)
          # !LIn x (free_vars v)
          # !LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (vars_hyps H)
          # (x <> y)
          # !LIn y (free_vars n)
          # !LIn y (free_vars m)
          # !LIn y (free_vars u)
          # !LIn y (free_vars v)
          # !LIn y (free_vars T)
          # !LIn y (free_vars b)
          # !LIn y (free_vars a)
          # !LIn y (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4 hyp5 hyp6.
   dwfseq.
  sp; GC;
  try (complete (discover; allapply @subset_hs_vars_hyps; sp)).

  destruct vhyps as [ nxn vhyps ].
  destruct vhyps as [ nxm vhyps ].
  destruct vhyps as [ nxu vhyps ].
  destruct vhyps as [ nxv vhyps ].
  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nyn vhyps ].
  destruct vhyps as [ nym vhyps ].
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
  rw @tequality_mkc_equality.
 


  apply if_raises_exceptionc_less in hyp1.
  repndors; exrepnd.

  - (* n raises exception, so use hyp4 *) 
    vr_seq_true in hyp4.
    pose proof (hyp4 (snoc s1 (x, mkc_axiom)) (snoc s2 (x, mkc_axiom)) ) as hyp.
    clear hyp4.
    repeat (autodimp hyp hyp').

    { apply @hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      apply tequality_mkc_isexc; auto.
      split; intro h; auto. GC;[].
      { 
       (* use the hyp5 says n in Base *)
        vr_seq_true in hyp5.
        pose proof (hyp5 s1 s' ) as hyp.
        clear hyp5.
        repeat (autodimp hyp hyp').
        exrepnd.
        lsubst_tac.   
        apply tequality_mkc_member_base in hyp0.
        apply cequiv_stable in hyp0.
        generalize_lsubstc_terms n'.
        pose proof (@raises_exceptionc_preserves_cequivc o lib (lsubstc n wm s1 cm) n') as xx. 
        apply xx; auto.
      }  
      
     } 
    { assert (wf_term (mk_isexc n))as wit.
      { apply wf_isexc; auto. }
      assert (cover_vars (mk_isexc n) s1) as cvit.
      { apply cover_vars_isexc; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      apply member_isexc_iff; auto.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp4.
    rw @tequality_mkc_equality in hyp0; repnd.
    sp.
 

  - (* n in Z, m raises exception  so we use hyp3 *)
     assert (wf_term (mk_member n mk_int)) as wit by (eauto 3 with slow).
     assert (wf_term (mk_isexc m)) as wit2 by (apply wf_isexc; auto).
    vr_seq_true in hyp3.
     pose proof (hyp3 (snoc (snoc s1 (x,mkc_axiom))(y,mkc_axiom))
                     (snoc (snoc s2 (x,mkc_axiom)) (y,mkc_axiom))) as hyp.
    clear hyp3.
    repeat (autodimp hyp hyp').
    
    

   
    { (* Hyp Functionality *)
      apply hyps_functionality_snoc2; simpl; auto.
      - introv equ' sim'.
        lsubst_tac.
       apply (@similarity_snoc o) in sim'. simpl in sim'. exrepnd.
        apply tequality_mkc_isexc.
       vr_seq_true in hyp6.       
        pose proof (hyp6 s1 s2a) as hyp. clear hyp6.
        repeat (autodimp hyp hyp');
        apply snoc_inj in sim'0; sp; subst; auto.
        lsubst_tac.
        apply tequality_mkc_member_base in p1.
        apply cequiv_stable in p1.
        split; auto.
        eapply raises_exceptionc_preserves_cequivc. exact p1.
     - apply hyps_functionality_snoc2; simpl; auto.
       introv equ' sim'.
        lsubst_tac.
        vr_seq_true in hyp5.
          pose proof (hyp5 s1 s') as hyp; clear hyp5.
          repeat (autodimp hyp hyp');[].
          exrepnd.
         lsubst_tac.
         apply tequality_mkc_member_base in hyp3.
         apply cequiv_stable in hyp3.
         eapply cequiv_member_int; eauto.
     
    }
    
     { (* Similarity *) 
    assert (cover_vars (mk_isexc m) (snoc s1 (x, mkc_axiom)) ) as cvrs.
    {apply cover_vars_isexc; dands; auto.
       apply cover_vars_snoc_weak. auto. }
    sim_snoc; sp; lsubst_tac.
    assert (cover_vars (mk_member n mk_int) s1) as cvrs2.
      { apply cover_vars_member; dands; auto. }
    sim_snoc. dands; auto. 
    lsubst_tac.
    rw <- @member_member_iff.
   eapply computes_to_integer_member_int; eauto.
   apply member_isexc_iff; auto.
   } 
    { (* Functionality and Truth *)
    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp8.
    rw @tequality_mkc_equality in hyp3; repnd.
    sp.
   }
 - (* Both n and m are integers. Use hyp2. *)
     assert (wf_term (mk_member n mk_int)) as wit by (eauto 3 with slow).
     assert (wf_term (mk_member m mk_int)) as wit2 by (eauto 3 with slow).
    vr_seq_true in hyp2.
     pose proof (hyp2 (snoc (snoc s1 (x,mkc_axiom))(y,mkc_axiom))
                     (snoc (snoc s2 (x,mkc_axiom)) (y,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').
        
    { (* Hyp Functionality *)
      apply hyps_functionality_snoc2; simpl; auto.
      - introv equ' sim'.
        lsubst_tac.
       apply (@similarity_snoc o) in sim'. simpl in sim'. exrepnd.
       eapply @cequiv_member_int; eauto.
       vr_seq_true in hyp6.       
        pose proof (hyp6 s1 s2a) as hyp. clear hyp6.
        repeat (autodimp hyp hyp');
        apply snoc_inj in sim'0; sp; subst; auto.
        lsubst_tac.
        apply tequality_mkc_member_base in p1.
        apply cequiv_stable in p1. auto.
     - apply hyps_functionality_snoc2; simpl; auto.
       introv equ' sim'.
        lsubst_tac.
       eapply @cequiv_member_int; eauto.
       vr_seq_true in hyp5.       
        pose proof (hyp5 s1 s') as hyp. clear hyp5.
        repeat (autodimp hyp hyp'). exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp2.
        apply cequiv_stable in hyp2. auto.
    }
    
    { (* Similarity *) 
    assert (cover_vars (mk_member m mk_int) (snoc s1 (x, mkc_axiom)) ) as cvrs.
    { apply cover_vars_member; dands; auto;
       apply cover_vars_snoc_weak; auto. }
    sim_snoc; sp; lsubst_tac.
    assert (cover_vars (mk_member n mk_int) s1) as cvrs2.
      { apply cover_vars_member; dands; auto. }
    sim_snoc. dands; auto; 
    lsubst_tac;
    rw <- @member_member_iff;
    eapply computes_to_integer_member_int; eauto.

    rw <- @member_member_iff;
    eapply computes_to_integer_member_int; eauto. 
   } 
    { (* Functionality and Truth *)
    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp8.
    rw @tequality_mkc_equality in hyp2; repnd.
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
