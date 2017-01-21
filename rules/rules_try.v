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
Require Export per_can.
Require Export computation_cbv.
Require Export cequiv_props2.


Lemma hasvaluec_mkc_try_implies {o} :
  forall lib t n v (c : @CVTerm o [v]),
    hasvaluec lib (mkc_try t n v c)
    ->
    (
      {u : CTerm
       & reduces_toc lib t u
       # iscvalue u
       # reduces_toc lib (mkc_try t n v c) (mkc_atom_eq n n u mkc_bottom)
      }
      [+]
      {m : CTerm
       & {u : CTerm
       & reduces_toc lib t (mkc_exception m u)
       # reduces_toc lib (mkc_try t n v c) (mkc_atom_eq n m (substc u v c) (mkc_exception m u))
      } }
    ).
Proof.
  introv hv.
  destruct_cterms; simpl in *.
  unfold reduces_toc; simpl.
  unfold hasvaluec in *; simpl in *.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  unfold reduces_to in hv1; exrepnd.
  unfold iscvalue; simpl.

  revert dependent x0.

  induction k; introv ispx0 r.

  {
    allrw @reduces_in_atmost_k_steps_0; subst.
    inversion hv0; subst; simpl in *; tcsp.
  }

  {
    allrw @reduces_in_atmost_k_steps_S; exrepnd.

    csunf r1; simpl in *.

    destruct x0 as [z|F|op bs]; ginv.

    {
      left.
      exists (mk_ct (sterm F) ispx0); simpl.
      dands; eauto 3 with slow.
    }

    {
      dopid op as [can|ncan|exc|abs] Case; simpl; ginv; auto.

      - left.
        exists (mk_ct (oterm (Can can) bs) ispx0); simpl.
        dands; eauto 3 with slow.

      - remember (compute_step lib (oterm (NCan ncan) bs)) as cs.
        destruct cs; simpl in *; ginv.
        symmetry in Heqcs.
        fold_terms.
        applydup @preserve_compute_step in Heqcs; eauto 2 with slow.
        applydup IHk in r0; auto; eauto 2 with slow;[].
        repndors; exrepnd; destruct_cterms; simpl in *.

        + left.
          exists (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

        + right.
          exists (mk_ct x2 i2) (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

      - destruct bs as [|b1 bs]; simpl in *; ginv.
        destruct b1 as [l1 t1]; simpl in *; ginv.
        destruct l1 as [|v1 l1]; simpl in *; ginv.
        destruct bs as [|b2 bs]; simpl in *; ginv.
        destruct b2 as [l2 t2]; simpl in *; ginv.
        destruct l2 as [|v2 l2]; simpl in *; ginv.
        destruct bs as [|]; simpl in *; ginv.
        fold_terms.
        right.

        allrw @isprog_exception_iff; repnd.
        exists (mk_ct t1 ispx1) (mk_ct t2 ispx0); simpl.
        dands; eauto 2 with slow.

      - remember (compute_step lib (oterm (Abs abs) bs)) as cs.
        destruct cs; simpl in *; ginv.
        symmetry in Heqcs.
        fold_terms.
        applydup @preserve_compute_step in Heqcs; eauto 2 with slow.
        applydup IHk in r0; auto; eauto 2 with slow;[].
        repndors; exrepnd; destruct_cterms; simpl in *.

        + left.
          exists (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

        + right.
          exists (mk_ct x2 i2) (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.
    }
  }
Qed.

(*
   H |- a = b ∈ T

     By haltsTry

     H |- (mk_try(t,n,v.c))↓
     H, x : (t)↓,
        y : mk_try(t,n,v.c) ~ if n=n then t else bottom |- a = b ∈ T
     H, m : Base,
        u : Base,
        x : t ~ exception(m,u),
        y : mk_try(t,n,v.c) ~ if n=m then c[v\u] else exception(m,u) |- a = b ∈ T
     H |- t ∈ Base
     H |- n ∈ Base
 *)
Definition rule_halts_try_cases {o}
           (H : barehypotheses)
           (a b T t n c : @NTerm o)
           (v x y u m : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [
      mk_baresequent H (mk_conclax (mk_halts (mk_try t n v c))),
      mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_halts t)))
              (mk_hyp y (mk_cequiv (mk_try t n v c) (mk_atom_eq n n t mk_bottom))))
        (mk_conclax (mk_equality a b T)),
      mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp m mk_base))
                          (mk_hyp u mk_base))
                    (mk_hyp x (mk_cequiv t (mk_exception (mk_var m) (mk_var u)))))
              (mk_hyp y (mk_cequiv (mk_try t n v c) (mk_atom_eq n (mk_var m) (subst c v (mk_var u)) (mk_exception (mk_var m) (mk_var u))))))
        (mk_conclax (mk_equality a b T)),
      mk_baresequent
        H
        (mk_conclax (mk_member t mk_base)),
      mk_baresequent
        H
        (mk_conclax (mk_member n mk_base))
    ]
    [].


Lemma rule_halts_try_cases_true {o} :
  forall lib
         (a b T t n c : NTerm)
         (v x y u m : NVar)
         (H : @barehypotheses o),
    rule_true lib (rule_halts_try_cases H a b T t n c v x y u m).
Proof.
  unfold rule_halts_try_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp_halts_try.
  rename Hyp1 into hyp_halts.
  rename Hyp2 into hyp_exc.
  rename Hyp3 into hyp_tbase.
  rename Hyp4 into hyp_nbase.

  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality a b T))) as cs.
  {
    unfold closed_extract; simpl.
    apply covered_axiom.
  }

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (vars_hyps H)) as vhyps.

  {
    clear hyp_halts_try hyp_halts hyp_exc hyp_tbase hyp_nbase.
    dwfseq.
    sp; GC;
      try (complete (discover; allapply @subset_hs_vars_hyps; sp)).
  }

  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa nxH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp_halts_try.
  pose proof (hyp_halts_try s1 s2 eqh sim) as hyp_halts_try.
  exrepnd.

  lsubst_tac.

  apply tequality_mkc_halts in hyp_halts_try0.
  apply equality_in_halts in hyp_halts_try1; repnd.
  clear hyp_halts_try3 hyp_halts_try1.
  applydup hyp_halts_try0 in hyp_halts_try2.
  clear hyp_halts_try0.
  spcast.

  Require Export computation11.

  applydup @hasvaluec_mkc_try_implies in hyp_halts_try2.
  repndors; exrepnd.

  {
    
  }

XXXXXXXXXXXXX


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
