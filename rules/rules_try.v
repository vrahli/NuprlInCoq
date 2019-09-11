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
Require Export cequiv_props5.



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
     H, v : Base |- c ∈ Base
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
        (mk_conclax (mk_member n mk_base)),
      mk_baresequent
        (snoc H (mk_hyp v mk_base))
        (mk_conclax (mk_member c mk_base))
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
  rename Hyp5 into hyp_cbase.

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
          # !LIn x (free_vars t)
          # !LIn x (free_vars n)
          # (x <> v -> !LIn x (free_vars c))
          # !LIn x (vars_hyps H)

          # !LIn y (free_vars T)
          # !LIn y (free_vars b)
          # !LIn y (free_vars a)
          # !LIn y (free_vars t)
          # !LIn y (free_vars n)
          # (y <> v -> !LIn y (free_vars c))
          # !LIn y (vars_hyps H)

          # !LIn m (free_vars T)
          # !LIn m (free_vars b)
          # !LIn m (free_vars a)
          # !LIn m (free_vars t)
          # !LIn m (free_vars n)
          # (m <> v -> !LIn m (free_vars c))
          # !LIn m (vars_hyps H)

          # !LIn u (free_vars T)
          # !LIn u (free_vars b)
          # !LIn u (free_vars a)
          # !LIn u (free_vars t)
          # !LIn u (free_vars n)
          # (u <> v -> !LIn u (free_vars c))
          # !LIn u (vars_hyps H)

          # m <> u
          # m <> x
          # m <> y

          # u <> x
          # u <> y

          # x <> y

          # !LIn v (vars_hyps H)) as vhyps.

  {
    clear hyp_halts_try hyp_halts hyp_exc hyp_tbase hyp_nbase hyp_cbase.
    dwfseq.
    sp; GC;
      try (complete (discover; allapply @subset_hs_vars_hyps; sp));
      try (complete (pose proof (ct4 x) as q; rw in_remove_nvars in q;
                     simpl in q; autodimp q hyp; tcsp));
      try (complete (pose proof (ct4 y) as q; rw in_remove_nvars in q;
                     simpl in q; autodimp q hyp; tcsp));
      try (complete (pose proof (ct4 m) as q; rw in_remove_nvars in q;
                     simpl in q; autodimp q hyp; tcsp));
      try (complete (pose proof (ct4 u) as q; rw in_remove_nvars in q;
                     simpl in q; autodimp q hyp; tcsp)).
  }

  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa vhyps ].
  destruct vhyps as [ nxt vhyps ].
  destruct vhyps as [ nxn vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nxH vhyps ].

  destruct vhyps as [ nyT vhyps ].
  destruct vhyps as [ nyb vhyps ].
  destruct vhyps as [ nya vhyps ].
  destruct vhyps as [ nyt vhyps ].
  destruct vhyps as [ nyn vhyps ].
  destruct vhyps as [ nyc vhyps ].
  destruct vhyps as [ nyH vhyps ].

  destruct vhyps as [ nmT vhyps ].
  destruct vhyps as [ nmb vhyps ].
  destruct vhyps as [ nma vhyps ].
  destruct vhyps as [ nmt vhyps ].
  destruct vhyps as [ nmn vhyps ].
  destruct vhyps as [ nmc vhyps ].
  destruct vhyps as [ nmH vhyps ].

  destruct vhyps as [ nuT vhyps ].
  destruct vhyps as [ nub vhyps ].
  destruct vhyps as [ nua vhyps ].
  destruct vhyps as [ nut vhyps ].
  destruct vhyps as [ nun vhyps ].
  destruct vhyps as [ nuc vhyps ].
  destruct vhyps as [ nuH vhyps ].

  destruct vhyps as [ dmu vhyps ].
  destruct vhyps as [ dmx vhyps ].
  destruct vhyps as [ dmy vhyps ].
  destruct vhyps as [ dux vhyps ].
  destruct vhyps as [ duy vhyps ].
  destruct vhyps as [ dxy vhyps ].

  rename vhyps into nvH.
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

  pose proof (hasvaluec_mkc_try2_implies
                lib
                (lsubstc t w0 s1 c0)
                (lsubstc t w0 s2 c5)
                (lsubstc n w2 s1 c2)
                (lsubstc n w2 s2 c6)
                v
                (lsubstc_vars c w3 (csub_filter s1 [v]) [v] c3)
                (lsubstc_vars c w3 (csub_filter s2 [v]) [v] c7)
             ) as q.
  repeat (autodimp q hyp).

  {
    vr_seq_true in hyp_tbase.
    pose proof (hyp_tbase s1 s2 eqh sim) as hyp_tbase.
    exrepnd.
    lsubst_tac.
    apply cequiv_stable.
    apply tequality_mkc_member_base in hyp_tbase0; auto.
  }

  repndors; exrepnd;[|].

  {
    vr_seq_true in hyp_halts.
    pose proof (hyp_halts
                  (snoc (snoc s1 (x, mkc_axiom)) (y, mkc_axiom))
                  (snoc (snoc s2 (x, mkc_axiom)) (y, mkc_axiom))
               ) as hyp_halts.

    repeat (autodimp hyp_halts hyp).

    {
      (* hyps_functionality *)
      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        lsubst_tac.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1a x mkc_axiom [v] c19) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd.
        rewrite lvcs0; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s2a x t2 [v] c24) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd.
        rewrite lvcs0; clear lvcs0.

        proof_irr.

        apply equality_in_mkc_cequiv in equ'; repnd.
        clear equ'0 equ'1; spcast.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1a x mkc_axiom [v] c19) as xx.
        simpl in xx.
        autodimp xx hyp.
        exrepnd; proof_irr.
        rewrite xx0 in equ'; clear xx0.

        apply tequality_mkc_cequiv; split; intro h; auto; spcast; GC; auto;
          try (complete (apply reduces_toc_implies_cequivc; auto)).

        vr_seq_true in hyp_tbase.
        pose proof (hyp_tbase s1a s2a eqh sim'3) as hyp_tbase.
        exrepnd.
        lsubst_tac.
        clear hyp_tbase1.
        apply tequality_mkc_member_base in hyp_tbase0; auto.
        apply cequiv_stable; spcast.

        vr_seq_true in hyp_nbase.
        pose proof (hyp_nbase s1a s2a eqh sim'3) as hyp_nbase.
        exrepnd.
        lsubst_tac.
        clear hyp_nbase1.
        apply tequality_mkc_member_base in hyp_nbase0; auto.
        apply cequiv_stable; spcast.

        pose proof (implies_cequivc_try
                      lib
                      (lsubstc t w0 s1a c0) (lsubstc t w0 s2a c22)
                      (lsubstc n w2 s1a c2) (lsubstc n w2 s2a c23)
                      v
                      (lsubstc_vars c w3 (csub_filter s1a [v]) [v] c3)
                      (lsubstc_vars c w3 (csub_filter s2a [v]) [v] cv'0)
                   ) as ceqtry1.
        repeat (autodimp ceqtry1 hyp).

        {
          introv.
          repeat substc_lsubstc_vars3.
          vr_seq_true in hyp_cbase.
          pose proof (hyp_cbase (snoc s1a (v,u0)) (snoc s2a (v,u0))) as hyp_cbase.
          repeat (autodimp hyp_cbase hyp).

          {
            apply hyps_functionality_snoc2; simpl; auto.
            introv equ'' sim''.
            lsubst_tac; auto.
          }

          {
            sim_snoc; dands; auto.
            lsubst_tac; auto.
            apply equality_in_base_iff; spcast; eauto 3 with slow.
          }

          exrepnd.
          lsubst_tac.
          clear hyp_cbase1.
          apply tequality_mkc_member_base in hyp_cbase0; auto.
          apply cequiv_stable; spcast.

          pose proof (lsubstc_snoc_move c s1a [] v u0 w3) as e1.
          allrw app_nil_r.
          pose proof (e1 ct5) as e1.
          autodimp e1 hyp.

          {
            apply similarity_dom in sim; repnd.
            rewrite sim0; auto.
          }

          exrepnd; proof_irr; rewrite <- e0; clear e0.

          pose proof (lsubstc_snoc_move c s2a [] v u0 w3) as e2.
          allrw app_nil_r.
          pose proof (e2 ct6) as e2.
          autodimp e2 hyp.

          {
            apply similarity_dom in sim'3; repnd.
            rewrite sim'3; auto.
          }

          exrepnd; proof_irr; rewrite <- e0; clear e0.
          auto.
        }

        eapply cequivc_trans;[apply cequivc_sym;exact ceqtry1|].
        clear ceqtry1.

        pose proof (implies_cequivc_atom_eq
                      lib
                      (lsubstc n w2 s1a c2)
                      (lsubstc n w2 s2a c23)
                      (lsubstc n w2 s1a c2)
                      (lsubstc n w2 s2a c23)
                      (lsubstc t w0 s1a c0)
                      (lsubstc t w0 s2a c22)
                      mkc_bottom
                      mkc_bottom
                   ) as ceqatomeq1.

        eapply cequivc_trans;[|apply ceqatomeq1]; auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        lsubst_tac.
        apply tequality_mkc_halts.

        vr_seq_true in hyp_tbase.
        pose proof (hyp_tbase s1 s' eqh sim') as hyp_tbase.
        exrepnd.
        lsubst_tac.
        clear hyp_tbase1.
        apply tequality_mkc_member_base in hyp_tbase0; auto.
        spcast.

        split; intro h.
        - eapply cequivc_preserves_chaltsc;[apply hyp_tbase0|]; auto.
        - eapply cequivc_preserves_chaltsc;[apply cequivc_sym; apply hyp_tbase0|]; auto.
      }
    }

    {
      (* similarity *)
      sim_snoc2.

      { apply wf_cequiv; auto.
        apply wf_atom_eq; auto. }

      { apply cover_vars_cequiv; dands; auto.
        - apply cover_vars_try; dands; auto.
          { apply cover_vars_snoc_weak; auto. }
          { apply cover_vars_snoc_weak; auto. }
          { apply cover_vars_upto_csub_filter_snoc_weak; auto. }
        -  apply cover_vars_atom_eq; dands; auto;
             try (complete (apply cover_vars_snoc_weak; auto)).
      }

      dands; auto.

      {
        sim_snoc2.

        { apply wf_halts; auto. }

        { apply cover_vars_halts; auto. }

        dands; auto.
        lsubst_tac.
        apply member_halts_iff; spcast.
        eapply reduces_toc_iscvalue_implies_hasvaluec; eauto.
      }

      lsubst_tac.
      apply member_cequiv.

      pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1 x mkc_axiom [v] c19) as xx.
      simpl in xx.
      autodimp xx hyp.
      exrepnd; proof_irr.
      rewrite xx0; clear xx0.

      apply reduces_toc_implies_cequivc in q6.
      eapply cequivc_trans;[apply q6|].
      apply implies_cequivc_atom_eq; eauto 3 with slow.
      apply cequivc_sym.
      apply reduces_toc_implies_cequivc; auto.
    }

    exrepnd.
    lsubst_tac.
    dands; auto.
  }

  {
    vr_seq_true in hyp_exc.
    pose proof (hyp_exc
                  (snoc (snoc (snoc (snoc s1 (m, m1)) (u, u1)) (x, mkc_axiom)) (y, mkc_axiom))
                  (snoc (snoc (snoc (snoc s2 (m, m2)) (u, u2)) (x, mkc_axiom)) (y, mkc_axiom))
               ) as hyp_exc.

    repeat (autodimp hyp_exc hyp).

    {
      (* hyps_functionality *)
      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'4; simpl in sim'4.
        exrepnd; subst; ginv; inj.
        Time lsubst_tac.
        (* this lsubst_tac is way too slow *)

        apply equality_in_mkc_cequiv in equ'; repnd.
        apply equality_in_mkc_cequiv in sim'1; repnd.
        clear equ'0 equ'1 sim'0 sim'4; spcast; GC.

        apply tequality_mkc_cequiv.

        split; intro h; spcast; auto; GC;[].

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc (snoc s1a (m,t3)) (u,t1)) x mkc_axiom [v] c24) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0 in equ'; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc s1a (m,t3)) u t1 [v] cv') as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0 in equ'; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1a m t3 [v] cv'0) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0 in equ'; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc (snoc s2a (m,t4)) (u,t0)) x t2 [v] c31) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc s2a (m,t4)) u t0 [v] cv'1) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s2a m t4 [v] cv'2) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0; clear lvcs0.

        vr_seq_true in hyp_tbase.
        pose proof (hyp_tbase s1a s2a eqh sim'5) as hyp_tbase.
        exrepnd.
        lsubst_tac.
        clear hyp_tbase1.
        apply tequality_mkc_member_base in hyp_tbase0; auto.
        apply cequiv_stable; spcast.

        vr_seq_true in hyp_nbase.
        pose proof (hyp_nbase s1a s2a eqh sim'5) as hyp_nbase.
        exrepnd.
        lsubst_tac.
        clear hyp_nbase1.
        apply tequality_mkc_member_base in hyp_nbase0; auto.
        apply cequiv_stable; spcast.

        pose proof (implies_cequivc_try
                      lib
                      (lsubstc t w0 s1a c0) (lsubstc t w0 s2a c37)
                      (lsubstc n w2 s1a c2) (lsubstc n w2 s2a c40)
                      v
                      (lsubstc_vars c w3 (csub_filter s1a [v]) [v] c3)
                      (lsubstc_vars c w3 (csub_filter s2a [v]) [v] cv'3)
                   ) as ceqtry1.
        repeat (autodimp ceqtry1 hyp).

        {
          introv.
          repeat (substc_lsubstc_vars3;[]).
          vr_seq_true in hyp_cbase.
          pose proof (hyp_cbase (snoc s1a (v,u0)) (snoc s2a (v,u0))) as hyp_cbase.
          repeat (autodimp hyp_cbase hyp).

          {
            apply hyps_functionality_snoc2; simpl; auto.
            introv equ'' sim''.
            lsubst_tac; auto.
          }

          {
            sim_snoc; dands; auto.
            lsubst_tac; auto.
            apply equality_in_base_iff; spcast; eauto 3 with slow.
          }

          exrepnd.
          lsubst_tac.
          clear hyp_cbase1.
          apply tequality_mkc_member_base in hyp_cbase0; auto.
          apply cequiv_stable; spcast.

          pose proof (lsubstc_snoc_move c s1a [] v u0 w3) as e1.
          allrw app_nil_r.
          pose proof (e1 ct5) as e1.
          autodimp e1 hyp.

          {
            apply similarity_dom in sim; repnd.
            rewrite sim0; auto.
          }

          exrepnd; proof_irr; rewrite <- e0; clear e0.

          pose proof (lsubstc_snoc_move c s2a [] v u0 w3) as e2.
          allrw app_nil_r.
          pose proof (e2 ct6) as e2.
          autodimp e2 hyp.

          {
            apply similarity_dom in sim'5; repnd.
            rewrite sim'5; auto.
          }

          exrepnd; proof_irr; rewrite <- e0; clear e0.
          auto.
        }

        eapply cequivc_trans;[apply cequivc_sym;exact ceqtry1|].
        clear ceqtry1.

        eapply cequivc_trans;[apply equ'|].

        apply equality_in_base_iff in sim'3.
        apply cequiv_stable; spcast.

        apply equality_in_base in sim'2; apply cequiv_stable; spcast.

        apply implies_cequivc_atom_eq; auto;
          try (apply implies_cequivc_exception; auto).

        assert (!LIn x (free_vars (subst c v (mk_var u)))) as nixsc.
        {
          intro i.
          pose proof (eqvars_free_vars_disjoint c [(v,mk_var u)]) as xx.
          simpl in xx.
          apply eqvars_is_eqset in xx; apply xx in i; clear xx.
          apply in_app_iff in i; rw in_remove_nvars in i; simpl in i; rw not_over_or in i.
          repndors; repnd.
          { autodimp nxc hyp; tcsp. }
          { boolvar; simpl in *; tcsp. }
        }

        pose proof (subset_free_vars_lsubstc_snoc_ex
                      (subst c v (mk_var u))
                      (snoc (snoc s1a (m, t3)) (u, t1))
                      x mkc_axiom w11 c19 nixsc
                   ) as xx.
        exrepnd; rewrite xx0; clear xx0; proof_irr.

        pose proof (subset_free_vars_lsubstc_snoc_ex
                      (subst c v (mk_var u))
                      (snoc (snoc s2a (m, t4)) (u, t0))
                      x t2 w11 c26 nixsc
                   ) as xx.
        exrepnd; rewrite xx0; clear xx0; proof_irr.

        applydup @similarity_dom in sim'5; repnd.

        pose proof (lsubstc_subst_snoc_aeq
                      (snoc s1a (m, t3)) c v u t1 w11 w3 c'0 cv'0) as xx.
        rw @dom_csub_snoc in xx.
        rw in_snoc in xx.
        repeat (autodimp xx hyp).
        { simpl; rewrite sim'4; tcsp. }
        eapply cequivc_trans;[apply alphaeqc_implies_cequivc;exact xx|]; clear xx.

        pose proof (lsubstc_subst_snoc_aeq
                      (snoc s2a (m, t4)) c v u t0 w11 w3 c'1 cv'2) as xx.
        rw @dom_csub_snoc in xx.
        rw in_snoc in xx.
        repeat (autodimp xx hyp).
        { simpl; rewrite sim'0; tcsp. }
        eapply cequivc_trans;[|apply cequivc_sym;apply alphaeqc_implies_cequivc;exact xx]; clear xx.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1a m t3 [v] cv'0) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s2a m t4 [v] cv'2) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd; proof_irr.
        rewrite lvcs0; clear lvcs0.

        substc_lsubstc_vars3.
        substc_lsubstc_vars3.
        vr_seq_true in hyp_cbase.
        pose proof (hyp_cbase (snoc s1a (v,t1)) (snoc s2a (v,t0))) as hyp_cbase.
        repeat (autodimp hyp_cbase hyp).

        {
          apply hyps_functionality_snoc2; simpl; auto.
          introv equ'' sim''.
          lsubst_tac; auto.
        }

        {
          sim_snoc; dands; auto.
          lsubst_tac; auto.
          apply equality_in_base_iff; spcast; eauto 3 with slow.
        }

        exrepnd.
        lsubst_tac.
        clear hyp_cbase1.
        apply tequality_mkc_member_base in hyp_cbase0; auto.
        apply cequiv_stable; spcast.

        pose proof (lsubstc_snoc_move c s1a [] v t1 w3) as e1.
        allrw app_nil_r.
        pose proof (e1 ct5) as e1.
        autodimp e1 hyp.

        {
          apply similarity_dom in sim; repnd.
          rewrite sim0; auto.
        }

        exrepnd; proof_irr; rewrite <- e0; clear e0.

        pose proof (lsubstc_snoc_move c s2a [] v t0 w3) as e2.
        allrw app_nil_r.
        pose proof (e2 ct6) as e2.
        autodimp e2 hyp.

        {
          rewrite sim'0; auto.
        }

        exrepnd; proof_irr; rewrite <- e0; clear e0.
        auto.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        apply similarity_snoc in sim'3; simpl in sim'3.
        exrepnd; subst; ginv; inj.
        Time lsubst_tac.
        (* this lsubst_tac is way too slow *)

        vr_seq_true in hyp_tbase.
        pose proof (hyp_tbase s1a s2a0 eqh sim'4) as hyp_tbase.
        exrepnd.
        lsubst_tac.
        clear hyp_tbase1.
        apply tequality_mkc_member_base in hyp_tbase0; auto; spcast.

        apply equality_in_base_iff in sim'1.
        apply equality_in_base_iff in sim'2.
        spcast.

        apply tequality_mkc_cequiv.
        split; intro h; spcast.

        {
          eapply cequivc_trans;[apply cequiv_sym;exact hyp_tbase0|].
          eapply cequivc_trans;[exact h|].
          apply implies_cequivc_exception; auto.
        }

        {
          eapply cequivc_trans;[exact hyp_tbase0|].
          eapply cequivc_trans;[exact h|].
          apply cequivc_sym.
          apply implies_cequivc_exception; auto.
        }
      }

      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        Time lsubst_tac.
        eauto 3 with slow.
      }

      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        Time lsubst_tac.
        eauto 3 with slow.
      }
    }

    {
      (* similarity *)

      vr_seq_true in hyp_tbase.
      pose proof (hyp_tbase s1 s2 eqh sim) as hyp_tbase.
      exrepnd.
      lsubst_tac.
      clear hyp_tbase1.
      apply tequality_mkc_member_base in hyp_tbase0; auto; spcast.
      eapply cequivc_trans in hyp_tbase0;
        [|apply cequivc_sym;apply reduces_toc_implies_cequivc;exact q0].
      apply cequivc_sym in hyp_tbase0.
      eapply cequivc_trans in hyp_tbase0;
        [|apply cequivc_sym;apply reduces_toc_implies_cequivc;exact q2].

      apply cequivc_sym in hyp_tbase0.
      apply cequivc_exception_implies in hyp_tbase0; repnd.

      sim_snoc2.

      {
        apply wf_cequiv.
        { apply wf_try; auto. }
        { apply wf_atom_eq; dands; auto.
          apply wf_term_subst; auto. }
      }

      {
        apply cover_vars_cequiv; dands; auto.
        { apply cover_vars_try; dands; auto;
            try (complete (repeat (apply cover_vars_snoc_weak; auto))).
          repeat (apply cover_vars_upto_csub_filter_snoc_weak; auto).
        }
        { apply cover_vars_atom_eq; dands; auto;
            try (complete (repeat (apply cover_vars_snoc_weak; auto))).
          { apply cover_vars_var.
            repeat (rw @dom_csub_snoc); simpl.
            repeat (rw in_snoc); tcsp. }
          { apply cover_vars_lsubst_if; simpl.
            { repeat (rw @dom_csub_snoc); simpl.
              unfold cover_vars_upto in c3.
              eapply subvars_trans;[exact c3|]; simpl.
              rw @dom_csub_csub_filter.
              apply subvars_cons_lr.
              apply subvars_remove_nvars.
              apply subvars_app_weak_l.
              repeat (apply subvars_snoc_weak); auto.
            }
            { introv i; repndors; tcsp; ginv.
              apply cover_vars_var.
              repeat (rw @dom_csub_snoc); simpl.
              repeat (rw in_snoc); tcsp.
            }
          }
          { unfold cover_vars, over_vars; simpl.
            repeat (rw @dom_csub_snoc); simpl.
            rw subvars_eq.
            unfold subset; simpl; introv i.
            repeat (rw in_snoc); tcsp.
          }
        }
      }

      dands; auto.

      {
        sim_snoc2.

        { apply wf_cequiv; auto. }

        { apply cover_vars_cequiv; dands; auto;
            try (complete (repeat (apply cover_vars_snoc_weak; auto))).
          unfold cover_vars, over_vars; simpl.
          repeat (rw @dom_csub_snoc); simpl.
          rw subvars_eq.
          unfold subset; simpl; introv i.
          repeat (rw in_snoc); tcsp.
        }

        dands; auto.

        {
          sim_snoc2.
          dands; auto.

          {
            sim_snoc2.
            dands; auto.
            lsubst_tac.
            apply equality_in_base_iff; spcast; auto.
          }

          lsubst_tac.
          apply equality_in_base_iff; spcast; auto.
        }

        lsubst_tac.
        apply member_cequiv.
        apply reduces_toc_implies_cequivc; auto.
      }

      lsubst_tac.
      apply member_cequiv.

      pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc (snoc s1 (m,m1)) (u,u1)) x mkc_axiom [v] c20) as lvcs.
      simpl in lvcs; autodimp lvcs hyp.
      exrepnd; proof_irr.
      rewrite lvcs0; clear lvcs0.

      pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 (snoc s1 (m,m1)) u u1 [v] cv') as lvcs.
      simpl in lvcs; autodimp lvcs hyp.
      exrepnd; proof_irr.
      rewrite lvcs0; clear lvcs0.

      pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1 m m1 [v] cv'0) as lvcs.
      simpl in lvcs; autodimp lvcs hyp.
      exrepnd; proof_irr.
      rewrite lvcs0; clear lvcs0.

      eapply cequivc_trans;[apply reduces_toc_implies_cequivc;exact q3|].

      apply implies_cequivc_atom_eq; auto;
        try (apply implies_cequivc_exception; auto).

      assert (!LIn x (free_vars (subst c v (mk_var u)))) as nixsc.
      {
        intro i.
        pose proof (eqvars_free_vars_disjoint c [(v,mk_var u)]) as xx.
        simpl in xx.
        apply eqvars_is_eqset in xx; apply xx in i; clear xx.
        apply in_app_iff in i; rw in_remove_nvars in i; simpl in i; rw not_over_or in i.
        repndors; repnd.
        { autodimp nxc hyp; tcsp. }
        { boolvar; simpl in *; tcsp. }
      }

      pose proof (subset_free_vars_lsubstc_snoc_ex
                    (subst c v (mk_var u))
                    (snoc (snoc s1 (m, m1)) (u, u1))
                    x mkc_axiom w6 c15 nixsc
                 ) as xx.
      exrepnd; rewrite xx0; clear xx0; proof_irr.

      applydup @similarity_dom in sim; repnd.

      pose proof (lsubstc_subst_snoc_aeq
                    (snoc s1 (m, m1)) c v u u1 w6 w3 c' cv'0) as xx.
      rw @dom_csub_snoc in xx.
      rw in_snoc in xx.
      repeat (autodimp xx hyp).
      { simpl; rewrite sim1; tcsp. }
      apply cequivc_sym.
      eapply cequivc_trans;[apply alphaeqc_implies_cequivc;exact xx|]; clear xx.

      pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1 m m1 [v] cv'0) as lvcs.
      simpl in lvcs; autodimp lvcs hyp.
      exrepnd; proof_irr.
      rewrite lvcs0; clear lvcs0.

      eauto 3 with slow.
    }

    exrepnd.
    lsubst_tac.
    dands; auto.
  }
Qed.
