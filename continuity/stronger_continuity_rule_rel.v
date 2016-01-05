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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export stronger_continuity_rule4_v3.

Definition spMp_rel {o} (F : @NTerm o) :=
  spMp (mk_lam nvarf (mk_pi1 (mk_apply F (mk_var nvarf)))).

Definition functional_rel {o} (P T : @NTerm o) f n :=
  mk_all
    (mk_nat2T T)
    f
    (mk_psqexists mk_tnat n (mk_apply2 P (mk_var f) (mk_var n))).

Definition strong_continuous_type_gen {o} (x M f n : NVar) (F P : @NTerm o) T :=
  mk_psqexists
    (mod_fun_type_v2 x T)
    M
    (mk_all
       (mk_nat2T T)
       f
       (mk_prod
          (mk_sqexists
             mk_tnat
             n
             (mk_equality
                (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
                (mk_apply F (mk_var f))
                mk_natU))
          (mk_all
             mk_tnat
             n
             (mk_ufun
                (mk_isint (mk_apply2 (mk_var M) (mk_var n) (mk_var f)) mk_true mk_false)
                (mk_equality
                   (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
                   (mk_apply F (mk_var f))
                   mk_tnat))))).

Definition rule_strong_continuity_rel {o}
           (F T t P : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_concl (strong_continuous_type2_v3 x M f n F T)
                                  (spMp_rel F)))
      [ mk_baresequent H (mk_conclax (mk_member F (functional_rel P T f n))),
        mk_baresequent H (mk_conclax (mk_member t T)) ]
      [].

Lemma rule_strong_continuity_true2_v3 {p} :
  forall lib
         (F T t : NTerm)
         (x M f n : NVar)
         (H : @barehypotheses p)
         (d1 : M <> f)
         (d2 : n <> f)
         (d3 : n <> M)
         (d4 : !LIn M (free_vars F))
         (d5 : !LIn f (free_vars F))
         (d6 : !LIn n (free_vars F))
         (d7 : !LIn x (free_vars T))
         (d8 : !LIn M (free_vars T))
         (d9  : !LIn nvare (free_vars F))
         (d10 : !LIn nvarf (free_vars F))
         (d11 : !LIn nvarn (free_vars F))
         (cov : covered F (nh_vars_hyps H))
         (nut : has_eq_value_type_nut_sim lib H T),
    rule_true lib (rule_strong_continuity2_v3
                     F T t
                     x M f n
                     H).
Proof.
  unfold rule_strong_continuity2_v3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  dup ct0 as cmF.
  apply covered_equality in cmF; repnd.
  clear cmF1 cmF.

  pose proof (covered_spM F (nh_vars_hyps H)) as cF.
  repeat (autodimp cF hyp).
  applydup cF in cov.
  apply covered_spM_iff_spMp in cov0.

  exists cov0.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hTT; exrepnd; clear hyp2.

  allunfold @strong_continuous_type2_v3.
  allunfold @mk_psqexists.
  allunfold @mk_sqexists.
  repeat lift_lsubsts_squash.
  lsubst_tac.

  apply equality_in_member in hTT1; repnd.
  apply tequality_mkc_member in hTT0; repnd.
  applydup hTT5 in hTT1.
  applydup @tequality_refl in hTT4.
  applydup @tequality_sym in hTT4.
  apply @tequality_refl in hTT8.
  clear hTT0 hTT2 hTT3 hTT5.
  allrw @fold_type.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member in h0; repnd.
  applydup h3 in h1.
  allrw @fold_equorsq.
  clear h2 h3.

  pose proof (lsubstc_spMp F wfce s1 pt1) as spMe1.
  repeat (autodimp spMe1 hyp);[].
  exrepnd; rw spMe1.

  pose proof (lsubstc_spMp F wfce s2 pt2) as spMe2.
  repeat (autodimp spMe2 hyp);[].
  exrepnd; rw spMe2.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  eapply member_respects_alphaeqc_r in h1;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
  eapply respects_alphaeqc_equorsq3 in h0;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
  eapply member_respects_alphaeqc_r in h4;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)].

  dup h1 as memF.
  eapply cequorsq_equality_trans1 in memF;[|apply equorsq_sym;exact h0].
  apply equality_sym in memF.
  rename h4 into memF'.
  clear h0.

  pose proof (nut wT s1 cT) as nut1.
  repeat (autodimp nut1 hyp); auto.
  { eapply similarity_refl; eauto. }
  pose proof (nut wT s2 cT0) as nut2.
  repeat (autodimp nut2 hyp); auto.
  { apply similarity_sym in sim; auto.
    eapply similarity_refl; eauto. }
  { eapply similarity_hyps_functionality_trans; eauto. }

  match goal with
      [ |- tequality ?l (mkc_psquash ?x) (mkc_psquash ?y) # _ ] =>
      assert (tequality l x y) as teq
  end.

  - unfold mk_exists.
    lsubst_tac.

    apply tequality_product.
    dands.

    + eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c6 wT cT);auto|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c8 wT cT0);auto|].
      apply tequality_modulus_fun_type_u_v2; auto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c6 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)|].
        apply tequality_nat2T; auto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply tequality_mkc_prod; dands.

        { apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intro inh; clear inh.
          allrw @lsubstc_mkc_tnat.
          apply tequality_function; dands.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.
          allrw @lsubstc_mk_true.
          allrw @lsubstc_mk_false.
          allrw @lsubstc_mk_tnat.
          apply tequality_mkc_ufun; dands.

          { pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_disjoint_bunion in h; eauto 3 with slow.
            repnd; clear h0 h2.
            repndors.

            - apply equality_in_tnat in h.
              unfold equality_of_nat in h; exrepnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              apply type_mkc_true.

            - apply equality_in_unit in h; repnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              apply tequality_false.
          }

          { introv inh.
            pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

  - dands.

    { apply sp_implies_tequality_mkc_psquash; auto. }

    apply equality_in_mkc_psquash; dands.

    {
    unfold mk_exists.
    lsubst_tac.

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c6 wT cT);auto|].
      apply tequality_modulus_fun_type_u_v2; eauto 3 with slow.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c6 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)|].
        apply tequality_nat2T.
        eapply tequality_refl; eauto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply tequality_mkc_prod; dands.

        { apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intro inh; clear inh.
          allrw @lsubstc_mkc_tnat.
          apply tequality_function; dands.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.
          allrw @lsubstc_mk_true.
          allrw @lsubstc_mk_false.
          allrw @lsubstc_mk_tnat.
          apply tequality_mkc_ufun; dands.

          { pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_in_disjoint_bunion in h; eauto 3 with slow.
            repnd; clear h0 h2.
            repndors.

            - apply equality_in_tnat in h.
              unfold equality_of_nat in h; exrepnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              apply type_mkc_true.

            - apply equality_in_unit in h; repnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              apply tequality_false.
          }

          { introv inh.
            pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp).
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

    + eexists; eexists; eexists; eexists; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

      * eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c6 wT cT);auto].

        apply (spM_in_modulus_fun_type_u_v2 _ _ (lsubstc t wt s1 ct1)); auto.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)|].
          eauto 3 with slow.
          apply tequality_nat2T; eauto 3 with slow. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          apply tequality_mkc_prod; dands.

          { apply tequality_mkc_squash.
            allrw @lsubstc_mkc_tnat.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s1 ct3)
                            (lsubstc t wt s1 ct1)
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s1 ct3)
                          (lsubstc t wt s1 ct1)
                          (lsubstc T wT s1 cT)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f2
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f2
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }
        }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c4 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @mkcv_pair_substc.
          allrw @substc_mkcv_axiom.
          repeat (rw @mkcv_lam_substc; try (complete (introv xx; ginv));[]).
          allrw @mkcv_ax_eq.
          allrw @substc2_mk_cv.
          allrw @lsubstc_mkc_tnat.

          apply equality_in_prod.
          dands.

          { apply tequality_mkc_squash.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              applydup @equality_refl in en2n.
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s1 ct3)
                            (lsubstc t wt s1 ct1)
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_refl in memF; auto.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s1 ct3)
                          (lsubstc t wt s1 ct1)
                          (lsubstc T wT s1 cT)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f1
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f1
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp).
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }

          { exists (@mkc_axiom p) (@mkc_axiom p)
                   (@mkc_lam p nvarn (mk_cv [nvarn] mkc_axiom))
                   (@mkc_lam p nvarn (mk_cv [nvarn] mkc_axiom)).
            dands; spcast.
            { apply computes_to_valc_refl; eauto 3 with slow. }
            { apply computes_to_valc_refl; eauto 3 with slow. }

            { apply equality_in_mkc_squash; dands; spcast;
              try (apply computes_to_valc_refl; eauto 3 with slow);[].

              applydup @equality_refl in en2n as mf1.
              pose proof (spM_cond_v2
                            lib
                            (lsubstc F wt0 s1 ct3)
                            f1
                            (lsubstc T wT s1 cT)
                            h1 mf1) as h.
              exrepnd.

              allrw @lsubstc_mkc_tnat.

              exists (mkc_pair (mkc_nat n0) (@mkc_axiom p)).

              apply equality_in_product; dands; eauto 3 with slow.

              - intros n1 n2 en.
                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply tequality_mkc_equality_if_equal.

                { eapply tequality_respects_alphaeqc_left;
                  [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  eapply tequality_respects_alphaeqc_right;
                    [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  apply type_natU. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].

                  pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s1 ct3)
                                (lsubstc t wt s1 ct1)
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp);[].
                  rw @equality_in_function in h; repnd.
                  applydup h in en as e.
                  eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
                  rw @csubst_mk_cv in e.

                  try (fold (@natU p) in e).
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply substc_mkcv_fun].
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply mkcv_natk_substc
                    ].
                  allrw @mkc_var_substc.
                  allrw @mkcv_tnat_substc.

                  try (fold (natk2nat n1) in e).

                  applydup @equality_refl in en.
                  apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

                  apply equality_in_fun in e; repnd; clear e0 e1.
                  applydup @equality_refl in en2n as ef.
                  allrw @csubst_mk_cv.
                  apply e in ef.
                  allrw <- @mkc_apply2_eq; auto. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  apply equality_in_bunion_left; eauto 2 with slow. }

              - eexists; eexists; eexists; eexists; dands; spcast;
                try (apply computes_to_valc_refl; eauto 3 with slow);
                eauto 3 with slow.

                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply member_equality.
                eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                auto.
            }

            { apply equality_in_function3.
              dands; eauto 3 with slow;[].

              intros n1 n2 en.
              repeat substc_lsubstc_vars3.
              a_lsubst_tac.
              allrw @lsubstc_mk_true.
              allrw @lsubstc_mk_false.
              allrw @lsubstc_mkc_tnat.

              dands.

              - pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s1 ct3)
                                (lsubstc t wt s1 ct1)
                                (lsubstc T wT s1 cT)) as spMt.
                repeat (autodimp spMt hyp);[].
                apply tequality_mkc_ufun; dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

              - apply equality_in_ufun.
                pose proof (spM_in_modulus_fun_type_u_v2
                              lib
                              (lsubstc F wt0 s1 ct3)
                              (lsubstc t wt s1 ct1)
                              (lsubstc T wT s1 cT)) as spMt.
                repeat (autodimp spMt hyp);[].

                dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh; clear inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).
                  apply equality_refl in memF.
                  apply equality_in_fun in memF; repnd; clear memF0 memF1.
                  apply memF in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

                { introv inh.
                  eapply equality_respects_cequivc_left;
                    [apply cequivc_sym;apply cequivc_beta|].
                  eapply equality_respects_cequivc_right;
                    [apply cequivc_sym;apply cequivc_beta|].
                  allrw @csubst_mk_cv.

                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T wT s1 cT)) as h.
                  repeat (autodimp h hyp).

                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors; apply equality_refl in h.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.

                    apply equality_in_tnat in en.
                    unfold equality_of_nat in en; exrepnd; spcast.

                    pose proof (spM_cond2_v2
                                  lib (lsubstc F wt0 s1 ct3) f1 k0 k
                                  (lsubstc T wT s1 cT)) as cond2.
                    repeat (autodimp cond2 hyp).
                    { eapply cequivc_trans;
                      [apply implies_cequivc_apply2;
                        [apply cequivc_refl
                        |apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact en1
                        |apply cequivc_refl]
                      |].
                      apply computes_to_valc_implies_cequivc; auto. }
                    apply member_equality.

                    eapply equality_respects_cequivc_right;
                      [apply cequivc_sym;exact cond2|].

                    eapply equality_respects_cequivc_left;
                      [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2|].
                    eauto 3 with slow.

                  - apply equality_in_unit in h.
                    repnd; spcast.
                    eapply inhabited_type_cequivc in inh;
                      [|apply implies_cequivc_isint;
                         [apply computes_to_valc_implies_cequivc;exact h
                         |apply cequivc_refl
                         |apply cequivc_refl]
                      ].
                    eapply inhabited_type_cequivc in inh;
                      [|apply cequivc_mkc_isint_mkc_axiom].
                    unfold inhabited_type in inh; exrepnd.
                    apply false_not_inhabited in inh0; sp.
                }
            }
          }
        }
    }

    {
    eapply tequality_preserving_equality;[|apply tequality_sym;exact teq].
    clear teq.
    rw @member_eq.

    unfold mk_exists.
    lsubst_tac.

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c6 wT cT0);auto|].
      apply tequality_modulus_fun_type_u_v2; eauto 3 with slow.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c6 wT cT0);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)|].
        apply tequality_nat2T.
        eapply tequality_refl; eauto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.

        apply tequality_mkc_prod; dands.

        { apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
            apply memF' in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intro inh; clear inh.
          allrw @lsubstc_mkc_tnat.
          apply tequality_function; dands.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.
          allrw @lsubstc_mk_true.
          allrw @lsubstc_mk_false.
          allrw @lsubstc_mk_tnat.
          apply tequality_mkc_ufun; dands.

          { pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s2 cT0)) as h.
            repeat (autodimp h hyp).
            apply equality_in_disjoint_bunion in h; eauto 3 with slow.
            repnd; clear h0 h2.
            repndors.

            - apply equality_in_tnat in h.
              unfold equality_of_nat in h; exrepnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
              apply type_mkc_true.

            - apply equality_in_unit in h; repnd; spcast.
              eapply tequality_respects_cequivc_left;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_right;
                [apply implies_cequivc_isint;
                  [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                  |apply cequivc_refl
                  |apply cequivc_refl]
                |].
              eapply tequality_respects_cequivc_left;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              eapply tequality_respects_cequivc_right;
                [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
              apply tequality_false.
          }

          { introv inh.
            pose proof (equality_in_modulus_fun_type_u_implies_v2
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T wT s2 cT0)) as h.
            repeat (autodimp h hyp);[].
            apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
            apply memF' in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

    + eexists; eexists; eexists; eexists; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

      * eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c6 wT cT0);auto].

        apply (spM_in_modulus_fun_type_u_v2 _ _ (lsubstc t wt s2 ct2)); auto.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)|].
          eauto 3 with slow.
          apply tequality_nat2T; eauto 3 with slow. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          apply tequality_mkc_prod; dands.

          { apply tequality_mkc_squash.
            allrw @lsubstc_mkc_tnat.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s2 ct4)
                            (lsubstc t wt s2 ct2)
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
              apply memF' in en2n; auto.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s2 ct4)
                          (lsubstc t wt s2 ct2)
                          (lsubstc T wT s2 cT0)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s2 ct4))
                            (spM_c (lsubstc F wt0 s2 ct4))
                            n1 n2 f1 f2
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s2 ct4))
                            (spM_c (lsubstc F wt0 s2 ct4))
                            n1 n2 f1 f2
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
              apply memF' in en2n; auto.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }
        }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s2 c2 wT cT0)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @mkcv_pair_substc.
          allrw @substc_mkcv_axiom.
          repeat (rw @mkcv_lam_substc; try (complete (introv xx; ginv));[]).
          allrw @mkcv_ax_eq.
          allrw @substc2_mk_cv.
          allrw @lsubstc_mkc_tnat.

          apply equality_in_prod.
          dands.

          { apply tequality_mkc_squash.

            apply tequality_product; dands; eauto 3 with slow.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
                [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              applydup @equality_refl in en2n.
              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s2 ct4)
                            (lsubstc t wt s2 ct2)
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              eapply equality_in_modulus_fun_type_u_implies_v2; eauto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
              apply memF' in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_bunion_left; eauto 2 with slow. }
          }

          { intro inh; clear inh.
            allrw @lsubstc_mkc_tnat.
            apply tequality_function; dands.
            { apply type_tnat. }

            intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.
            allrw @lsubstc_mk_true.
            allrw @lsubstc_mk_false.
            allrw @lsubstc_mk_tnat.

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s2 ct4)
                          (lsubstc t wt s2 ct2)
                          (lsubstc T wT s2 cT0)) as spMt.
            repeat (autodimp spMt hyp);[].
            apply tequality_mkc_ufun; dands.

            { applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s2 ct4))
                            (spM_c (lsubstc F wt0 s2 ct4))
                            n1 n2 f1 f1
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_disjoint_bunion in h; eauto 3 with slow.
              repnd; clear h0 h2.
              repndors.

              - apply equality_in_tnat in h.
                unfold equality_of_nat in h; exrepnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                apply type_mkc_true.

              - apply equality_in_unit in h; repnd; spcast.
                eapply tequality_respects_cequivc_left;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_right;
                  [apply implies_cequivc_isint;
                    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                    |apply cequivc_refl
                    |apply cequivc_refl]
                  |].
                eapply tequality_respects_cequivc_left;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                eapply tequality_respects_cequivc_right;
                  [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                apply tequality_false.
            }

            { introv inh.
              applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s2 ct4))
                            (spM_c (lsubstc F wt0 s2 ct4))
                            n1 n2 f1 f1
                            (lsubstc T wT s2 cT0)) as h.
              repeat (autodimp h hyp);[].
              apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
              apply memF' in en2n; auto.
              applydup @equality_refl in en2n.
              apply equality_in_natU_implies_cequivc in h; spcast.
              apply equality_in_tnat_implies_cequivc in en2n.
              apply tequality_equality_if_cequivc; eauto 3 with slow.
              apply type_tnat.
            }
          }

          { exists (@mkc_axiom p) (@mkc_axiom p)
                   (@mkc_lam p nvarn (mk_cv [nvarn] mkc_axiom))
                   (@mkc_lam p nvarn (mk_cv [nvarn] mkc_axiom)).
            dands; spcast.
            { apply computes_to_valc_refl; eauto 3 with slow. }
            { apply computes_to_valc_refl; eauto 3 with slow. }

            { apply equality_in_mkc_squash; dands; spcast;
              try (apply computes_to_valc_refl; eauto 3 with slow);[].

              applydup @equality_refl in en2n as mf1.
              pose proof (spM_cond_v2
                            lib
                            (lsubstc F wt0 s2 ct4)
                            f1
                            (lsubstc T wT s2 cT0)
                            memF' mf1) as h.
              exrepnd.

              allrw @lsubstc_mkc_tnat.

              exists (mkc_pair (mkc_nat n0) (@mkc_axiom p)).

              apply equality_in_product; dands; eauto 3 with slow.

              - intros n1 n2 en.
                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply tequality_mkc_equality_if_equal.

                { eapply tequality_respects_alphaeqc_left;
                  [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  eapply tequality_respects_alphaeqc_right;
                    [apply alphaeqc_sym; apply lsubstc_mk_natU|].
                  apply type_natU. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].

                  pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s2 ct4)
                                (lsubstc t wt s2 ct2)
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].
                  rw @equality_in_function in h; repnd.
                  applydup h in en as e.
                  eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
                  rw @csubst_mk_cv in e.

                  try (fold (@natU p) in e).
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply substc_mkcv_fun].
                  eapply alphaeqc_preserving_equality in e;
                    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                      apply mkcv_natk_substc
                    ].
                  allrw @mkc_var_substc.
                  allrw @mkcv_tnat_substc.

                  try (fold (natk2nat n1) in e).

                  applydup @equality_refl in en.
                  apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

                  apply equality_in_fun in e; repnd; clear e0 e1.
                  applydup @equality_refl in en2n as ef.
                  allrw @csubst_mk_cv.
                  apply e in ef.
                  allrw <- @mkc_apply2_eq; auto. }

                { eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                  apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
                  apply memF' in en2n; auto.
                  apply equality_in_bunion_left; eauto 2 with slow. }

              - eexists; eexists; eexists; eexists; dands; spcast;
                try (apply computes_to_valc_refl; eauto 3 with slow);
                eauto 3 with slow.

                repeat substc_lsubstc_vars3.
                a_lsubst_tac.

                apply member_equality.
                eapply alphaeqc_preserving_equality;
                  [|apply alphaeqc_sym; apply lsubstc_mk_natU].
                auto.
            }

            { apply equality_in_function3.
              dands; eauto 3 with slow;[].

              intros n1 n2 en.
              repeat substc_lsubstc_vars3.
              a_lsubst_tac.
              allrw @lsubstc_mk_true.
              allrw @lsubstc_mk_false.
              allrw @lsubstc_mkc_tnat.

              dands.

              - pose proof (spM_in_modulus_fun_type_u_v2
                                lib
                                (lsubstc F wt0 s2 ct4)
                                (lsubstc t wt s2 ct2)
                                (lsubstc T wT s2 cT0)) as spMt.
                repeat (autodimp spMt hyp);[].
                apply tequality_mkc_ufun; dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s2 ct4))
                                (spM_c (lsubstc F wt0 s2 ct4))
                                n1 n2 f1 f1
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s2 ct4))
                                (spM_c (lsubstc F wt0 s2 ct4))
                                n1 n2 f1 f1
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].
                  apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
                  apply memF' in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

              - apply equality_in_ufun.
                pose proof (spM_in_modulus_fun_type_u_v2
                              lib
                              (lsubstc F wt0 s2 ct4)
                              (lsubstc t wt s2 ct2)
                              (lsubstc T wT s2 cT0)) as spMt.
                repeat (autodimp spMt hyp);[].

                dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s2 ct4))
                                (spM_c (lsubstc F wt0 s2 ct4))
                                n1 n2 f1 f1
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].
                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_nat|].
                    apply type_mkc_true.

                  - apply equality_in_unit in h; repnd; spcast.
                    eapply tequality_respects_cequivc_left;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_right;
                      [apply implies_cequivc_isint;
                        [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h0
                        |apply cequivc_refl
                        |apply cequivc_refl]
                      |].
                    eapply tequality_respects_cequivc_left;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    eapply tequality_respects_cequivc_right;
                      [apply cequivc_sym;apply cequivc_mkc_isint_mkc_axiom|].
                    apply tequality_false.
                }

                { introv inh; clear inh.
                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s2 ct4))
                                (spM_c (lsubstc F wt0 s2 ct4))
                                n1 n2 f1 f1
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].
                  apply equality_in_fun in memF'; repnd; clear memF'0 memF'1.
                  apply memF' in en2n; auto.
                  applydup @equality_refl in en2n.
                  apply equality_in_natU_implies_cequivc in h; spcast.
                  apply equality_in_tnat_implies_cequivc in en2n.
                  apply tequality_equality_if_cequivc; eauto 3 with slow.
                  apply type_tnat.
                }

                { introv inh.
                  eapply equality_respects_cequivc_left;
                    [apply cequivc_sym;apply cequivc_beta|].
                  eapply equality_respects_cequivc_right;
                    [apply cequivc_sym;apply cequivc_beta|].
                  allrw @csubst_mk_cv.

                  applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s2 ct4))
                                (spM_c (lsubstc F wt0 s2 ct4))
                                n1 n2 f1 f1
                                (lsubstc T wT s2 cT0)) as h.
                  repeat (autodimp h hyp);[].

                  apply equality_in_disjoint_bunion in h; eauto 3 with slow.
                  repnd; clear h0 h2.
                  repndors; apply equality_refl in h.

                  - apply equality_in_tnat in h.
                    unfold equality_of_nat in h; exrepnd; spcast.

                    apply equality_in_tnat in en.
                    unfold equality_of_nat in en; exrepnd; spcast.

                    pose proof (spM_cond2_v2
                                  lib (lsubstc F wt0 s2 ct4) f1 k0 k
                                  (lsubstc T wT s2 cT0)) as cond2.
                    repeat (autodimp cond2 hyp).
                    { eapply cequivc_trans;
                      [apply implies_cequivc_apply2;
                        [apply cequivc_refl
                        |apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact en1
                        |apply cequivc_refl]
                      |].
                      apply computes_to_valc_implies_cequivc; auto. }
                    apply member_equality.

                    eapply equality_respects_cequivc_right;
                      [apply cequivc_sym;exact cond2|].

                    eapply equality_respects_cequivc_left;
                      [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact h2|].
                    eauto 3 with slow.

                  - apply equality_in_unit in h.
                    repnd; spcast.
                    eapply inhabited_type_cequivc in inh;
                      [|apply implies_cequivc_isint;
                         [apply computes_to_valc_implies_cequivc;exact h
                         |apply cequivc_refl
                         |apply cequivc_refl]
                      ].
                    eapply inhabited_type_cequivc in inh;
                      [|apply cequivc_mkc_isint_mkc_axiom].
                    unfold inhabited_type in inh; exrepnd.
                    apply false_not_inhabited in inh0; sp.
                }
            }
          }
        }
    }
Qed.

Lemma subtype_rel_nat_iff_eq_value_type_nut {o} :
  forall lib (T : @CTerm o),
    subtype_rel lib T mkc_tnat
    -> eq_value_type_nut lib T.
Proof.
  introv.
  introv subt e.
  apply subt in e.
  apply equality_in_tnat in e.
  apply equality_of_nat_imp_tt in e.
  unfold equality_of_nat_tt in e; exrepnd.
  unfold compute_to_eqvals_nut.
  exists (@mkc_nat o k); dands; tcsp.
Qed.

Definition rule_strong_continuity2_v3_2 {o}
           (F T t : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_concl (strong_continuous_type2_v3 x M f n F T)
                                  (spMp F)))
      [ mk_baresequent H (mk_conclax (mk_member F (mk_fun (mk_nat2T T) mk_tnat))),
        mk_baresequent H (mk_conclax (mk_member t T)),
        mk_baresequent H (mk_conclax (mk_subtype_rel T mk_tnat)) ]
      [].

Lemma rule_strong_continuity_true2_v3_2 {p} :
  forall lib
         (F T t : NTerm)
         (x M f n : NVar)
         (H : @barehypotheses p)
         (d1 : M <> f)
         (d2 : n <> f)
         (d3 : n <> M)
         (d4 : !LIn M (free_vars F))
         (d5 : !LIn f (free_vars F))
         (d6 : !LIn n (free_vars F))
         (d7 : !LIn x (free_vars T))
         (d8 : !LIn M (free_vars T))
         (d9  : !LIn nvare (free_vars F))
         (d10 : !LIn nvarf (free_vars F))
         (d11 : !LIn nvarn (free_vars F))
         (cov : covered F (nh_vars_hyps H)),
    rule_true lib (rule_strong_continuity2_v3_2
                     F T t
                     x M f n
                     H).
Proof.
  unfold rule_strong_continuity2_v3_2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  rename Hyp1 into hyp3.
  destruct hyp3 as [wc3 hyp3].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  dup ct0 as cmF.
  apply covered_equality in cmF; repnd.
  clear cmF1 cmF.

  pose proof (covered_spM F (nh_vars_hyps H)) as cF.
  repeat (autodimp cF hyp).
  applydup cF in cov.
  apply covered_spM_iff_spMp in cov0.

  exists cov0.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  pose proof (rule_strong_continuity_true2_v3
                lib F T t x M f n H
                d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 cov) as q.
  autodimp q hyp.
  { introv sim hf.
    vr_seq_true in hyp3.
    pose proof (hyp3 s s) as q.
    repeat (autodimp q hyp); exrepnd; clear hyp3.
    lsubst_tac.
    allrw @equality_in_subtype_rel; repnd.
    allrw @lsubstc_mkc_tnat.
    apply subtype_rel_nat_iff_eq_value_type_nut; auto. }

  unfold rule_true in q.
  allsimpl.
  allunfold @strong_continuous_type2_v3; allsimpl.
  allunfold @closed_type_baresequent; allsimpl.
  allunfold @closed_extract_baresequent; allsimpl.
  allunfold @wf_sequent; allsimpl.
  allunfold @wf_concl; allsimpl.
  allunfold @closed_type; allsimpl.
  allunfold @closed_extract; allsimpl.

  pose proof (q (wfh, (wfct, wfce)) cg cargs) as h; clear q.
  autodimp h hyp.
  { introv seq; repndors; subst; tcsp.
    - exists (wfh, (wfct2, wfce2), (ct1, ce1)); auto.
    - exists (wfh, (wfct1, wfce2), (ct0, ce1)); auto. }
  exrepnd.
  allunfold @ext_wf_cseq; allsimpl.
  proof_irr; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)