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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

 *)


Require Export stronger_continuity_rule4_v2.
Require Export per_props_subtype_rel.


Lemma subtype_rel_nat_implies_eq_value_type_nut {o} :
  forall lib (T : @CTerm o),
    subtype_rel lib T mkc_tnat
    -> eq_value_type_nut lib T.
Proof.
  introv subt e.
  apply subt in e.
  apply equality_in_tnat in e.
  apply equality_of_nat_imp_tt in e.
  unfold equality_of_nat_tt in e; exrepnd.
  unfold compute_to_eqvals_nut.
  exists (@mkc_nat o k); dands; tcsp.
Qed.
Hint Resolve subtype_rel_nat_implies_eq_value_type_nut : slow.

(* Same as rule_strong_continuity2_v2 but with an extra explicit subtyping hyp *)
Definition rule_strong_continuity2_v2_2 {o}
           (F T t : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_conclax (strong_continuous_type2_v2 x M f n F T)))
      [ mk_baresequent H (mk_conclax (mk_member F (mk_fun (mk_nat2T T) mk_tnat))),
        mk_baresequent H (mk_conclax (mk_member t T)),
        mk_baresequent H (mk_conclax (mk_subtype_rel T mk_tnat)) ]
      [].

Lemma rule_strong_continuity_true2_v2_2 {p} :
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
         (d8 : !LIn M (free_vars T)),
    rule_true lib (rule_strong_continuity2_v2_2
                     F T t
                     x M f n
                     H).
Proof.
  unfold rule_strong_continuity2_v2_2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

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

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hTT; exrepnd; clear hyp2.

  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as subt; exrepnd; clear hyp3.

  allunfold @strong_continuous_type2_v2.
  allunfold @mk_sqexists.
  lsubst_tac.

  apply equality_in_member in hTT1; repnd.
  apply tequality_mkc_member in hTT0; repnd.
  clear hTT0 hTT2 hTT3.

  clear subt0.
  apply equality_in_subtype_rel in subt1.
  repnd.
  clear subt0 subt2 subt3 subt4.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member in h0; repnd.
  allrw @fold_equorsq.
  clear h2.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  eapply member_respects_alphaeqc_r in h1;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].
  eapply respects_alphaeqc_equorsq3 in h0;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].

  dup h1 as memF.
  eapply cequorsq_equality_trans1 in memF;[|apply equorsq_sym;exact h0].
  apply equality_sym in memF.
  clear h0.

  prove_and teq.

  - apply tequality_mkc_squash.

    unfold mk_exists.
    lsubst_tac.

    apply tequality_product.
    dands.

    + eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w4 s1 c7 w1 c1);auto|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w4 s2 c9 w1 c0);auto|].
      apply tequality_modulus_fun_type_u_v2; auto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w4 s1 c7 w1 c1);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w3 s2 c16 w1 c0)|].
        apply tequality_nat2T; auto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].
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
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T w1 s1 c1)) as h.
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
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T w1 s1 c1)) as h.
            repeat (autodimp h hyp).
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_natU_implies_cequivc in h; spcast.
            apply equality_in_tnat_implies_cequivc in en2n.
            apply tequality_equality_if_cequivc; eauto 3 with slow.
            apply type_tnat.
          }
        }

  - apply equality_in_mkc_squash; dands;
    try (spcast; apply computes_to_valc_refl; eauto 3 with slow);[].

    unfold mk_exists.
    lsubst_tac.

    exists (mkc_pair (spM_c (lsubstc F wt0 s1 ct3))
                     (mkc_lam f (mkcv_pair
                                   [f]
                                   (mkcv_axiom f)
                                   (mkcv_lam [f] n (mkcv_ax [n,f]))))).

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w4 s1 c7 w1 c1);auto|].
      apply tequality_modulus_fun_type_u_v2; eauto 3 with slow.
      eapply tequality_refl; eauto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w4 s1 c7 w1 c1);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)|].
        apply tequality_nat2T.
        eapply tequality_refl; eauto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].
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
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T w1 s1 c1)) as h.
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
                          lib M1 M2 n1 n2 f1 f2 (lsubstc T w1 s1 c1)) as h.
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
        [|apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w4 s1 c7 w1 c1);auto].

        apply (spM_in_modulus_fun_type_u_v2 _ _ (lsubstc t wt s1 ct2)); eauto 3 with slow.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)|].
          eauto 3 with slow.
          apply tequality_nat2T; eauto 3 with slow.
          eapply tequality_refl; eauto. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].
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
                            (lsubstc t wt s1 ct2)
                            (lsubstc T w1 s1 c1)) as h.
              repeat (autodimp h hyp); eauto 3 with slow;[].
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
                          (lsubstc t wt s1 ct2)
                          (lsubstc T w1 s1 c1)) as spMt.
            repeat (autodimp spMt hyp);eauto 3 with slow; [].
            apply tequality_mkc_ufun; dands.

            { pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f2
                            (lsubstc T w1 s1 c1)) as h.
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
                            (lsubstc T w1 s1 c1)) as h.
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
            [|apply (lsubstc_mk_nat2T_sp1 T w3 s1 c6 w1 c1)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @mkcv_pair_substc.
          allrw @substc_mkcv_axiom.
          repeat (rw @mkcv_lam_substc;auto;[]).
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
                            (lsubstc t wt s1 ct2)
                            (lsubstc T w1 s1 c1)) as h.
              repeat (autodimp h hyp);eauto 3 with slow;[].
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
                          (lsubstc t wt s1 ct2)
                          (lsubstc T w1 s1 c1)) as spMt.
            repeat (autodimp spMt hyp);eauto 3 with slow;[].
            apply tequality_mkc_ufun; dands.

            { applydup @equality_refl in en2n.
              pose proof (equality_in_modulus_fun_type_u_implies_v2
                            lib
                            (spM_c (lsubstc F wt0 s1 ct3))
                            (spM_c (lsubstc F wt0 s1 ct3))
                            n1 n2 f1 f1
                            (lsubstc T w1 s1 c1)) as h.
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
                            (lsubstc T w1 s1 c1)) as h.
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
                   (@mkc_lam p n (mk_cv [n] mkc_axiom))
                   (@mkc_lam p n (mk_cv [n] mkc_axiom)).
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
                            (lsubstc T w1 s1 c1)
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
                                (lsubstc t wt s1 ct2)
                                (lsubstc T w1 s1 c1)) as h.
                  repeat (autodimp h hyp); eauto 3 with slow;[].
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
                                (lsubstc t wt s1 ct2)
                                (lsubstc T w1 s1 c1)) as spMt.
                repeat (autodimp spMt hyp);eauto 3 with slow;[].
                apply tequality_mkc_ufun; dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T w1 s1 c1)) as h.
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
                                (lsubstc T w1 s1 c1)) as h.
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
                              (lsubstc t wt s1 ct2)
                              (lsubstc T w1 s1 c1)) as spMt.
                repeat (autodimp spMt hyp);eauto 3 with slow;[].

                dands.

                { applydup @equality_refl in en2n.
                  pose proof (equality_in_modulus_fun_type_u_implies_v2
                                lib
                                (spM_c (lsubstc F wt0 s1 ct3))
                                (spM_c (lsubstc F wt0 s1 ct3))
                                n1 n2 f1 f1
                                (lsubstc T w1 s1 c1)) as h.
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
                                (lsubstc T w1 s1 c1)) as h.
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
                                (lsubstc T w1 s1 c1)) as h.
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
                                  (lsubstc T w1 s1 c1)) as cond2.
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
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
