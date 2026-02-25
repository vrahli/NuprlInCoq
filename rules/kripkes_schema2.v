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


Require Export kripkes_schema.
Require Export per_props_isect.


Lemma apply_one_at_zero_to_not_zero_computes_to_one {o} :
  forall lib x k,
    k <> 0
    -> @computes_to_valc o lib (mkc_apply (one_at_zero x) (mkc_nat k)) mkc_zero.
Proof.
  introv d0.
  unfold one_at_zero.
  unfold computes_to_valc; simpl.
  eapply implies_computes_to_value_apply;
    [apply computes_to_value_isvalue_refl;
     apply isvalue_mk_lam;
     apply isprog_vars_mk_int_eq;
     dands;eauto 2 with slow
    |].
  unfold subst; simpl.
  rewrite lsubst_lsubst_aux; simpl; auto; fold_terms.
  boolvar; fold_terms.
  split;[|unfold mk_one; eauto 3 with slow].
  apply reduces_to_if_step; csunf; simpl.
  dcwf h; simpl.
  unfold compute_step_comp; simpl.
  boolvar; ginv; tcsp.
  inversion e as [xx]; clear e.
  assert (0%Z = Z.of_nat 0%nat) as zz by auto.
  rewrite zz in xx; clear zz.
  lia.
Qed.

(**

<<
   H |- ↓(∃a:ℕ → ℕ.((∃x:ℕ.(a(x) = 1 /\ ∀y:ℕ.y<>x->a(y)=0)) ↔ A))

     By Kripke's Schema

     H |- A ∈ Type(i)
>>

 *)

Definition rule_kripke_s_schema2 {o}
           (A : @NTerm o)
           (a x y : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_squash (mk_exists
                                 mk_nat2nat
                                 a
                                 (mk_iff
                                    (mk_exists
                                       mk_tnat
                                       x
                                       (mk_prod
                                          (mk_equality
                                             (mk_apply (mk_var a) (mk_var x))
                                             mk_one
                                             mk_tnat)
                                          (mk_isect
                                             mk_tnat
                                             y
                                             (mk_ufun
                                                (mk_not (mk_equality (mk_var y) (mk_var x) mk_tnat))
                                                (mk_equality (mk_apply (mk_var a) (mk_var y)) mk_zero mk_tnat)))))
                                    A)))))
    [
      mk_baresequent H (mk_conclax (mk_member A (mk_uni i)))
    ]
    [].

Lemma rule_kripke_s_schema2_true {o} :
  forall lib (A : @NTerm o)
         (a x y : NVar)
         (i : nat)
         (H : @barehypotheses o)
         (cond1 : a <> x)
         (cond2 : !LIn a (free_vars A))
         (cond3 : !LIn x (free_vars A))
         (cond4 : x <> y)
         (cond5 : a <> y),
    rule_true lib (rule_kripke_s_schema2 A a x y i H).
Proof.
  unfold rule_kripke_s_schema, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf hyp].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  unfold mk_exists.

  vr_seq_true in hyp.
  pose proof (hyp s1 s2 eqh sim) as h; exrepnd.

  lsubst_tac.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member_implies_sp in h0; auto.

  rw @tequality_mkc_squash.
  rw @equality_in_mkc_squash_ax.

  dands.

  {
    (* we first prove the functionality of the conclusion
       (we'll then prove that it's true) *)

    apply tequality_product.
    dands.

    {
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;
         apply lsubstc_mk_nat2nat; auto
        |].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym;
         apply lsubstc_mk_nat2nat; auto
        |].
      apply type_nat2nat.
    }

    {
      introv equnn.
      eapply alphaeqc_preserving_equality in equnn;[|apply lsubstc_mk_nat2nat].
      repeat substc_lsubstc_vars3.
      lsubst_tac.

      apply tequality_mkc_iff.
      allrw @lsubstc_mkc_tnat.
      dands.

      {
        apply tequality_product.
        dands.

        { apply type_tnat. }

        introv equn.
        pose proof (equality_nat2nat_apply lib a0 a' a1 a'0 equnn equn) as eqap.
        dup eqap as m1. apply equality_refl in m1.
        dup eqap as m2. apply equality_sym in m2. apply equality_refl in m2.
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        allrw @lsubstc_mk_one.

        apply tequality_mkc_prod; dands.

        {
          apply tequality_mkc_equality.
          dands; try complete (try split; intro; auto).
          apply type_tnat.
        }

        {
          introv inh.
          unfold mk_forall.
          lsubst_tac.
          allrw @lsubstc_mkc_tnat.
          apply tequality_isect; dands.

          { apply type_tnat. }

          introv ea.
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          apply tequality_mkc_ufun; dands.

          {
            apply tequality_not.
            allrw @lsubstc_mkc_tnat.
            apply tequality_mkc_equality; dands; tcsp.
            apply type_tnat.
            split; intro. apply equality_trans with (t2 := a2); auto. apply equality_sym; auto.
                          apply equality_trans with (t2 := a'1); auto. apply equality_sym; auto.
            split; intro. apply equality_trans with (t2 := a1); auto. apply equality_sym; auto.
                          apply equality_trans with (t2 := a'0); auto. apply equality_sym; auto.
          }

          {
            introv inh1.
            allrw @lsubstc_mkc_tnat.
            apply tequality_mkc_equality2; dands; tcsp.
            { apply type_tnat. }
            {eapply equality_nat2nat_apply; eauto. 
            }
            {pose proof (@equality_in_tnat_nat o lib 0). rw @mkc_zero_eq; auto. }
          }
        }
      }

      {
        introv inh.
        apply equality_in_uni in h0; auto.
      }

      {
        introv inh.
        apply equality_in_uni in h0; auto.
      }
    }
  }

  {
    (* we now prove that the conclusion is true) *)

    apply inhabited_product; dands.

    {
      eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
      apply type_nat2nat.
    }

    {
      introv equnn.
      eapply alphaeqc_preserving_equality in equnn;[|apply lsubstc_mk_nat2nat].
      repeat substc_lsubstc_vars3.
      lsubst_tac.

      apply tequality_mkc_iff.
      allrw @lsubstc_mkc_tnat.
      dands.

      {
        apply tequality_product.
        dands.

        { apply type_tnat. }

        introv equn.
        pose proof (equality_nat2nat_apply lib a0 a' a1 a'0 equnn equn) as eqap.
        dup eqap as m1. apply equality_refl in m1.
        dup eqap as m2. apply equality_sym in m2. apply equality_refl in m2.
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        allrw @lsubstc_mk_one.

        apply tequality_mkc_prod; dands.

        {
          apply tequality_mkc_equality.
          dands; try complete (try split; intro; auto).
              apply type_tnat.

        }

        {
          introv inh.
          unfold mk_forall.
          lsubst_tac.
          allrw @lsubstc_mkc_tnat.
          apply tequality_isect; dands.

          { apply type_tnat. }

          introv ea.
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          apply tequality_mkc_ufun; dands.

          {
            apply tequality_not.
            allrw @lsubstc_mkc_tnat.
            apply tequality_mkc_equality2; dands; tcsp.
            apply type_tnat. 
          }

          {
            introv inh1.
            allrw @lsubstc_mkc_tnat.
            apply tequality_mkc_equality2; dands; tcsp.
            { apply type_tnat. }
            { eapply equality_nat2nat_apply; eauto. }
            { pose proof (@equality_in_tnat_nat o lib 0). rw @mkc_zero_eq; auto. }
          }
        }
      }

      {
        introv inh.
        apply equality_in_uni in h0; auto.
        apply tequality_refl in h0; auto.
      }

      {
        introv inh.
        apply equality_in_uni in h0; auto.
        apply tequality_refl in h0; auto.
      }
    }

    {
      destruct (classic (inhabited_type lib (lsubstc A wt s1 ct0))) as [inh | ninh].

      {
        (* A is inhabited *)
        exists (@one_at_zero o x).

        dands.

        {
          eapply respects_alphaeqc_member;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
          eauto 2 with slow.
        }

        {
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          allrw @lsubstc_mkc_tnat.

          apply implies_inhabited_mkc_iff.

          {
            unfold inhabited_type in inh; exrepnd.
            exists (mkc_lam x (mk_cv [x] t)).
            apply equality_in_fun.
            dands.

            {
              apply tequality_product.
              dands.

              { apply type_tnat. }

              introv equn.
              repeat substc_lsubstc_vars3.
              lsubst_tac.
              allrw @lsubstc_mkc_tnat.
              allrw @lsubstc_mk_one.

              apply tequality_mkc_prod; dands.

              {
                apply tequality_mkc_equality2.
                dands.

                { apply type_tnat. }

                { eapply equality_nat2nat_apply; eauto.
                  apply one_at_zero_is_nat2nat.
                }

                {  rw @mkc_one_as_mkc_nat.
                    apply nat_in_nat.
                }
              }

              {
                introv inh.
                lsubst_tac.
                allrw @lsubstc_mkc_tnat.
                apply tequality_isect; dands.

                { apply type_tnat. }

                introv ea.
                repeat substc_lsubstc_vars3.
                lsubst_tac.

                apply tequality_mkc_ufun; dands.

                {
                  apply tequality_not.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  apply type_tnat.
                }

                {
                  introv inh1.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  { apply type_tnat. }
                  { apply equality_nat2nat_apply; auto.
                    apply one_at_zero_is_nat2nat. }
                  { pose proof (@equality_in_tnat_nat o lib 0). rw @mkc_zero_eq; auto. }
                }
              }
            }

            {
              introv inh.
              apply equality_in_uni in h0; auto.
              apply tequality_refl in h0; auto.
            }

            {
              introv equ.

              eapply equality_respects_cequivc_left;
                [apply cequivc_sym; apply cequivc_beta|].
              eapply equality_respects_cequivc_right;
                [apply cequivc_sym; apply cequivc_beta|].
              autorewrite with core.
              auto.
            }
          }

          {
            exists (@mkc_lam o x (mkcv_pair
                                    [x]
                                    (mkcv_zero [x])
                                    (mkcv_pair
                                       [x]
                                       (mkcv_axiom x)
                                       (mkcv_axiom x)))).
            apply equality_in_fun.
            dands.

            {
              apply equality_in_uni in h0; auto.
              apply tequality_refl in h0; auto.
            }

            {
              introv inha.
              apply tequality_product.
              dands.

              { apply type_tnat. }

              introv equn.
              repeat substc_lsubstc_vars3.
              lsubst_tac.
              allrw @lsubstc_mkc_tnat.
              allrw @lsubstc_mk_one.

              apply tequality_mkc_prod; dands.

              {
                apply tequality_mkc_equality2.
                dands.

                { apply type_tnat. }

                { apply equality_nat2nat_apply; auto;
                       apply one_at_zero_is_nat2nat.
                }

                {rw @mkc_one_as_mkc_nat.
                    apply nat_in_nat. 
                }
              }

              {
                introv inh1.
                lsubst_tac.
                allrw @lsubstc_mkc_tnat.
                apply tequality_isect; dands.

                { apply type_tnat. }

                introv ea.
                repeat substc_lsubstc_vars3.
                lsubst_tac.

                apply tequality_mkc_ufun; dands.

                {
                  apply tequality_not.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  apply type_tnat.
                }

                {
                  introv inh2.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  { apply type_tnat. }
                  { apply equality_nat2nat_apply; auto.
                    apply one_at_zero_is_nat2nat. }
                  { pose proof (@equality_in_tnat_nat o lib 0). rw @mkc_zero_eq; auto. }
                }
              }
            }

            {
              introv equ.

              eapply equality_respects_cequivc_left;
                [apply cequivc_sym; apply cequivc_beta|].
              eapply equality_respects_cequivc_right;
                [apply cequivc_sym; apply cequivc_beta|].
              autorewrite with core.

              apply equality_in_product; dands; eauto 2 with slow.

              {
                introv equn.
                repeat substc_lsubstc_vars3.
                lsubst_tac.
                allrw @lsubstc_mkc_tnat.
                allrw @lsubstc_mk_one.

                apply tequality_mkc_prod; dands.

                {
                  apply tequality_mkc_equality2; dands; eauto 3 with slow.

                  { apply type_tnat. }

                  { apply equality_nat2nat_apply; auto.
                    apply one_at_zero_is_nat2nat.
                  }

                  { rw @mkc_one_as_mkc_nat.
                    apply nat_in_nat. 
                  }
                }

                {
                  introv inh1.
                  lsubst_tac.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_isect; dands.

                  { apply type_tnat. }

                  introv ea.
                  repeat substc_lsubstc_vars3.
                  lsubst_tac.

                  apply tequality_mkc_ufun; dands.

                  {
                    apply tequality_not.
                    allrw @lsubstc_mkc_tnat.
                    apply tequality_mkc_equality2; dands; tcsp.
                    apply type_tnat.
                  }

                  {
                    introv inh2.
                    allrw @lsubstc_mkc_tnat.
                    apply tequality_mkc_equality2; dands; tcsp.
                    { apply type_tnat. }
                    { apply equality_nat2nat_apply; auto.
                      apply one_at_zero_is_nat2nat. }
                    { allrw @mkc_zero_eq.
                      apply nat_in_nat. }
                    }
                }
              }

              {
                exists (@mkc_zero o) (@mkc_zero o)
                       (mkc_pair (@mkc_axiom o) (@mkc_axiom o))
                       (mkc_pair (@mkc_axiom o) (@mkc_axiom o)).
                dands; spcast; auto; eauto 3 with slow.

                { allrw @mkc_zero_eq.
                  apply nat_in_nat. }

                {
                  repeat substc_lsubstc_vars3.
                  lsubst_tac.
                  allrw @lsubstc_mkc_tnat.
                  allrw @lsubstc_mk_one.

                  apply equality_in_prod; dands.

                  {
                    apply type_mkc_equality2.
                    apply type_tnat.
                  }

                  {
                    introv inh1.
                    lsubst_tac.
                    allrw @lsubstc_mkc_tnat.
                    apply tequality_isect; dands.

                    { apply type_tnat. }

                    introv ea.
                    repeat substc_lsubstc_vars3.
                    lsubst_tac.

                    apply tequality_mkc_ufun; dands.

                    {
                      apply tequality_not.
                      allrw @lsubstc_mkc_tnat.
                      apply tequality_mkc_equality2; dands; tcsp.
                      { apply type_tnat. }
                      { rw @mkc_zero_eq.
                        apply nat_in_nat. } 
                    }

                    {
                      introv inh2.
                      allrw @lsubstc_mkc_tnat.
                      apply tequality_mkc_equality2; dands; tcsp.
                      { apply type_tnat. }
                      { apply equality_nat2nat_apply; auto.
                        apply one_at_zero_is_nat2nat. }
                      { rw @mkc_zero_eq.
                        apply nat_in_nat. }
                    }
                  }

                  exists (@mkc_axiom o) (@mkc_axiom o) (@mkc_axiom o) (@mkc_axiom o).
                  dands; spcast; eauto 3 with slow.

                  {
                    apply member_equality.

                    eapply equality_respects_cequivc_left;
                      [apply cequivc_sym;
                       apply computes_to_valc_implies_cequivc;
                       apply apply_one_at_zero_to_zero_computes_to_one
                      |].
                    rw @mkc_one_as_mkc_nat.
                    apply nat_in_nat.
                  }

                  {
                    apply equality_in_isect; dands; auto.

                    { apply type_tnat. }

                    {
                      introv ea.
                      repeat substc_lsubstc_vars3.
                      lsubst_tac.

                      apply tequality_mkc_ufun; dands.

                      {
                        apply tequality_not.
                        allrw @lsubstc_mkc_tnat.
                        apply tequality_mkc_equality2; dands; tcsp.
                        { apply type_tnat. }
                        { rw @mkc_zero_eq.
                        apply nat_in_nat.  }
                      }

                      {
                        introv inh2.
                        allrw @lsubstc_mkc_tnat.
                        apply tequality_mkc_equality2; dands; tcsp.
                        { apply type_tnat. }
                        { apply equality_nat2nat_apply; auto.
                          apply one_at_zero_is_nat2nat. }
                        { rw @mkc_zero_eq.
                        apply nat_in_nat.  }
                      }
                    }

                    {
                      introv ea.
                      repeat substc_lsubstc_vars3.
                      lsubst_tac.

                      apply equality_in_ufun; dands.

                      {
                        apply tequality_not.
                        allrw @lsubstc_mkc_tnat.
                        apply tequality_mkc_equality2; dands; tcsp.
                        { apply type_tnat. }
                        { apply equality_refl in ea; auto. }
                        { rw @mkc_zero_eq.
                        apply nat_in_nat.  }
                      }

                      {
                        introv inh1.
                        allrw @lsubstc_mkc_tnat.
                        apply type_mkc_equality2.
                        apply type_tnat.
                      }

                      {
                        introv inh1.
                        allrw @lsubstc_mkc_tnat.
                        rw <- @member_equality_iff.
                        unfold inhabited_type in inh1; exrepnd.
                        apply equality_in_not in inh0; repnd.
                        rw @inhabited_mkc_equality in inh0.

                        apply equality_in_tnat in ea.
                        unfold equality_of_nat in ea; exrepnd; spcast.

                        assert (k <> 0) as d0.
                        {
                          introv xx; subst.
                          destruct inh0.
                          apply equality_in_tnat.
                          exists 0.
                          dands; spcast; auto.
                          rw @mkc_zero_eq; eauto 3 with slow.
                        }

                        eapply equality_respects_cequivc_left;
                          [apply implies_cequivc_apply;[apply cequivc_refl|];
                           apply cequivc_sym;apply computes_to_valc_implies_cequivc;
                           eauto
                          |].

                        eapply equality_respects_cequivc_left;
                          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;
                           apply apply_one_at_zero_to_not_zero_computes_to_one;auto
                          |].

                        apply equality_in_tnat; exists 0;
                          rw <- @mkc_zero_eq;
                          dands; spcast; eauto 3 with slow.
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }

      {
        (* A is not inhabited *)
        exists (@all_zero o x).

        dands.

        {
          eapply respects_alphaeqc_member;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
          eauto 2 with slow.
        }

        {
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          allrw @lsubstc_mkc_tnat.

          apply implies_inhabited_mkc_iff.

          {
            exists (@mkc_lam o x (mkcv_bot [x])).
            apply equality_in_fun.
            dands.

            {
              apply tequality_product.
              dands.

              { apply type_tnat. }

              introv equn.
              repeat substc_lsubstc_vars3.
              lsubst_tac.
              allrw @lsubstc_mkc_tnat.
              allrw @lsubstc_mk_one.

              apply tequality_mkc_prod; dands.

              {
                apply tequality_mkc_equality2.
                dands.

                { apply type_tnat. }

                { apply equality_nat2nat_apply; auto;
                  apply all_zero_is_nat2nat.
                }

                {rw @mkc_one_as_mkc_nat.
                    apply nat_in_nat.
                }
              }

              {
                introv inh.
                lsubst_tac.
                allrw @lsubstc_mkc_tnat.
                apply tequality_isect; dands.

                { apply type_tnat. }

                introv ea.
                repeat substc_lsubstc_vars3.
                lsubst_tac.

                apply tequality_mkc_ufun; dands.

                {
                  apply tequality_not.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  apply type_tnat.
                }

                {
                  introv inh1.
                  allrw @lsubstc_mkc_tnat.
                  apply tequality_mkc_equality2; dands; tcsp.
                  { apply type_tnat. }
                  { apply equality_nat2nat_apply; auto.
                    apply all_zero_is_nat2nat. }
                  { rw @mkc_zero_eq.
                        apply nat_in_nat.  }
                }
              }
            }

            {
              introv inh.
              apply equality_in_uni in h0; auto.
              apply tequality_refl in h0; auto.
            }

            {
              introv equ.

              assert False; tcsp.

              apply equality_in_product in equ; exrepnd; spcast.
              clear equ0 equ1 equ2 equ4.
              repeat substc_lsubstc_vars3.
              lsubst_tac.

              apply equality_in_prod in equ3; exrepnd.
              clear equ2 equ4 equ3.

              apply equality_in_mkc_equality in equ6; repnd.
              clear equ3 equ6.
              allrw @lsubstc_mkc_tnat.
              allrw @lsubstc_mk_one.

              apply equality_in_tnat in equ5.
              unfold equality_of_nat in equ5; exrepnd; spcast.

              eapply equality_respects_cequivc_left in equ2;
                [|apply implies_cequivc_apply;
                  [apply cequivc_refl
                  |apply computes_to_valc_implies_cequivc;eauto]
                ].

              eapply equality_respects_cequivc_left in equ2;
                [|apply computes_to_valc_implies_cequivc;
                  apply apply_all_zero_to_nat_computes_to_zero].

              apply equality_in_tnat in equ2.
              unfold equality_of_nat in equ2; exrepnd; spcast.
              apply computes_to_valc_isvalue_eq in equ2; eauto 2 with slow.
              apply computes_to_valc_isvalue_eq in equ5; eauto 2 with slow.
              rewrite mkc_one_as_mkc_nat in equ5.
              rewrite mkc_zero_eq in equ2.
              apply mkc_nat_eq_implies in equ2.
              apply mkc_nat_eq_implies in equ5.
              subst; ginv.
            }
          }

          {
            exists (@mkc_lam o x (mkcv_bot [x])).
            apply equality_in_fun.
            dands.

            {
              apply equality_in_uni in h0; auto.
              apply tequality_refl in h0; auto.
            }

            {
              introv inha; tcsp.
            }

            {
              introv equ.
              apply inhabited_type_if_equality in equ; tcsp.
            }
          }
        }
      }
    }
  }
Qed.
