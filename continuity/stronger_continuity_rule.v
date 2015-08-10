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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export alphaeq4.
Require Export stronger_continuity_defs4.
Require Export per_props_nat2.

Definition mod_fun_type {o} (x : NVar) : @NTerm o :=
  mk_function
    mk_tnat
    x
    (mk_fun (mk_natk2nat (mk_var x))  mk_natU).

Lemma lsubstc_mod_fun_type {o} :
  forall v w (s : @CSub o) c,
    alphaeqc (lsubstc (mod_fun_type v) w s c) modulus_fun_type_u.
Proof.
  introv.
  unfold mod_fun_type.
  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  unfold modulus_fun_type.

  apply implies_alphaeqc_mkc_function; eauto 2 with slow.
  introv.
  repeat substc_lsubstc_vars3.
  eapply alphaeqc_trans;[|apply alphaeqc_sym;apply substc_mkcv_fun].

  match goal with
    | [ |- context[lsubstc (mk_fun ?a ?b) ?w ?s ?c] ] =>
      pose proof (lsubstc_mk_fun_ex a b s w c) as h;
        exrepnd; clear_irr
  end.
  eapply alphaeqc_trans;[exact h1|]; clear h1.

  apply alphaeqc_mkc_fun.

  - eapply alphaeqc_trans;[|apply alphaeqc_sym;apply substc_mkcv_fun].
    eapply alphaeqc_trans;
      [|apply alphaeqc_sym;apply alphaeqc_mkc_fun;
        [apply mkcv_natk_substc
        |apply alphaeqc_refl]
      ].
    rw @mkcv_tnat_substc.
    rw @mkc_var_substc.

    eapply alphaeqc_trans;[apply lsubstc_mk_natk2nat_sp1|].
    eauto 2 with slow.

  - eapply alphaeqc_trans;[apply lsubstc_mk_natU|].
    rw @csubst_mk_cv; eauto 3 with slow.
Qed.


(* XXXXXXXXXX *)


Definition mk_sqexists {o} (a : @NTerm o) v b := mk_squash (mk_exists a v b).

Definition strong_continuous_type {o} (x M f n : NVar) (F : @NTerm o) :=
  mk_sqexists
    (mod_fun_type x)
    M
    (mk_all
       mk_nat2nat
       f
       (mk_sqexists
          mk_tnat
          n
          (mk_equality
             (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
             (mk_apply F (mk_var f))
             mk_natU))).

Definition rule_strong_continuity {o}
           (F : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_conclax (strong_continuous_type x M f n F)))
      [ mk_baresequent H (mk_conclax (mk_member F (mk_fun mk_nat2nat mk_tnat))) ]
      [].

Lemma rule_strong_continuity_true {p} :
  forall lib
         (F : NTerm)
         (x M f n : NVar)
         (H : @barehypotheses p)
         (d1 : M <> f)
         (d2 : n <> f)
         (d3 : n <> M)
         (d4 : !LIn M (free_vars F))
         (d5 : !LIn f (free_vars F))
         (d6 : !LIn n (free_vars F)),
    rule_true lib (rule_strong_continuity
                     F
                     x M f n
                     H).
Proof.
  unfold rule_strong_continuity, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  allunfold @strong_continuous_type.
  allunfold @mk_sqexists.
  lsubst_tac.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member_sp in h0; repnd.
  allrw @fold_equorsq.
  clear h2.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  eapply member_respects_alphaeqc_r in h1;
    [|apply alphaeqc_mkc_fun;[apply lsubstc_mk_nat2nat|apply alphaeqc_refl] ].
  eapply respects_alphaeqc_equorsq3 in h0;
    [|apply alphaeqc_mkc_fun;[apply lsubstc_mk_nat2nat|apply alphaeqc_refl] ].

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
      [apply alphaeqc_sym; apply lsubstc_mod_fun_type|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply lsubstc_mod_fun_type|].
      apply type_modulus_fun_type_u.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;[|apply lsubstc_mod_fun_type].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply lsubstc_mk_nat2nat|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym; apply lsubstc_mk_nat2nat|].
        apply type_nat2nat.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;[|apply lsubstc_mk_nat2nat].
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply tequality_mkc_squash.
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

          apply equality_in_function2 in em; repnd.
          clear em0.
          applydup em in en as e.
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
          apply (equality_nat2nat_to_natk2nat lib n1) in en2n; auto;[].

          apply equality_in_fun in e; repnd; clear e0 e1.
          apply e in en2n.
          allrw <- @mkc_apply2_eq; auto. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].
          apply equality_in_fun in memF; repnd; clear memF0 memF1.
          apply memF in en2n; auto.
          apply equality_in_bunion_left; eauto 2 with slow. }

  - apply equality_in_mkc_squash; dands;
    try (spcast; apply computes_to_valc_refl; eauto 3 with slow);[].

    unfold mk_exists.
    lsubst_tac.

    exists (mkc_pair (spM_c (lsubstc F wt s1 ct0))
                     (mkc_lam f (mkcv_axiom f))).

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym; apply lsubstc_mod_fun_type|].
      apply type_modulus_fun_type_u.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;[|apply lsubstc_mod_fun_type].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply lsubstc_mk_nat2nat|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym; apply lsubstc_mk_nat2nat|].
        apply type_nat2nat.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;[|apply lsubstc_mk_nat2nat].
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply tequality_mkc_squash.
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

          apply equality_in_function2 in em; repnd.
          clear em0.
          applydup em in en as e.
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
          apply (equality_nat2nat_to_natk2nat lib n1) in en2n; auto;[].

          apply equality_in_fun in e; repnd; clear e0 e1.
          apply e in en2n.
          allrw <- @mkc_apply2_eq; auto. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].
          apply equality_refl in memF.
          apply equality_in_fun in memF; repnd; clear memF0 memF1.
          apply memF in en2n; auto.
          apply equality_in_bunion_left; eauto 2 with slow. }

    + eexists; eexists; eexists; eexists; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

      * eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym; apply lsubstc_mod_fun_type].

        apply spM_in_modulus_fun_type_u; auto.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym; apply lsubstc_mk_nat2nat|].
          eauto 3 with slow. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;[|apply lsubstc_mk_nat2nat].
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          apply tequality_mkc_squash.
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

            pose proof (spM_in_modulus_fun_type_u lib (lsubstc F wt s1 ct0) h1) as h.
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
            apply (equality_nat2nat_to_natk2nat lib n1) in en2n; auto;[].

            apply equality_in_fun in e; repnd; clear e0 e1.
            apply e in en2n.
            allrw <- @mkc_apply2_eq; auto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;[|apply lsubstc_mk_nat2nat].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @substc_mkcv_axiom.

          apply equality_in_mkc_squash; dands; spcast;
          try (apply computes_to_valc_refl; eauto 3 with slow);[].

          applydup @equality_refl in en2n as mf1.
          pose proof (spM_cond lib (lsubstc F wt s1 ct0) f1 h1 mf1) as h.
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

              pose proof (spM_in_modulus_fun_type_u lib (lsubstc F wt s1 ct0) h1) as h.
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
              apply (equality_nat2nat_to_natk2nat lib n1) in en2n; auto;[].

              apply equality_in_fun in e; repnd; clear e0 e1.
              applydup @equality_refl in en2n as ef.
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
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
