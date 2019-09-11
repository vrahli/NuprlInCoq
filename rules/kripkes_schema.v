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

Require Export Classical_Prop.

Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_union.
Require Export per_props_equality.
Require Export per_props_squash.
Require Export per_props_iff.
Require Export seq_util2.
Require Export subst_tacs.
Require Export sequents_equality.


Lemma lsubstc_mk_one {o} :
  forall p sub c,
    lsubstc mk_one p sub c = @mkc_one o.
Proof.
  unfold lsubstc, mkc_one; sp.
  apply cterm_eq; sp.
Qed.
Hint Rewrite @lsubstc_mk_one : slow.

Lemma mkc_one_as_mkc_nat {o} : @mkc_one o = mkc_nat 1.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.

Lemma iscvalue_mkc_one {o} : @iscvalue o mkc_one.
Proof.
  unfold iscvalue; simpl.
  split; eauto 3 with slow.
  unfold iscan; simpl; auto.
Qed.
Hint Resolve iscvalue_mkc_one : slow.

Definition one_at_zero {o} (v : NVar) : @CTerm o :=
  mkc_lam
    v
    (mkcv_inteq
       [v]
       (mkc_var v)
       (mkcv_zero [v])
       (mkcv_one [v])
       (mkcv_zero [v])).

Definition all_zero {o} (v : NVar) : @CTerm o :=
  mkc_lam v (mkcv_zero [v]).

Hint Rewrite @mkcv_inteq_substc : core.
Hint Rewrite @substc_mkcv_zero  : core.
Hint Rewrite @mkc_var_substc    : core.
Hint Rewrite @mkcv_one_substc   : core.
Hint Rewrite @csubst_mk_cv      : core.
Hint Rewrite @substc_mkcv_axiom : core.
Hint Rewrite @mkcv_pair_substc  : core.

Lemma one_at_zero_is_nat2nat {o} :
  forall lib x, @member o lib (one_at_zero x) nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply equality_in_fun; dands; auto; eauto 2 with slow.
  introv equn.
  unfold one_at_zero.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_beta|].
  autorewrite with core.

  apply equality_in_tnat in equn.
  unfold equality_of_nat in equn; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_mkc_inteq;
     [apply computes_to_valc_implies_cequivc;eauto
     |apply cequivc_refl
     |apply cequivc_refl
     |apply cequivc_refl]
    |].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_mkc_inteq;
     [apply computes_to_valc_implies_cequivc;eauto
     |apply cequivc_refl
     |apply cequivc_refl
     |apply cequivc_refl]
    |].

  allrw @mkc_zero_eq.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_inteq_nat
    |].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_inteq_nat
    |].

  boolvar; subst.

  { rw @mkc_one_as_mkc_nat.
    apply nat_in_nat. }

  { apply nat_in_nat. }
Qed.
Hint Resolve one_at_zero_is_nat2nat : slow.

Lemma all_zero_is_nat2nat {o} :
  forall lib x, @member o lib (all_zero x) nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply equality_in_fun; dands; auto; eauto 2 with slow.
  introv equn.
  unfold one_at_zero.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_beta|].
  autorewrite with core.

  allrw @mkc_zero_eq.
  apply nat_in_nat.
Qed.
Hint Resolve all_zero_is_nat2nat : slow.

Lemma implies_inhabited_mkc_iff {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_fun a b)
    -> inhabited_type lib (mkc_fun b a)
    -> inhabited_type lib (mkc_iff a b).
Proof.
  introv imp1 imp2.
  unfold inhabited_type in *; exrepnd.
  exists (mkc_pair t0 t).
  apply equality_in_iff.
  dands; auto.

  { apply inhabited_implies_tequality in imp2.
    apply type_mkc_fun in imp2; repnd; auto. }

  { apply inhabited_implies_tequality in imp0.
    apply type_mkc_fun in imp0; repnd; auto. }

  { exists t0 t0 t t; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow);
      introv equ.

    {
      apply equality_in_fun in imp2; repnd.
      apply imp2; auto.
    }

    {
      apply equality_in_fun in imp0; repnd.
      apply imp0; auto.
    }
  }
Qed.

Lemma apply_one_at_zero_to_zero_computes_to_one {o} :
  forall lib x,
    @computes_to_valc o lib (mkc_apply (one_at_zero x) mkc_zero) mkc_one.
Proof.
  introv.
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
Qed.

Lemma apply_all_zero_to_nat_computes_to_zero {o} :
  forall lib x k,
    @computes_to_valc o lib (mkc_apply (all_zero x) (mkc_nat k)) mkc_zero.
Proof.
  introv.
  unfold one_at_zero.
  unfold computes_to_valc; simpl.
  split;[|unfold mk_one; eauto 3 with slow].
  apply reduces_to_if_step; csunf; simpl.
  unfold apply_bterm, lsubst; simpl; auto.
Qed.


(**

<<
   H |- ↓(∃a:ℕ → ℕ.((∃x:ℕ.a(x) = 1) ↔ A))

     By Kripke's Schema

     H |- A ∈ Type(i)
>>

 *)

Definition rule_kripke_s_schema {o}
           (A : @NTerm o)
           (a x : NVar)
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
                                       (mk_equality
                                          (mk_apply (mk_var a) (mk_var x))
                                          mk_one
                                          mk_tnat))
                                    A)))))
    [
      mk_baresequent H (mk_conclax (mk_member A (mk_uni i)))
    ]
    [].

Lemma rule_kripke_s_schema_true {o} :
  forall lib (A : @NTerm o)
         (a x : NVar)
         (i : nat)
         (H : @barehypotheses o)
         (cond1 : a <> x)
         (cond2 : !LIn a (free_vars A))
         (cond3 : !LIn x (free_vars A)),
    rule_true lib (rule_kripke_s_schema A a x i H).
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

  (* We prove some simple facts on our sequents *)
(*  assert (s <> n
          # s <> x
          # n <> x
          # con <> n
          # con <> s
          # con <> m

          # !LIn x (free_vars c)
          # !LIn s (free_vars c)
          # !LIn n (free_vars c)
          # !LIn con (free_vars c)

          # !LIn x (free_vars X)
          # !LIn s (free_vars X)
          # !LIn n (free_vars X)
          # !LIn m (free_vars X)
          # !LIn con (free_vars X)

          # !LIn con (free_vars B)

          # !LIn m (free_vars R)
          # !LIn n (free_vars R)
          # !LIn s (free_vars R)
          # !LIn x (free_vars R)
          # !LIn con (free_vars R)

          # !LIn x (vars_hyps H)
          # !LIn s (vars_hyps H)
          # !LIn n (vars_hyps H)
          # !LIn con (vars_hyps H)) as vhyps.

  {
    clear hyp_wfb hyp_wfr hyp_R0 hyp_bar hyp_ind hyp_imp.
    dwfseq.
    assert (forall x : NVar, LIn x (free_vars c) -> x <> v -> LIn x (vars_hyps H)) as imp.
    {
      introv h1 h2.
      apply cg.
      repeat (first [rw remove_nvars_cons_r|rw remove_nvars_app_r]).
      allrw memvar_singleton.
      allrw <- beq_var_refl.
      allrw remove_nvars_nil_r; allrw app_nil_r.
      rw in_remove_nvars; rw in_single_iff; sp.
    }
    sp; GC;
      try (complete (discover; allapply @subset_hs_vars_hyps; sp));
      try (complete (pose proof (ct12 con) as xx; autodimp xx hyp;
                     repeat (rw in_snoc in xx); repndors; tcsp));
      try (complete (pose proof (ct9 m) as xx; autodimp xx hyp;
                     repeat (rw in_snoc in xx); repndors; tcsp)).
  }

  destruct vhyps as [ nsn vhyps ].
  destruct vhyps as [ nsx vhyps ].
  destruct vhyps as [ nnx vhyps ].
  destruct vhyps as [ nconn vhyps ].
  destruct vhyps as [ ncons vhyps ].
  destruct vhyps as [ nconm vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nsc vhyps ].
  destruct vhyps as [ nnc vhyps ].
  destruct vhyps as [ nconc vhyps ].
  destruct vhyps as [ nxX vhyps ].
  destruct vhyps as [ nsX vhyps ].
  destruct vhyps as [ nnX vhyps ].
  destruct vhyps as [ nmX vhyps ].
  destruct vhyps as [ nconX vhyps ].
  destruct vhyps as [ nconB vhyps ].
  destruct vhyps as [ nmR vhyps ].
  destruct vhyps as [ nnR vhyps ].
  destruct vhyps as [ nsR vhyps ].
  destruct vhyps as [ nxR vhyps ].
  destruct vhyps as [ nconR vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nsH vhyps ].
  destruct vhyps as [ nnH nconH ].*)
  (* done with proving these simple facts *)

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
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        allrw @lsubstc_mk_one.

        apply tequality_mkc_equality2.
        dands.

        { apply type_tnat. }

        {
          split; intro h; eapply equality_trans; try (exact h);
            apply equality_nat2nat_apply; auto;
              try (complete (apply equality_sym; auto)).
        }

        {
          unfold equorsq2, equorsq; dands; try left.

          { apply equality_nat2nat_apply; auto. }

          { rw @mkc_one_as_mkc_nat.
            apply nat_in_nat. }
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
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        allrw @lsubstc_mkc_tnat.
        allrw @lsubstc_mk_one.

        apply tequality_mkc_equality2.
        dands.

        { apply type_tnat. }

        {
          split; intro h; eapply equality_trans; try (exact h);
            apply equality_nat2nat_apply; auto;
              try (complete (apply equality_sym; auto)).
        }

        {
          unfold equorsq2, equorsq; dands; try left.

          { apply equality_nat2nat_apply; auto. }

          { rw @mkc_one_as_mkc_nat.
            apply nat_in_nat. }
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

              apply tequality_mkc_equality2.
              dands.

              { apply type_tnat. }

              {
                split; intro h; eapply equality_trans; try (exact h);
                  apply equality_nat2nat_apply; auto;
                    try (complete (apply equality_sym; auto));
                    rw @member_eq; apply one_at_zero_is_nat2nat.
              }

              {
                unfold equorsq2, equorsq; dands; try left.

                { apply equality_nat2nat_apply; auto.
                  rw @member_eq; apply one_at_zero_is_nat2nat. }

                { rw @mkc_one_as_mkc_nat.
                  apply nat_in_nat. }
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
            exists (@mkc_lam o x (mkcv_pair [x] (mkcv_zero [x]) (mkcv_axiom x))).
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

              apply tequality_mkc_equality2.
              dands.

              { apply type_tnat. }

              {
                split; intro h; eapply equality_trans; try (exact h);
                  apply equality_nat2nat_apply; auto;
                    try (complete (apply equality_sym; auto));
                    rw @member_eq; apply one_at_zero_is_nat2nat.
              }

              {
                unfold equorsq2, equorsq; dands; try left.

                { apply equality_nat2nat_apply; auto.
                  rw @member_eq; apply one_at_zero_is_nat2nat. }

                { rw @mkc_one_as_mkc_nat.
                  apply nat_in_nat. }
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

                apply tequality_mkc_equality_sp; dands; eauto 3 with slow.

                { apply type_tnat. }

                {
                  apply equality_int_nat_implies_cequivc in equn.
                  right; spcast.
                  apply implies_cequivc_apply; auto.
                }

                {
                  right; spcast; auto.
                }
              }

              {
                exists (@mkc_zero o) (@mkc_zero o) (@mkc_axiom o) (@mkc_axiom o).
                dands; spcast; auto;
                  try (apply computes_to_valc_refl; eauto 3 with slow).

                { allrw @mkc_zero_eq.
                  apply nat_in_nat. }

                {
                  repeat substc_lsubstc_vars3.
                  lsubst_tac.
                  allrw @lsubstc_mkc_tnat.
                  allrw @lsubstc_mk_one.

                  apply member_equality.

                  eapply equality_respects_cequivc_left;
                    [apply cequivc_sym;
                     apply computes_to_valc_implies_cequivc;
                     apply apply_one_at_zero_to_zero_computes_to_one
                    |].
                  rw @mkc_one_as_mkc_nat.
                  apply nat_in_nat.
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

              apply tequality_mkc_equality2.
              dands.

              { apply type_tnat. }

              {
                split; intro h; eapply equality_trans; try (exact h);
                  apply equality_nat2nat_apply; auto;
                    try (complete (apply equality_sym; auto));
                    rw @member_eq; apply all_zero_is_nat2nat.
              }

              {
                unfold equorsq2, equorsq; dands; try left.

                { apply equality_nat2nat_apply; auto.
                  rw @member_eq; apply all_zero_is_nat2nat. }

                { rw @mkc_one_as_mkc_nat.
                  apply nat_in_nat. }
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
              clear equ2 equ4.
              repeat substc_lsubstc_vars3.
              lsubst_tac.

              apply equality_in_mkc_equality in equ3; repnd.
              clear equ3 equ4.
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
