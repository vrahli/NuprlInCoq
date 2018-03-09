(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export computation_lib_extends.
Require Export computation_preserves_utok.


Lemma nt_wf_oterm_snd {o} :
  forall op l1 (t1 : @NTerm o) l2 t2 bs ,
    nt_wf (oterm op (bterm l1 t1 :: bterm l2 t2 :: bs)) -> nt_wf t2.
Proof.
  introv w.
  allrw @nt_wf_oterm_iff; repnd; allsimpl.
  pose proof (w (bterm l2 t2)) as w1; autodimp w1 hyp.
  allrw @bt_wf_iff; auto.
Qed.
Hint Resolve nt_wf_oterm_snd : slow.

Hint Resolve nt_wf_oterm_fst : slow.

Lemma lib_extends_implies_subset_get_utokens_lib {o} :
  forall (lib1 lib2 : @library o) t,
    lib_extends lib2 lib1
    -> subset (get_utokens_lib lib1 t) (get_utokens_lib lib2 t).
Proof.
  introv ext i.
  allrw in_app_iff; repndors; tcsp.
  right.
  eapply lib_extends_implies_subset_get_utokens_library; eauto.
Qed.

Lemma lib_extends_preserves_not_in_get_utokens_lib {o} :
  forall (lib1 lib2 : @library o) t a,
    lib_extends lib2 lib1
    -> !LIn a (get_utokens_lib lib2 t)
    -> !LIn a (get_utokens_lib lib1 t).
Proof.
  introv ext i j; destruct i.
  eapply lib_extends_implies_subset_get_utokens_lib; eauto.
Qed.
Hint Resolve lib_extends_preserves_not_in_get_utokens_lib : slow.

Hint Resolve subst_aux_preserves_wf : wf.

Lemma subst_utokens_aux_var_ren_utok {o} :
  forall (t : @NTerm o) a a' n,
    (!LIn a' (get_utokens t) [+] a = a')
    -> subst_utokens_aux (ren_utok t a a') [(a', mk_var n)]
       = subst_utokens_aux t [(a, mk_var n)].
Proof.
  nterm_ind t as [v|op bs ind] Case; introv h; tcsp.
  Case "oterm".
  allrw @ren_utok_oterm.
  allrw @subst_utokens_aux_oterm.

  unfold ren_utok_op.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; simpl.

  - boolvar; subst; tcsp; simpl.

    + unfold subst_utok; simpl; boolvar; tcsp.

    + allrw; simpl.
      unfold subst_utok; simpl.
      boolvar; tcsp; subst; tcsp.

      * repndors; tcsp.
        apply not_in_get_utokens_implies_not_in_get_utokens_o in h.
        apply get_utok_some_implies_get_utokens_o_eq in Heqguo.
        rewrite Heqguo in h; simpl in h; allrw not_over_or; tcsp.

      * allrw map_map; unfold compose.
        f_equal.
        apply eq_maps; introv i.
        destruct x as [l t]; simpl.
        f_equal.
        eapply ind; eauto.
        repndors; tcsp; eauto 3 with slow.

  - allrw; simpl.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl; f_equal.
    eapply ind; eauto.
    repndors; tcsp; eauto 3 with slow.
Qed.

Lemma subst_utokens_var_ren_utok {o} :
  forall (t : @NTerm o) a a' n,
    (!LIn a' (get_utokens t) [+] a = a')
    -> subst_utokens (ren_utok t a a') [(a', mk_var n)]
       = subst_utokens t [(a, mk_var n)].
Proof.
  introv h.
  unfold subst_utokens; autorewrite with slow.
  boolvar; tcsp.
  - apply subst_utokens_aux_var_ren_utok; tcsp.
  - rewrite change_bvars_alpha_ren_utok.
    rewrite subst_utokens_aux_var_ren_utok; autorewrite with slow; tcsp.
Qed.

(*
Lemma lib_extends_preserves_compute_step {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : nt_wf a)
         (comp : compute_step lib1 a = csuccess b),
    compute_step lib2 a = csuccess b.
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv wf comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|op bts]; try (complete (allsimpl; ginv));[].

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto.

                + unfold mk_choice_seq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; try omega.
                  autorewrite with slow.
                  eapply lib_extends_preserves_find_cs_value_at in comp5;[|eauto].
                  allrw; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q; eauto 2 with slow.
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCompSeq1".

              csunf comp; allsimpl.
              apply compute_step_comp_seq1_success in comp; exrepnd; subst.
              repndors; repnd; subst; csunf; simpl.
              { eexists; dands; eauto. }
              boolvar; autorewrite with slow in *; try omega.
              eexists; dands; eauto.
            }

            {
              SSSCase "NCompSeq2".

              csunf comp; allsimpl.
              apply compute_step_comp_seq2_success in comp; exrepnd; subst.
              repndors; repnd; subst; csunf; simpl.
              { boolvar; autorewrite with slow in *; try omega.
                eexists; dands; eauto. }
              { boolvar; autorewrite with slow in *; try omega.
                eexists; dands; eauto. }
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with slow.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with slow.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 2 with slow.
            csunf; simpl.
            rewrite Heqc; auto.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 2 with slow.
            csunf; simpl.
            rewrite Heqc; auto.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - fold (mk_fresh n t).
          rewrite compute_step_fresh_if_isnoncan_like; auto.

          remember (get_fresh_atom lib1 t) as a.
          pose proof (get_fresh_atom_prop_and_lib lib1 t) as prop; rewrite <- Heqa in prop.
          clear Heqa.

          remember (get_fresh_atom lib2 t) as a'.
          pose proof (get_fresh_atom_prop_and_lib lib2 t) as prop'; rewrite <- Heqa' in prop'.
          clear Heqa'.

          simpl.
          unfsubst in comp2.

          pose proof (compute_step_subst_utoken2 lib1 t x n a a') as w.
          repeat (autodimp w hyp); eauto 2 with slow.

          pose proof (ind t (subst t n (mk_utoken a')) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow;[|].
          { rewrite simple_osize_subst; eauto 2 with slow. }
          fold_terms.
          unfsubst in q.
          allrw @fold_subst_aux.
          apply q in w;[|eauto 4 with wf slow]; clear q.

          unfsubst.
          allrw @fold_subst_aux.
          allrw; simpl.

          rewrite subst_utokens_var_ren_utok; auto.

          apply compute_step_preserves_utokens in comp2;[|eauto 3 with slow wf].
          destruct (get_patom_deq o a a'); tcsp;[].
          left.
          introv i; eapply get_utokens_subset_get_utokens_lib in i.
          apply comp2 in i.
          apply implies_get_utokens_lib_subst_aux2 in i; tcsp; eauto 2 with slow.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.

      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).
      eapply lib_extends_preserves_find_entry; eauto.
Qed.

Lemma lib_extends_preserves_reduces_in_atmost_k_steps {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wfa  : wf_term a)
         (n    : nat)
         (comp : reduces_in_atmost_k_steps lib1 a b n),
    reduces_in_atmost_k_steps lib2 a b n.
Proof.
  introv ext wf comp.

  revert dependent a.
  induction n; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @compute_step_preserves_wf in comp1; auto.
    apply IHn in comp0; exrepnd; auto; clear IHn.
    apply (lib_extends_preserves_compute_step lib1 lib2) in comp1; eauto 2 with slow.
    allrw.
    eexists; dands; eauto.
Qed.

Lemma lib_extends_preserves_reduces_to {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : reduces_to lib1 a b),
    reduces_to lib2 a b.
Proof.
  introv ext wf r.
  unfold reduces_to in *; exrepnd.
  eapply lib_extends_preserves_reduces_in_atmost_k_steps in r0; eauto.
Qed.
Hint Resolve lib_extends_preserves_reduces_to : slow.

Lemma lib_extends_preserves_computes_to_value {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : computes_to_value lib1 a b),
    computes_to_value lib2 a b.
Proof.
  introv ext wf r.
  unfold computes_to_value in *; repnd.
  dup r0 as comp; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_computes_to_value : slow.

Lemma lib_extends_preserves_computes_to_valc {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @CTerm o)
         (comp : computes_to_valc lib1 a b),
    computes_to_valc lib2 a b.
Proof.
  introv ext r.
  destruct_cterms.
  unfold computes_to_valc in *; simpl in *.
  eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_computes_to_valc : slow.
 *)
