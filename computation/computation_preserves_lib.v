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


Require Export computation3.

Lemma eq_opabs_implies :
  forall x y : opabs,
    x = y -> (opabs_name x = opabs_name y
              # opabs_params x = opabs_params y
              # opabs_sign x = opabs_sign y).
Proof.
  introv xx; subst; auto.
Qed.

Lemma opabs_deq : Deq opabs.
Proof.
  introv.
  destruct (decidable_eq_opabs_name x y);
    destruct (decidable_eq_opabs_sign x y);
    destruct (parameters_dec (opabs_params x) (opabs_params y));
    destruct x, y; simpl in *; subst; tcsp;
    try (complete (right; intro xx; apply eq_opabs_implies in xx; tcsp)).
Qed.

Lemma sovar_sig_deq : Deq sovar_sig.
Proof.
  introv.
  destruct x, y.
  destruct (deq_nat n0 n2); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
  destruct (deq_nvar n n1); subst; tcsp;
  try (complete (right; intro xx; inversion xx; subst; tcsp)).
Qed.

Definition same_opabs (oa1 oa2 : opabs) :=
  opabs_name oa1 = opabs_name oa2
  # opabs_sign oa1 = opabs_sign oa2
  # matching_parameters (opabs_params oa1) (opabs_params oa2).

Definition same_opabs_dec :
  forall oa1 oa2, decidable (same_opabs oa1 oa2).
Proof.
  introv.
  destruct (decidable_eq_opabs_name oa1 oa2) as [n|n];
    try (complete (right; intro xx; inversion xx; tcsp)).
  destruct (decidable_eq_opabs_sign oa1 oa2) as [s|s];
    try (complete (right; intro xx; inversion xx; tcsp)).

  unfold same_opabs.
  unfold matching_parameters, assert.
  destruct (matching_parametersb (opabs_params oa1) (opabs_params oa2)); simpl;
  try (complete (right; intro xx; inversion xx; tcsp)).
  left; dands; auto.
Qed.

Definition opabs_of_lib_entry {o} (e : @library_entry o) :=
  match e with
  | lib_abs opabs _ _ _ => opabs
  end.

Definition in_lib {o}
           (opabs : opabs)
           (lib   : @library o) :=
  {e : library_entry & LIn e lib # same_opabs opabs (opabs_of_lib_entry e)}.

Lemma in_lib_dec {o} :
  forall (opabs : opabs)
         (lib   : @library o),
    decidable (in_lib opabs lib).
Proof.
  unfold in_lib; induction lib; simpl.
  - right; intro xx; exrepnd; auto.
  - destruct a.
    destruct (same_opabs_dec opabs opabs0) as [d|d]; ginv.
    + left; eexists; eexists; eauto.
    + destruct IHlib as [k|k]; exrepnd.
      * left; eexists; eexists; eauto.
      * right; intro xx; exrepnd; repndors; subst; allsimpl; tcsp.
        destruct k; eexists; eexists; eauto.
Qed.

Lemma found_entry_in {o} :
  forall lib oa0 (bs : list (@BTerm o)) oa vars rhs correct,
    found_entry lib oa0 bs oa vars rhs correct
    -> LIn (lib_abs oa vars rhs correct) lib.
Proof.
  unfold found_entry.
  induction lib; introv fe; allsimpl; ginv.
  destruct a.
  boolvar; ginv; tcsp.
  - apply some_inj in fe; tcsp.
  - right.
    eapply IHlib; eauto.
Qed.

Lemma matching_paramsb_sym :
  forall p1 p2,
    matching_paramsb p1 p2 = true
    -> matching_paramsb p2 p1 = true.
Proof.
  introv m.
  destruct p1; allsimpl; tcsp.
  destruct pt; allsimpl; tcsp.
Qed.

Lemma matching_paramsb_trans :
  forall p1 p2 p3,
    matching_paramsb p1 p2 = true
    -> matching_paramsb p2 p3 = true
    -> matching_paramsb p1 p3 = true.
Proof.
  introv m1 m2.
  destruct p1; allsimpl; tcsp.
  destruct pt; allsimpl; tcsp.
  - destruct p2; allsimpl; tcsp.
    destruct pt; allsimpl; tcsp.
  - destruct p2; allsimpl; tcsp.
    destruct pt; allsimpl; tcsp.
Qed.

Lemma matching_parameters_sym :
  forall ps1 ps2,
    matching_parameters ps1 ps2
    -> matching_parameters ps2 ps1.
Proof.
  unfold matching_parameters, assert.
  induction ps1; introv m; simpl in *.
  - destruct ps2; allsimpl; tcsp.
  - destruct ps2; allsimpl; tcsp.
    allrw andb_eq_true; repnd.
    dands; eauto.
    eapply matching_paramsb_sym; eauto.
Qed.

Lemma matching_parameters_trans :
  forall ps1 ps2 ps3,
    matching_parameters ps1 ps2
    -> matching_parameters ps2 ps3
    -> matching_parameters ps1 ps3.
Proof.
  unfold matching_parameters, assert.
  induction ps1; introv m1 m2; simpl in *.
  - destruct ps2; allsimpl; tcsp.
  - destruct ps2; allsimpl; tcsp.
    destruct ps3; allsimpl; tcsp.
    allrw andb_eq_true; repnd.
    dands; eauto.
    eapply matching_paramsb_trans; eauto.
Qed.

Lemma found_entry_add_new_abs {o} :
  forall lib abs (bs : list (@BTerm o)) oa2 vars0 rhs0 correct0 opabs vars rhs correct,
    !in_lib opabs lib
    -> found_entry lib abs bs oa2 vars0 rhs0 correct0
    -> found_entry
         (lib_abs opabs vars rhs correct :: lib)
         abs bs oa2 vars0 rhs0 correct0.
Proof.
  introv nilib fe.
  applydup @found_entry_implies_matching_entry in fe.
  applydup @found_entry_in in fe.

  allunfold @found_entry; simpl.
  boolvar; auto.
  assert False; tcsp.

  unfold matching_entry in *; repnd.
  destruct nilib; unfold in_lib, same_opabs.
  eexists; dands; eauto; simpl; tcsp.

  apply matching_parameters_sym.
  eapply matching_parameters_trans; eauto.
  apply matching_parameters_sym; auto.
Qed.

Lemma compute_step_consistent_with_new_definition {o} {lib} :
  forall (e    : library_entry)
         (p    : !in_lib (opabs_of_lib_entry e) lib)
         (a b  : @NTerm o)
         (comp : compute_step lib a = csuccess b),
    compute_step (e :: lib) a = csuccess b.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          SSCase "NEApply".

          apply compute_step_eapply_success in comp; exrepnd; subst.
          repndors; exrepnd; allsimpl; subst.

          + apply compute_step_eapply2_success in comp1; repnd; subst.
            repndors; exrepnd; subst; ginv.
            csunf; simpl.
            dcwf h; simpl.
            boolvar; try omega.
            rewrite Znat.Nat2Z.id; auto.

          + csunf; simpl.
            apply isexc_implies2 in comp0; exrepnd; subst.
            dcwf h; simpl; auto.

          + fold_terms.
            rewrite compute_step_eapply_iscan_isnoncan_like; auto.
            pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            apply h in comp1; clear h.
            rewrite comp1; auto.

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

                + unfold mk_nseq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q.
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
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
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
                apply q in comp4; clear q.
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
            remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
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
            remember (compute_step lib (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - rewrite compute_step_fresh_if_isnoncan_like; auto.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.
          rewrite comp2; simpl; auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.
      destruct e.
      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).

      apply found_entry_add_new_abs; auto.
Qed.

Lemma reduces_to_consistent_with_new_definition {o} {lib} :
  forall (a b : @NTerm o)
         (r   : reduces_to lib a b)
         (e   : library_entry)
         (p   : !in_lib (opabs_of_lib_entry e) lib),
    reduces_to (e :: lib) a b.
Proof.
  introv r p.
  allunfold @reduces_to; exrepnd.
  exists k.
  revert dependent a.
  induction k; introv comp.
  - allrw @reduces_in_atmost_k_steps_0; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    exists u.
    dands;[|apply IHk;auto];[].
    apply compute_step_consistent_with_new_definition; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
