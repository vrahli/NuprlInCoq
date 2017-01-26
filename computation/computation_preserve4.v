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

Require Export computation_preserve3.


Lemma get_utokens_sub_sub_keep_first_subset {o} :
  forall (sub : @Sub o) l1 l2,
    subset l1 l2
    -> subset (get_utokens_sub (sub_keep_first sub l1))
              (get_utokens_sub (sub_keep_first sub l2)).
Proof.
  introv s i.
  allunfold @get_utokens_sub.
  allrw lin_flat_map; exrepnd.
  eexists; dands; eauto.
  allrw @in_range_iff; exrepnd.
  exists v.
  allrw @in_sub_keep_first; repnd; dands; auto.
Qed.

Lemma sub_keep_first_eq_nil {o} :
  forall (sub : @Sub o) vs,
    disjoint vs (dom_sub sub)
    -> sub_keep_first sub vs = [].
Proof.
  induction sub; introv disj; allsimpl; auto.
  destruct a as [v t]; allsimpl; allrw disjoint_cons_r; repnd.
  boolvar; tcsp.
Qed.

Lemma implies_subset_get_utokens_sub_sub_keep_first_flat_map {o} :
  forall {T} (l : list T) f atoms (sub : @Sub o),
    (forall x, LIn x l -> subset (get_utokens_sub (sub_keep_first sub (f x))) atoms)
    -> subset (get_utokens_sub (sub_keep_first sub (flat_map f l))) atoms.
Proof.
  introv imp i.
  allunfold @get_utokens_sub.
  allrw lin_flat_map; exrepnd.
  allrw @in_range_iff; exrepnd.
  allrw @in_sub_keep_first; repnd.
  allrw lin_flat_map; exrepnd.
  pose proof (imp x1 i2) as h.
  apply h.
  apply lin_flat_map.
  eexists; dands; eauto.
  apply in_range_iff.
  exists v.
  apply in_sub_keep_first; dands; auto.
Qed.

Lemma get_utokens_sub_sub_keep_first_subset_get_utokens_step_seq_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    subset
      (get_utokens_sub (sub_keep_first sub (free_vars t)))
      (get_utokens_step_seq (lsubst_aux t sub)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; allsimpl.

  - Case "vterm".
    remember (sub_find sub v) as sf; symmetry in Heqsf; destruct sf; simpl.

    + introv i.
      unfold get_utokens_sub in i; rw lin_flat_map in i; exrepnd.
      allrw @in_range_iff; exrepnd.
      allrw @in_sub_keep_first; repnd.
      allsimpl; repndors; subst; tcsp.
      rw i1 in Heqsf; ginv.
      apply subset_get_utokens_get_utokens_step_seq in i0; auto.

    + rw @sub_keep_first_eq_nil; autorewrite with slow; auto.
      introv i j; allsimpl; repndors; subst; tcsp.
      apply sub_find_none2 in Heqsf; sp.

  - Case "sterm".
    rw @sub_keep_first_eq_nil; autorewrite with slow; eauto 3 with slow.

  - Case "oterm".
    allrw @fold_get_utokens_step_seq_bterms_seq.
    allrw @fold_get_utokens_step_seq_op_seq.
    apply implies_subset_get_utokens_sub_sub_keep_first_flat_map.
    introv i.
    destruct x as [l t]; allsimpl.
    allrw flat_map_map; unfold compose.
    apply subset_app_l.
    apply subset_app_r.
    eapply subset_trans;[|apply subsetSingleFlatMap;eauto].
    simpl.
    eapply subset_trans;[|eapply ind;eauto 3 with slow].

    introv j.
    allunfold @get_utokens_sub.
    allrw lin_flat_map; exrepnd.
    allrw @in_range_iff; exrepnd.
    allrw @in_sub_keep_first; repnd.
    allrw in_remove_nvars; repnd.
    eexists; dands; eauto.
    apply in_range_iff.
    exists v.
    apply in_sub_keep_first; dands; auto.
    rw @sub_find_sub_filter_eq.
    boolvar; tcsp.
Qed.

Lemma compute_step_lsubst_aux {o} :
  forall lib (t u : @NTerm o) sub,
    nt_wf t
    -> cl_sub sub
    -> subvars (free_vars t) (dom_sub sub)
    -> compute_step lib t = csuccess u
    -> {v : NTerm
        & compute_step lib (lsubst_aux t sub) = csuccess v
        # alpha_eq v (lsubst_aux u sub)}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf cl sv comp; ginv.

  - Case "sterm".
    allsimpl.
    csunf comp; allsimpl; ginv.
    csunf; simpl; eexists; dands; eauto.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).
      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [v|f|op bts]; try (complete (allsimpl; ginv)).

        { allsimpl.
          dopid_noncan ncan SSCase; try (complete (csunf comp; allsimpl; ginv)).

          - SSCase "NApply".
            csunf comp; allsimpl.
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
            allrw remove_nvars_nil_l; allrw app_nil_r.
            allrw @sub_filter_nil_r.
            csunf; simpl.
            eexists; dands; eauto.

          - SSCase "NEApply".
            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
            allrw remove_nvars_nil_l.
            repndors; exrepnd; subst; allsimpl.

            + apply compute_step_eapply2_success in comp1; exrepnd; subst; allsimpl.
              allrw app_nil_r.
              repndors; exrepnd; subst; ginv; allsimpl; GC.
              csunf; simpl.
              dcwf h; simpl.
              boolvar; try omega.
              rw Znat.Nat2Z.id.
              eexists; dands; eauto.
              allrw @nt_wf_eapply_iff; exrepnd; allunfold @nobnd; ginv.
              allrw @nt_wf_sterm_iff.
              pose proof (wf2 n) as q; repnd.
              rw @lsubst_aux_trivial_cl_term2; auto.

            + allrw @sub_filter_nil_r.
              apply isexc_implies2 in comp0; exrepnd; subst; allsimpl.
              csunf; simpl.
              dcwf h; simpl.
              eexists; dands; eauto.

            + allrw @sub_filter_nil_r.
              fold_terms.
              pose proof (ind arg2 arg2 []) as h; repeat (autodimp h hyp); eauto 3 with slow; clear ind.
              pose proof (h x sub) as ih; clear h.
              allrw @nt_wf_eapply_iff; exrepnd; allunfold @nobnd; ginv.
              allrw @nt_wf_sterm_iff.
              allsimpl; allrw app_nil_r.
              repeat (autodimp ih hyp); exrepnd.
              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow.
              rw ih1; eexists; dands; eauto.
              apply implies_alpha_eq_mk_eapply; eauto 3 with slow.

          - SSCase "NFix".
            csunf comp; allsimpl.
            apply compute_step_fix_success in comp; repnd; subst; allsimpl.
            csunf; simpl.
            eexists; dands; eauto.

          - SSCase "NCbv".
            csunf comp; allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
            allrw app_nil_r.
            csunf; simpl; eexists; dands; eauto.
            unfold apply_bterm; simpl; allrw @fold_subst.

            pose proof (simple_lsubst_lsubst_aux_sub_aeq x [(v,sterm f)] sub) as h.
            repeat (autodimp h hyp).
            rw @covered_sub_cons; dands; eauto 3 with slow.
            unfold covered; simpl; auto.

          - SSCase "NTryCatch".
            csunf comp; allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
            allrw remove_nvars_nil_l; allrw app_nil_r.
            allrw @sub_filter_nil_r.
            csunf; simpl; eexists; dands; eauto;[].
            apply implies_alpha_eq_mk_atom_eq; eauto 3 with slow.
            rw @sub_find_sub_filter; simpl; tcsp.

          - SSCase "NCanTest".
            csunf comp; allsimpl.
            apply nt_wf_NCanTest in wf; exrepnd; allunfold @nobnd; ginv; allsimpl.
            autorewrite with slow in *.
            allrw subvars_app_l; repnd.
            csunf; simpl.
            eexists; dands; eauto.
        }

        dopid op as [can2|ncan2|exc2|abs2] SSCase.

        * SSCase "Can".
          dopid_noncan ncan SSSCase.

          { SSSCase "NApply".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; fold_terms.

            { simpl; unfold apply_bterm; simpl.
              allrw @sub_filter_nil_r.

              allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.
              allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

              eexists;dands;[complete eauto|].

              pose proof (simple_lsubst_lsubst_aux_sub_aeq b [(v,arg)] sub) as h.
              repeat (autodimp h hyp).
              rw @covered_sub_cons; dands; auto.
              apply covered_sub_nil. }

            { allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r.
              allrw @sub_filter_nil_r.
              eexists; dands; eauto. }
          }

          { SSSCase "NEApply".

            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
            allrw remove_nvars_nil_l.
            repndors; exrepnd; allsimpl; subst; autorewrite with slow in *.

            - apply compute_step_eapply2_success in comp1; repnd; subst; allsimpl.
              allrw app_nil_r.
              repndors; exrepnd; subst; allsimpl; ginv;[|].

              { unfold mk_lam in comp3; ginv; allsimpl; autorewrite with slow in *.
                fold_terms; unfold mk_eapply.
                rw @compute_step_eapply_lam_iscan; eauto 3 with slow.
                eexists; dands; eauto.
                unfold apply_bterm; simpl; allrw @fold_subst.
                allrw subvars_app_l; repnd.

                pose proof (simple_lsubst_lsubst_aux_sub_aeq b [(v,arg2)] sub) as h.
                repeat (autodimp h hyp).
                rw @covered_sub_cons; dands; eauto 3 with slow. }

              { allunfold @mk_nseq; allsimpl; ginv; GC; allsimpl; fold_terms.
                csunf; simpl; dcwf h; simpl; boolvar; try omega.
                rw @Znat.Nat2Z.id.
                eexists; dands; eauto. }

            - fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isexc; simpl; eauto 3 with slow.
              eapply eapply_wf_def_len_implies;[|exact comp2].
              allrw map_map; unfold compose.
              apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto.

            - allrw @sub_filter_nil_r.
              pose proof (ind arg2 arg2 []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              allrw @nt_wf_eapply_iff; exrepnd; subst; allsimpl; allunfold @nobnd; ginv.
              allsimpl; allrw app_nil_r.
              allrw subvars_app_l; repnd.
              pose proof (h x sub) as ih; clear h.
              repeat (autodimp ih hyp); eauto 3 with slow.
              exrepnd.

              fold_terms; unfold mk_eapply.
              rw @compute_step_eapply_iscan_isnoncan_like; simpl; eauto 3 with slow.
              { rw ih1; eexists; dands; eauto.
                allrw @sub_filter_nil_r.
                fold_terms.
                apply implies_alpha_eq_mk_eapply; auto. }
              { eapply eapply_wf_def_len_implies;[|exact comp2].
                allrw map_map; unfold compose.
                apply eq_maps; introv i; destruct x0; unfold num_bvars; simpl; auto. }
          }

(*          { SSSCase "NApseq".

            clear ind; csunf comp; csunf; allsimpl.
            apply compute_step_apseq_success in comp; exrepnd; subst; allsimpl.
            boolvar; try omega.
            rw @Znat.Nat2Z.id.
            eexists; dands; eauto.
          }*)

          { SSSCase "NFix".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_fix_success in comp; repnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.

            eexists;dands;[complete eauto|];auto. }

          { SSSCase "NSpread".

            clear ind; csunf comp; simpl in comp.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl; fold_terms.
            csunf; allsimpl.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

            eexists;dands;[complete eauto|].

            pose proof (simple_lsubst_lsubst_aux_sub_aeq arg [(va,a),(vb,b)] sub) as h.
            repeat (autodimp h hyp).
            rw @covered_sub_cons; dands; auto.
            rw @covered_sub_cons; dands; auto.
            apply covered_sub_nil. }

          { SSSCase "NDsup".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

            eexists;dands;[complete eauto|].

            pose proof (simple_lsubst_lsubst_aux_sub_aeq arg [(va,a),(vb,b)] sub) as h.
            repeat (autodimp h hyp).
            rw @covered_sub_cons; dands; auto.
            rw @covered_sub_cons; dands; auto.
            apply covered_sub_nil. }

          { SSSCase "NDecide".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

            dorn comp0; repnd; subst; allsimpl.

            - eexists;dands;[complete eauto|].

              pose proof (simple_lsubst_lsubst_aux_sub_aeq t1 [(v1,d)] sub) as h.
              repeat (autodimp h hyp).
              rw @covered_sub_cons; dands; auto.
              apply covered_sub_nil.

            - eexists;dands;[complete eauto|].

              pose proof (simple_lsubst_lsubst_aux_sub_aeq t2 [(v2,d)] sub) as h.
              repeat (autodimp h hyp).
              rw @covered_sub_cons; dands; auto.
              apply covered_sub_nil. }

          { SSSCase "NCbv".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

            eexists;dands;[complete eauto|].

            pose proof (simple_lsubst_lsubst_aux_sub_aeq x [(v,oterm (Can can2) bts)] sub) as h.
            repeat (autodimp h hyp).
            rw @covered_sub_cons; dands; auto.
            apply covered_sub_nil. }

          { SSSCase "NSleep".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.

            unfold compute_step_sleep; simpl.
            eexists;dands;[complete eauto|]; auto. }

          { SSSCase "NTUni".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl; fold_terms.

            unfold compute_step_tuni; simpl.
            boolvar; try omega.
            eexists;dands;[complete eauto|]; auto.
            rw Znat.Nat2Z.id; auto. }

          { SSSCase "NMinus".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl; fold_terms.

            eexists; dands; eauto.
            unfold compute_step_minus; simpl; auto. }

          { SSSCase "NFresh".

            csunf comp; allsimpl; ginv. }

          { SSSCase "NTryCatch".

            clear ind; csunf comp; csunf; simpl in comp.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.
            allrw subvars_app_l; allrw subvars_remove_nvars; repnd.
            allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar.
            eexists;dands; eauto. }

          { SSSCase "NParallel".
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; subst; allsimpl; fold_terms.
            exists (@mk_axiom o); dands; auto. }

          { SSSCase "NCompOp".

            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            - SSSSCase "Can".
              csunf comp; csunf; simpl in comp; boolvar; tcsp; ginv.
              dcwf h;[].
              apply compute_step_compop_success_can_can in comp; exrepnd; subst; allsimpl.
              dcwf h;[].
              boolvar; tcsp.

              repndors; exrepnd; subst;
              allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r;
              allrw @get_param_from_cop_some; subst; allsimpl;
              unfold compute_step_comp; simpl;
              allrw @get_param_from_cop_pk2can;
              eexists; dands; eauto;
              boolvar; tcsp.

            - SSSSCase "NCan".
              rw @compute_step_ncompop_ncan2 in comp; boolvar; tcsp; ginv.
              dcwf h;allsimpl;[].
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1; destruct comp1; ginv.
              simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; repnd.
              allrw @nt_wf_NCompOp; exrepnd; allunfold @nobnd; ginv.
              allsimpl; allrw @sub_filter_nil_r; allrw remove_nvars_nil_l; allrw app_nil_r.
              eapply (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2)) in Heqcomp1;eauto 3 with slow;exrepnd;[].

              allsimpl; rw @compute_step_ncompop_ncan2; boolvar; tcsp.
              allrw @sub_filter_nil_r.
              rw Heqcomp1.
              dcwf h; allsimpl;[].

              eexists;dands;[complete eauto|].
              apply alpha_eq_oterm_snd_subterm.
              apply alphaeqbt_nilv2; auto.

            - SSSSCase "Exc".
              csunf comp; csunf; allsimpl.
              repeat (dcwf h);[].
              boolvar; tcsp; ginv.
              allsimpl; ginv; allsimpl; allrw remove_nvars_nil_l;
              allrw subvars_app_l; allrw @sub_filter_nil_r; repnd.
              eexists;dands;[complete eauto|]; auto.

            - SSSSCase "Abs".
              allsimpl.
              csunf comp; csunf; allsimpl; boolvar; tcsp; ginv.
              repeat (dcwf h);[].
              allunfold @on_success.
              allrw remove_nvars_nil_l; allrw @sub_filter_nil_r.
              allrw subvars_app_l; repnd.
              csunf comp; csunf; allsimpl.

              remember (compute_step_lib lib abs3 bs2) as csl;
                symmetry in Heqcsl; destruct csl; ginv; simpl;
                allrw @sub_filter_nil_r.

              applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
              applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
              unfold matching_entry in Heqcsl0; repnd.

              pose proof (compute_step_lib_success_change_bs
                            lib abs3 oa2
                            bs2 (map (fun t : BTerm => lsubst_bterm_aux t sub) bs2)
                            vars rhs correct) as h.
              repeat (autodimp h hyp);
                [ rw map_map; unfold compose; apply eq_maps;
                  introv j; destruct x; unfold num_bvars; auto
                | ].
              rw h; clear h.

              eexists;dands;[complete eauto|].
              auto.
              apply alpha_eq_oterm_snd_subterm.
              apply alphaeqbt_nilv2; auto.

              unfold correct_abs in correct; repnd.
              fold (lsubst_bterms_aux bs2 sub).
              apply alpha_eq_lsubst_aux_mk_instance; auto.
          }

          { SSSCase "NArithOp".

            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b as [l t].
            destruct l; destruct t as [v|f|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            - SSSSCase "Can".
              csunf comp; csunf; allsimpl.
              repeat (dcwf h);[].
              boolvar; tcsp; ginv.
              apply compute_step_arithop_success_can_can in comp; exrepnd; subst; allsimpl.
              allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r;
              unfold compute_step_arith; rw comp3; rw comp5; simpl.

              eexists; dands; eauto.

            - SSSSCase "NCan".
              allsimpl.
              allrw @compute_step_narithop_ncan2; boolvar; tcsp; ginv.
              repeat (dcwf h); [].
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1; destruct comp1; ginv.
              simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; repnd.
              allrw @nt_wf_NArithOp; exrepnd; allunfold @nobnd; ginv.
              allsimpl; allrw @sub_filter_nil_r; allrw remove_nvars_nil_l; allrw app_nil_r.
              eapply ind in Heqcomp1; eauto 3 with slow; exrepnd;[].
              allsimpl; allrw @sub_filter_nil_r; rw Heqcomp1.

              eexists;dands;[complete eauto|].
              simpl.
              apply alpha_eq_oterm_snd_subterm.
              apply alphaeqbt_nilv2; auto.

            - SSSSCase "Exc".
              csunf comp; csunf; allsimpl; boolvar; tcsp; ginv.
              repeat (dcwf h);[].
              allsimpl; ginv; allsimpl; allrw remove_nvars_nil_l;
              allrw subvars_app_l; allrw @sub_filter_nil_r; repnd.
              eexists;dands;[complete eauto|]; auto.

            - SSSSCase "Abs".
              allsimpl.
              allrw @compute_step_narithop_abs2; boolvar; tcsp; ginv.
              repeat (dcwf h);[].
              allunfold @on_success.
              allrw remove_nvars_nil_l; allrw @sub_filter_nil_r.
              allrw subvars_app_l; repnd.

              remember (compute_step_lib lib abs3 bs2) as csl;
                symmetry in Heqcsl; destruct csl; ginv; simpl;
                allrw @sub_filter_nil_r.

              applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
              applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
              unfold matching_entry in Heqcsl0; repnd.

              pose proof (compute_step_lib_success_change_bs
                            lib abs3 oa2
                            bs2 (map (fun t : BTerm => lsubst_bterm_aux t sub) bs2)
                            vars rhs correct) as h.
              repeat (autodimp h hyp);
                [ rw map_map; unfold compose; apply eq_maps;
                  introv j; destruct x; unfold num_bvars; auto
                | ].
              rw h; clear h.

              eexists;dands;[complete eauto|].
              auto.
              apply alpha_eq_oterm_snd_subterm.
              apply alphaeqbt_nilv2; auto.

              unfold correct_abs in correct; repnd.
              fold (lsubst_bterms_aux bs2 sub).
              apply alpha_eq_lsubst_aux_mk_instance; auto.
          }

          { SSSCase "NCanTest".

            clear ind; csunf comp; csunf; allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl; fold_terms.
            allrw remove_nvars_nil_l; allrw app_nil_r; allrw @sub_filter_nil_r.

            eexists;dands;[complete eauto|].

            remember (canonical_form_test_for c can2) as cft; destruct cft; auto. }

        * SSCase "NCan".
          allsimpl.
          allrw @compute_step_ncan_ncan.
          remember (compute_step lib (oterm (NCan ncan2) bts)) as cs;
            symmetry in Heqcs; destruct cs; ginv.
          simpl in sv; allrw remove_nvars_nil_l; allrw subvars_app_l; repnd.
          pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as h;
            repeat (autodimp h hyp); eauto 3 with slow.
          applydup @nt_wf_oterm_fst in wf.
          eapply h in Heqcs; eauto; exrepnd; clear h;[].
          allrw @sub_filter_nil_r.
          allsimpl; rw Heqcs1.

          eexists;dands;[complete eauto|].
          simpl; allrw @sub_filter_nil_r.
          apply alpha_eq_oterm_fst_subterm.
          apply alphaeqbt_nilv2; auto.

        * SSCase "Exc".
          csunf comp; csunf; allsimpl.
          apply compute_step_catch_success in comp; dorn comp; exrepnd; subst;
          allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r;
          allrw subvars_app_l; repnd; allrw @sub_filter_nil_r.

          { eexists;dands;[complete eauto|].

            apply implies_alpha_eq_mk_atom_eq; auto.

            pose proof (simple_lsubst_lsubst_aux_sub_aeq b [(v,e)] sub) as h.
            repeat (autodimp h hyp).
            rw @covered_sub_cons; dands; auto.
            apply covered_sub_nil. }

          { rw @compute_step_catch_non_trycatch; auto.
            eexists;dands;[complete eauto|]; auto. }

        * SSCase "Abs".
          allsimpl.
          allrw @compute_step_ncan_abs.
          allunfold @on_success.

          allrw remove_nvars_nil_l; allrw @sub_filter_nil_r.
          allrw subvars_app_l; repnd.

          remember (compute_step_lib lib abs2 bts) as csl;
            symmetry in Heqcsl; destruct csl; ginv; simpl;
            allrw @sub_filter_nil_r.

          applydup @compute_step_lib_success in Heqcsl; exrepnd; subst.
          applydup @found_entry_implies_matching_entry in Heqcsl1; auto.
          unfold matching_entry in Heqcsl0; repnd.

          pose proof (compute_step_lib_success_change_bs
                        lib abs2 oa2
                        bts (map (fun t : BTerm => lsubst_bterm_aux t sub) bts)
                        vars rhs correct) as h.
          repeat (autodimp h hyp);
            [ rw map_map; unfold compose; apply eq_maps;
              introv i; destruct x; unfold num_bvars; auto
            | ].
          rw h; clear h.

          eexists;dands;[complete eauto|].
          auto.
          apply alpha_eq_oterm_fst_subterm.
          apply alphaeqbt_nilv2; auto.

          unfold correct_abs in correct; repnd.
          fold (lsubst_bterms_aux bts sub).
          apply alpha_eq_lsubst_aux_mk_instance; auto.
      }

      { csunf comp; csunf; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst.

        - allsimpl.
          rw @sub_find_sub_filter; tcsp.
          boolvar.
          eexists; dands; eauto.

        - rw @compute_step_fresh_if_isvalue_like0; eauto with slow.
          eexists; dands; eauto.
          repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
          apply alpha_eq_sym.
          apply cl_lsubst_pushdown_fresh; eauto with slow.

        - rw @compute_step_fresh_if_isnoncan_like0; eauto with slow; allsimpl; allrw app_nil_r.

          remember (get_fresh_atom t) as a'.
          remember (get_fresh_atom (lsubst_aux t (sub_filter sub [n]))) as a''.

          pose proof (get_fresh_atom_prop t) as fa'; rw <- Heqa' in fa'.
          pose proof (get_fresh_atom_prop (lsubst_aux t (sub_filter sub [n]))) as fa''; rw <- Heqa'' in fa''.

          pose proof (compute_step_subst_utoken lib t x [(n, mk_utoken a')]) as ch.
          allrw @nt_wf_fresh.
          repeat (autodimp ch hyp); eauto with slow.
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; tcsp. }
          exrepnd.

          pose proof (ch0 [(n,mk_utoken a'')]) as comp'; clear ch0; allsimpl.
          repeat (autodimp comp' hyp).
          { apply nr_ut_sub_cons; auto; introv i j.
            destruct fa''.
            apply get_utokens_lsubst_aux; rw in_app_iff; tcsp. }
          { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; intro i.
            destruct fa''.
            apply get_utokens_lsubst_aux; rw in_app_iff; tcsp. }
          exrepnd.
          allrw @fold_subst.

          pose proof (ind t (subst t n (mk_utoken a'')) [n]) as h; clear ind.
          repeat (autodimp h hyp).
          { rw @simple_osize_subst; eauto 3 with slow. }
          pose proof (h s (sub_filter sub [n])) as k; clear h.
          repeat (autodimp k hyp); eauto 3 with slow.
          { apply nt_wf_subst; eauto 3 with slow. }
          { rw @cl_subst_subst_aux; eauto 3 with slow.
            unfold subst_aux; allsimpl; allrw app_nil_r.
            rw @free_vars_lsubst_aux_cl; simpl; eauto with slow.
            rw <- @dom_sub_sub_filter.
            allrw subvars_prop; introv i; applydup sv in i.
            allrw in_remove_nvars; allsimpl; allrw not_over_or; repnd; sp. }

          exrepnd.
          rw <- @cl_lsubst_lsubst_aux in k1; eauto with slow.
          unfold subst in k1.
          rw @substitution3.cl_lsubst_swap in k1; simpl; eauto with slow;
          [|rw disjoint_singleton_l; rw <- @dom_sub_sub_filter; rw in_remove_nvars; simpl; complete sp].
          rw <- @cl_lsubst_lsubst_aux; eauto with slow.
          unfold subst.
          rw k1; simpl.

          eexists; dands; eauto.

          assert (alpha_eq v (lsubst w (sub_filter sub [n] ++ [(n,mk_utoken a'')]))) as aeq.
          { eapply alpha_eq_trans;[exact k0|].
            rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
            eapply (alpha_eq_trans _ (lsubst (subst w n (mk_utoken a'')) (sub_filter sub [n]))).
            - apply alpha_eq_lsubst_if_ext_eq; eauto 3 with slow.
            - unfold subst; rw <- @cl_lsubst_app; eauto 3 with slow.
              apply alpha_eq_lsubst_if_ext_eq; auto; introv i.
              allrw @sub_find_app; allrw @sub_find_sub_filter_eq; simpl;[].
              rw memvar_singleton; boolvar; tcsp; eauto 3 with slow;[].
              remember (sub_find sub v0) as sf; destruct sf; simpl; auto. }

          pose proof (implies_alpha_eq_mk_fresh_subst_utokens
                        n a'' v
                        (lsubst w (sub_filter sub [n] ++ [(n, mk_utoken a'')]))
                        aeq) as h.
          eapply alpha_eq_trans;[exact h|clear h].
          rw @cl_lsubst_app; eauto 3 with slow.
          rw <- @cl_lsubst_lsubst_aux in fa''; eauto 3 with slow.
          eapply alpha_eq_trans;[apply implies_alpha_eq_mk_fresh; apply simple_alphaeq_subst_utokens_subst|].

          { intro h.
            allrw @get_utokens_lsubst; allrw in_app_iff; allrw not_over_or; repnd.
            repndors; tcsp.
            - eapply get_utokens_sub_sub_keep_first_subset in h;
              [|apply subvars_eq in ch3;eauto]; tcsp. }

          apply implies_alpha_eq_mk_fresh.
          apply (alpha_eq_subst_utokens _ _ [(a',mk_var n)] [(a',mk_var n)]) in ch1; eauto 3 with slow.
          pose proof (simple_alphaeq_subst_utokens_subst w n a') as aeq1.
          autodimp aeq1 hyp.
          { intro k; apply ch4 in k; tcsp. }

          assert (alpha_eq (subst_utokens x [(a', mk_var n)]) w) as aeq2; eauto 3 with slow; clear aeq1.

          apply (lsubst_alpha_congr2 _ _ (sub_filter sub [n])) in aeq2.
          rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      }

    + SCase "Exc".
      csunf comp; csunf; allsimpl; ginv.
      eexists; dands; eauto.

    + SCase "Abs".
      csunf comp; allsimpl.
      csunf; simpl.

      applydup @compute_step_lib_success in comp; exrepnd; subst.
      applydup @found_entry_implies_matching_entry in comp1; auto.
      unfold matching_entry in comp0; repnd.

      pose proof (compute_step_lib_success_change_bs
                    lib abs oa2
                    bs (map (fun t : BTerm => lsubst_bterm_aux t sub) bs)
                    vars rhs correct) as h.
      repeat (autodimp h hyp);
        [ rw map_map; unfold compose; apply eq_maps;
          introv i; destruct x; unfold num_bvars; auto
        | ].
      rw h; clear h.

      eexists;dands;[complete eauto|].
      auto.

      unfold correct_abs in correct; repnd.
      fold (lsubst_bterms_aux bs sub).
      apply alpha_eq_lsubst_aux_mk_instance; auto.
Qed.

(* !!MOVE *)
Hint Resolve subvars_trans : slow.

Lemma is_utok_implies_wf {o} :
  forall (t : @NTerm o), is_utok t -> wf_term t.
Proof.
  introv h.
  apply is_utok_implies in h; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve is_utok_implies_wf : slow.

Lemma is_utok_sub_implies_wf_sub {o} :
  forall (sub : @Sub o),
    is_utok_sub sub -> wf_sub sub.
Proof.
  induction sub; introv h; eauto 3 with slow.
  destruct a.
  allrw @is_utok_sub_cons; repnd.
  apply wf_sub_cons; eauto 3 with slow.
Qed.
Hint Resolve is_utok_sub_implies_wf_sub : slow.

Lemma wf_term_utok {o} :
  forall a (bs : list (@BTerm o)),
    wf_term (oterm (Can (NUTok a)) bs)
    <=> (bs = []).
Proof.
  introv; split; intro k; subst; auto; allrw @wf_oterm_iff; allsimpl; repnd; tcsp.
  destruct bs; allsimpl; cpx.
Qed.

Lemma alphaeq_preserves_wf_term {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> wf_term t1
    -> wf_term t2.
Proof.
  introv aeq w.
  apply alphaeq_preserves_wf in aeq.
  allrw @wf_term_eq; apply aeq; auto.
Qed.
Hint Resolve alphaeq_preserves_wf_term : slow.

Hint Rewrite diff_nil : slow.

Lemma get_utokens_subst_utokens_aux_subset2 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> subset (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens t))
              (get_utokens (subst_utokens_aux t sub)).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; auto.

  - Case "vterm".
    allsimpl; auto.
    rw diff_nil; auto.

  - Case "sterm".
    allsimpl; autorewrite with slow; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      allrw @wf_term_utok; subst; allsimpl.
      remember (utok_sub_find sub g) as sf; symmetry in Heqsf; destruct sf; allsimpl.

      * apply utok_sub_find_some in Heqsf.
        apply in_utok_sub_eta in Heqsf; repnd.
        rw diff_cons_r; boolvar; tcsp; GC.
        rw diff_nil; auto.

      * apply utok_sub_find_none in Heqsf.
        rw diff_cons_r; boolvar; tcsp.
        rw diff_nil; auto.

    + rw diff_app_r.
      allapply @get_utok_none; allrw; simpl.
      allrw diff_nil; simpl.
      allrw flat_map_map; unfold compose.
      rw diff_flat_map_r.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; allsimpl.
      eapply ind; eauto.
      allrw @wf_oterm_iff; repnd.
      pose proof (wf (bterm l t)) as k; sp.
Qed.

Lemma get_utokens_subst_utokens_subset2 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> subset
         (diff (get_patom_deq o) (utok_sub_dom sub) (get_utokens t))
         (get_utokens (subst_utokens t sub)).
Proof.
  introv w i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0.
  applydup @alphaeq_preserves_utokens in h1 as k; rw k in i.
  apply get_utokens_subst_utokens_aux_subset2; eauto with slow.
Qed.

(*
Lemma get_utokens_ot_subst_utokens_aux_subset2 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> subset
         (get_utokens_ot t)
         (get_utokens_ot (subst_utokens_aux t sub)).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv wf.

  - Case "vterm".
    allsimpl; auto.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo; allsimpl.

    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold subst_utok.
      allrw @wf_term_utok; subst; allsimpl; auto.

    + allrw @wf_oterm_iff; repnd.
      apply subset_app_lr; auto.
      allrw flat_map_map; unfold compose.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; allsimpl.
      eapply ind; eauto.
      pose proof (wf (bterm l t)) as k; sp.
Qed.

Lemma get_utokens_ot_subst_utokens_subset2 {o} :
  forall (t : @NTerm o) sub,
    wf_term t
    -> subset (get_utokens_ot t) (get_utokens_ot (subst_utokens t sub)).
Proof.
  introv wf i.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd; rw h0.
  applydup @alphaeq_preserves_utokens_ot in h1 as k; rw k in i.
  apply get_utokens_ot_subst_utokens_aux_subset2; eauto with slow.
Qed.
*)

Lemma wf_term_implies {o} :
  forall (t : @NTerm o), wf_term t -> nt_wf t.
Proof.
  introv w.
  apply nt_wf_eq; auto.
Qed.
Hint Resolve wf_term_implies : slow.

Hint Resolve preserve_nt_wf_compute_step : slow.
Hint Resolve nt_wf_implies : slow.

Lemma compute_step_preserves_wf {o} :
  forall lib (t1 t2 : @NTerm o),
    compute_step lib t1 = csuccess t2
    -> wf_term t1
    -> wf_term t2.
Proof.
  introv comp wf.
  eauto with slow.
Qed.
Hint Resolve compute_step_preserves_wf : slow.

Lemma isprogram_implies_wf {o} :
  forall (t : @NTerm o), isprogram t -> wf_term t.
Proof.
  introv isp.
  destruct isp; eauto with slow.
Qed.

Hint Resolve eqset_trans : slow.
Hint Resolve eqset_sym : slow.

Lemma sub_bound_vars_allvars_sub {o} :
  forall (sub : @Sub o),
    allvars_sub sub
    -> sub_bound_vars sub = [].
Proof.
  induction sub; introv h; allsimpl; auto.
  destruct a.
  allrw @allvars_sub_cons; repnd.
  rw IHsub; auto.
  apply isvariable_implies in h0; exrepnd; subst; simpl; auto.
Qed.

Lemma alpha_eq_subst_utoken_not_in_implies {o} :
  forall (t1 t2 : @NTerm o) v a,
    !LIn a (get_utokens t1)
    -> !LIn a (get_utokens t2)
    -> !LIn v (bound_vars t1)
    -> !LIn v (bound_vars t2)
    -> alpha_eq (subst t1 v (mk_utoken a)) (subst t2 v (mk_utoken a))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case; introv ni1 ni2 nib1 nib2 aeq; allsimpl; GC.

  - Case "vterm".
    repeat (unfsubst in aeq); allsimpl; boolvar.

    + destruct t2 as [v2|f2|op2 bs2]; allsimpl; boolvar; tcsp;
      try (complete (inversion aeq)).

      inversion aeq; allsimpl; subst.
      destruct bs2; allsimpl; cpx; GC.
      destruct ni2; sp.

    + destruct t2 as [v2|f2|op2 bs2]; allsimpl; boolvar; tcsp;
      try (complete (inversion aeq)).

  - Case "sterm".
    repeat (unfsubst in aeq); allsimpl.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; GC; tcsp;
    boolvar; tcsp; try (complete (inversion aeq)).

  - Case "oterm".
    repeat (unfsubst in aeq); allsimpl.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl;
    try (complete (inversion aeq)).

    + boolvar; GC.

      * inversion aeq; allsimpl; subst.
        destruct bs1; allsimpl; cpx; GC.
        destruct ni1; sp.

      * inversion aeq.

    + allrw @alpha_eq_oterm_combine2; repnd; subst.
      allrw map_length.
      dands; auto.
      introv i.
      destruct b1 as [l1 t1].
      destruct b2 as [l2 t2].
      allrw in_app_iff; allrw not_over_or; repnd.
      allrw lin_flat_map; exrepnd.

      pose proof (aeq (lsubst_bterm_aux (bterm l1 t1) [(v,mk_utoken a)])
                      (lsubst_bterm_aux (bterm l2 t2) [(v,mk_utoken a)])) as h; clear aeq.
      rw <- @map_combine in h.
      rw in_map_iff in h.
      autodimp h hyp.
      { eexists; dands; eauto. }
      allsimpl.
      applydup in_combine in i; repnd.
      boolvar; tcsp; allrw @lsubst_aux_nil; auto.

      { destruct nib1.
        exists (bterm l1 t1); dands; simpl; auto.
        rw in_app_iff; sp. }

      { destruct nib2.
        exists (bterm l2 t2); dands; simpl; auto.
        rw in_app_iff; sp. }

      apply alphaeq_bterm3_if
      with (lva := v
                     :: all_vars t1
                     ++ all_vars t2
           )
        in h.

      inversion h as [? ? ? ? ? disj len1 len2 norep al]; subst; clear h.
      allrw disjoint_app_r; allrw disjoint_cons_r; allrw disjoint_app_r; repnd.

      apply (al_bterm _ _ lv); allrw disjoint_app_r; dands; try omega; eauto 3 with slow.
      apply alpha_eq_if3 in al.

      pose proof (lsubst_aux_nest_swap2 t1 [(v,mk_utoken a)] (var_ren l1 lv)) as h1.
      simpl in h1; allrw disjoint_singleton_l.
      allrw <- @sub_free_vars_is_flat_map_free_vars_range.
      allrw <- @sub_bound_vars_is_flat_map_bound_vars_range.
      repeat (rw @sub_free_vars_var_ren in h1; auto).
      repeat (rw @dom_sub_var_ren in h1; auto).
      repeat (autodimp h1 hyp); eauto with slow.

      pose proof (lsubst_aux_nest_swap2 t2 [(v,mk_utoken a)] (var_ren l2 lv)) as h2.
      simpl in h2; allrw disjoint_singleton_l.
      allrw <- @sub_free_vars_is_flat_map_free_vars_range.
      allrw <- @sub_bound_vars_is_flat_map_bound_vars_range.
      repeat (rw @sub_free_vars_var_ren in h2; auto; try omega).
      repeat (rw @dom_sub_var_ren in h2; auto; try omega).
      repeat (autodimp h2 hyp); eauto with slow.

      rw h1 in al; rw h2 in al; clear h1 h2.
      allrw @fold_subst.
      pose proof (ind1 t1 (lsubst_aux t1 (var_ren l1 lv)) l1) as h; clear ind1.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (h (lsubst_aux t2 (var_ren l2 lv)) v a) as k; clear h.
      repeat (autodimp k hyp).

      { intro j; apply get_utokens_lsubst_aux in j.
        rw @get_utokens_sub_allvars_sub in j; eauto with slow.
        rw app_nil_r in j; auto.
        destruct ni1.
        exists (bterm l1 t1); simpl; sp. }

      { intro j; apply get_utokens_lsubst_aux in j.
        rw @get_utokens_sub_allvars_sub in j; eauto with slow.
        rw app_nil_r in j; auto.
        destruct ni2.
        exists (bterm l2 t2); simpl; sp. }

      { intro j; pose proof (eqvars_bound_vars_lsubst_aux t1 (var_ren l1 lv)) as h.
        rw eqvars_prop in h; apply h in j; clear h.
        rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
        rw app_nil_r in j.
        destruct nib1.
        exists (bterm l1 t1); simpl; rw in_app_iff; sp. }

      { intro j; pose proof (eqvars_bound_vars_lsubst_aux t2 (var_ren l2 lv)) as h.
        rw eqvars_prop in h; apply h in j; clear h.
        rw @sub_bound_vars_allvars_sub in j; eauto 3 with slow.
        rw app_nil_r in j.
        destruct nib2.
        exists (bterm l2 t2); simpl; rw in_app_iff; sp. }

      { repeat unfsubst. }

      { rw @lsubst_lsubst_aux2; eauto 3 with slow; try omega.
        rw @lsubst_lsubst_aux2; eauto 3 with slow; try omega. }
Qed.

(* !!MOVE *)
Hint Resolve alpha_eq_preserves_isvalue_like : slow.

Lemma isvalue_like_pushdown_fresh {o} :
  forall v (t : @NTerm o),
    isvalue_like t
    -> isvalue_like (pushdown_fresh v t).
Proof.
  introv isv.
  allunfold @isvalue_like; repndors.
  - apply iscan_implies in isv; repndors; exrepnd; subst; simpl; sp.
  - apply isexc_implies2 in isv; exrepnd; subst; simpl; sp.
Qed.
Hint Resolve isvalue_like_pushdown_fresh : slow.

Lemma reduces_in_atmost_k_step_fresh_id {o} :
  forall (lib : @library o) v t,
    isvalue_like t
    -> !(reduces_to lib (mk_fresh v (mk_var v)) t).
Proof.
  introv isv r.
  unfold reduces_to in r; exrepnd.
  induction k; introv.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; sp.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r0; allsimpl; boolvar; ginv; sp.
Qed.

Hint Resolve computek_preserves_program reduces_to_preserves_program : slow.


Ltac decomp_progc := unfold_all_mk;
match goal with
| [ |- isprogram (oterm _ ?lbt)] => try trivial;apply isprogram_ot_if_eauto2;
    [spc;fail|  ];
      (let Hlt := fresh "XXHlt" in
       let n := fresh "XXn" in
       simpl; intros n Hlt;
       repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
      )
| [ |- isprogram_bt (bterm [] ?lbt)] => apply implies_isprogram_bt0
 end .

(*it loops.. use decomp_progc instead
Ltac decomp_progc2 :=unfold mk_apply;
match goal with
| [ |- isprogram (oterm _ ?lbt)] => try trivial;apply isprogram_ot_if_eauto2;
    [spc |
      (let Hlt := fresh "XXHlt" in
       let n := fresh "XXn" in
       simpl; intros n Hlt;
       repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
      )]
| [ |- isprogram_bt (bterm [] ?lbt)] => apply implies_isprogram_bt0
 end .
*)

Lemma computes_in_max_k_steps_refl {p} :
  forall lib k v,
   @isvalue p v -> computes_to_value_in_max_k_steps lib k v v.
Proof.
 intros. unfolds_base. dands;sp.
 apply compute_at_most_k_steps_if_value;sp.
Qed.

Ltac repeatn n tac:=
match n with
| 0 => idtac
| S ?n => tac; repeatn n tac
end.

Lemma computes_to_value_in_max_k_steps_0 {p} :
  forall lib (a b : @NTerm p),
    computes_to_value_in_max_k_steps lib 0 a b <=> (a = b # isvalue b).
Proof.
  unfold computes_to_value_in_max_k_steps, reduces_in_atmost_k_steps.
  simpl; introv; split; intro k; repnd.
  inversion k0; auto.
  subst; dands; auto.
Qed.

Lemma computes_to_value_in_max_k_steps_S {p} :
  forall lib t v k,
    computes_to_value_in_max_k_steps lib (S k) t v
    <=> {u : @NTerm p
        & compute_step lib t = csuccess u
        # computes_to_value_in_max_k_steps lib k u v}.
Proof.
  introv; split; intro comp.

  - allunfold @computes_to_value_in_max_k_steps; repnd.
    apply reduces_in_atmost_k_steps_S in comp0; exrepnd.
    exists u; sp.

  - exrepnd.
    allunfold @computes_to_value_in_max_k_steps; repnd; dands; auto.
    rw @reduces_in_atmost_k_steps_S.
    exists u; sp.
Qed.

Lemma computes_to_value_in_max_k_steps_isvalue_like {o} :
  forall lib k (t u : @NTerm o),
    computes_to_value_in_max_k_steps lib k t u
    -> isvalue_like t
    -> t = u.
Proof.
  induction k; introv comp isv.
  - allrw @computes_to_value_in_max_k_steps_0; sp.
  - allrw @computes_to_value_in_max_k_steps_S; exrepnd.
    unfold isvalue_like in isv; repndors.
    + apply iscan_implies in isv; repndors; exrepnd; subst;
      csunf comp1; allsimpl; ginv;
      apply IHk in comp0; eauto with slow.
    + apply isexc_implies2 in isv; exrepnd; subst.
      csunf comp1; allsimpl; ginv.
      apply IHk in comp0; eauto with slow.
Qed.

Lemma compute_at_most_k_steps_S2 {o} :
  forall (lib : library) (n : nat) (t : @NTerm o),
    compute_at_most_k_steps lib (S n) t
    = match compute_step lib t with
        | csuccess u => compute_at_most_k_steps lib n u
        | cfailure m u => cfailure m u
      end.
Proof.
  induction n; introv; allsimpl.
  - remember (compute_step lib t) as c; destruct c; auto.
  - rw IHn; remember (compute_step lib t) as c; destruct c; auto.
Qed.

Lemma co_wf_pk2can {o} :
  forall (pk : @param_kind o), co_wf CompOpEq (pk2can pk) [] = true.
Proof.
  introv.
  unfold co_wf.
  allrw @get_param_from_cop_pk2can; auto.
Qed.
Hint Rewrite @co_wf_pk2can : slow.

(* move to computation.v*)
Lemma compute_max_steps_eauto {p} :
  forall lib k t tv,
  @computes_to_value_in_max_k_steps p lib k t tv -> isvalue tv.
Proof.
  introv Hc.
  repnud Hc.
  trivial.
Qed.

Lemma compute_max_steps_eauto2 {p} : forall t,
  @isvalue p t -> isprogram t.
Proof.
  introv Hc.
  inverts Hc.
  trivial.
Qed.

(* move to computation.v*)
Lemma no_change_after_value3 {p} :
   forall lib t k1 v,
          @computes_to_value_in_max_k_steps p lib k1 t v
          ->  (isvalue v)
          ->  forall k2, k1<=k2 -> computes_to_value_in_max_k_steps lib k2 t v.
Proof.
  unfold computes_to_value_in_max_k_steps. intros.
  repnd.
  dands;sp.
  eapply no_change_after_value2; eauto.
Qed.

Lemma compute_at_most_k_steps_isvalue_like {o} :
  forall lib k (t : @NTerm o),
    isvalue_like t
    -> compute_at_most_k_steps lib k t = csuccess t.
Proof.
  induction k; simpl; introv isv; auto.
  rw IHk; auto.
  apply compute_step_value_like; auto.
Qed.

Lemma computes_atmost_ksteps_prinarg {p} :
  forall lib op ntp lbt k ntpc,
  compute_at_most_k_steps lib k ntp = @csuccess p ntpc
  -> {j : nat $ compute_at_most_k_steps lib j (oterm (NCan op) ((bterm [] ntp)::lbt))
                = csuccess (oterm (NCan op) ((bterm [] ntpc)::lbt))
                    # j<=k}.
Proof.
  induction k as [| k Hind]; introv Hck;[exists 0; allsimpl|];spc;[].
  destruct ntp as [| | ntpo  ntplbt];
    [rw @compute_at_most_steps_var in Hck; spc; fail| |].

  { rw @compute_at_most_k_steps_isvalue_like in Hck; eauto 3 with slow; ginv.
    exists 0; dands; auto; try omega. }

  allsimpl.
  remember (compute_at_most_k_steps lib k (oterm ntpo ntplbt)) as ck.
  destruct ck as [csk | cf]; spc;[].
  dimp (Hind csk); exrepnd; spc;[]. clear Hind.
  destruct csk as [sckv| f | csko csklbt]; [inverts Hck; fail| |].

  { rw @compute_step_value_like in Hck; eauto 3 with slow; ginv.
    eexists; dands; eauto. }

  dopid csko as [cskoc| cskon | cskexc | cskabs] Case.
  - Case "Can".
    simpl in Hck. inverts Hck. exists j; sp.
  - Case "NCan".
    exists (S j). dands;[|omega]. simpl. rw hyp1. simpl in Hck. simpl.
    rw @compute_step_ncan_ncan.
    rw Hck;sp.
  - Case "Exc".
    rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
    exists j; sp.
  - Case "Abs".
    exists (S j).
    dands;[|omega]. simpl. rw hyp1. simpl in Hck. simpl.
    rw @compute_step_ncan_abs.
    csunf Hck; allsimpl.
    rw Hck;sp.
Qed.

Lemma reduces_to_prinarg {p} : forall lib op ntp ntpc lbt,
  @reduces_to p lib ntp  ntpc
  -> reduces_to lib (oterm (NCan op) ((bterm [] ntp)::lbt))
                (oterm (NCan op) ((bterm [] ntpc)::lbt)).
Proof.
  introv Hc. repnud Hc. exrepnd.
  eapply (computes_atmost_ksteps_prinarg) in Hc0.
  exrepnd.
  exists j.
  eauto.
Qed.

Lemma compute_at_most_k_steps_step {p} :
  forall lib t m a, compute_at_most_k_steps lib m t = csuccess a
    -> m >0
    -> {tc : @NTerm p $ compute_step lib t = csuccess tc}.
Proof.
  induction m as [| m Hind];introv Hc Hlt;[omega|].
  allsimpl. remember (compute_at_most_k_steps lib m t) as ck.
  destruct ck; spc.
  destruct m; allsimpl; [ inverts Heqck ; exists a; spc |].
  dimp (Hind n); spc; omega.
Qed.

Lemma if_computes_to_value_steps_arith {p} :
  forall lib a k lbt v,
    computes_to_value_in_max_k_steps lib k (oterm (NCan (NArithOp a)) lbt) v
    -> {n1,n2 : NTerm $ lbt = [bterm [] n1, bterm [] n2] #
          {nv1,nv2 : Z $ v = mk_integer ((get_arith_op a) nv1 nv2) #
            { k1,k2 : nat $ k1+k2+1 <=k
                # computes_to_value_in_max_k_steps lib k1 n1 (mk_integer nv1)
                # computes_to_value_in_max_k_steps lib k2 n2 (mk_integer nv2)
                # compute_at_most_k_steps lib (k1+k2) (oterm (NCan (NArithOp a)) lbt)
                   = csuccess (oterm (NCan (NArithOp a))
                        [bterm [] (mk_integer nv1),
                          bterm [] (@mk_integer p nv2)])
                  }}}.
Proof.
  induction k as [| k Hind]; introv Hcv.

  { allrw @computes_to_value_in_max_k_steps_0; repnd; subst.
    allapply @isvalue_ncan; tcsp. }

  repnud Hcv.
  unfold reduces_in_atmost_k_steps in Hcv0.
  rw @compute_at_most_k_steps_eq_f in Hcv0.
  simpl in Hcv0.  rename Hcv0 into Hcomp.
  dlist lbt SSCase as [| arg1]; invertsn Hcomp.
  SSCase "conscase".
  destruct arg1 as [arg1vs arg1nt];
  dlist arg1vs SSSCase as [|arg1v1]; [|inverts Hcomp].
  SSSCase "nilcase".
  destruct arg1nt as [v89|f| arg1o arg1bts];[inverts Hcomp| |];[|].

  { csunf Hcomp; allsimpl; ginv. }

  dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase; try (complete ginv).

  - SSSSCase "Can".
    destruct lbt as [| bt2 lbt].
    { csunf Hcomp; allsimpl; boolvar; ginv; dcwf h. }
    destruct bt2 as [lv2 nt2].
    destruct lv2; destruct nt2 as [?|?| arg2o arg2bts];
    try (complete (csunf Hcomp; allsimpl; boolvar; ginv; dcwf h));[].

    dopid arg2o as [arg2c | arg2nc | arg2exc | arg2abs] SSSSSCase; try (complete ginv).

    + SSSSSCase "Can".
      csunf Hcomp; allsimpl; boolvar; allsimpl; ginv; dcwf h;[].
      match goal with
        | [ H : context[compute_step_arith ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_arith a1 a2 a3 a4 a5 a6 a7) as c
      end; destruct c; ginv; symmetry in Heqc.
      apply compute_step_arithop_success_can_can in Heqc; exrepnd; subst.
      allapply @get_param_from_cop_pki; subst; fold_terms.
      exists (@mk_integer p n1) (@mk_integer p n2); dands; auto.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      rw @compute_on_value in Hcomp; eauto 3 with slow; ginv.
      exists n1 n2; dands; auto.
      exists 0 0; dands; auto; try omega;
      apply computes_in_max_k_steps_refl; eauto with slow.

    + SSSSSCase "NCan".
      rw @compute_step_narithop_ncan2 in Hcomp; boolvar; tcsp; ginv; dcwf h;[].
      remember (compute_step lib (oterm (NCan arg2nc) arg2bts)) as c.
      symmetry in Heqc; destruct c; allsimpl; ginv.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      make_and Hcomp Hcv.
      apply Hind in HcompHcv; exrepnd; subst; ginv; clear Hind.
      eexists; eexists; dands; eauto.
      eexists; eexists; dands; eauto.
      applydup @computes_to_value_in_max_k_steps_isvalue_like in HcompHcv4; eauto with slow.
      inversion HcompHcv0; subst; fold_terms; GC.
      exists k1 (S k2); dands; try omega; auto.
      * rw @computes_to_value_in_max_k_steps_S.
        eexists; dands; eauto.
      * rw Nat.add_succ_r.
        rw @compute_at_most_k_steps_S2.
        unfold mk_integer, nobnd.
        rw @compute_step_narithop_ncan2; simpl; boolvar; tcsp.
        rw Heqc; auto.

    + SSSSSCase "Exc".
      csunf Hcomp; allsimpl; boolvar; ginv; dcwf h;[].
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      rw @compute_at_most_k_steps_exception in Hcomp; inversion Hcomp; subst; GC.
      allapply @isvalue_exc; sp.

    + SSSSSCase "Abs".
      rw @compute_step_narithop_abs2 in Hcomp; boolvar; tcsp; ginv; dcwf h;[].
      remember (compute_step_lib lib arg2abs arg2bts) as c.
      symmetry in Heqc; destruct c; allsimpl; ginv.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      make_and Hcomp Hcv.
      apply Hind in HcompHcv; exrepnd; subst; ginv; clear Hind.
      eexists; eexists; dands; eauto.
      eexists; eexists; dands; eauto.
      applydup @computes_to_value_in_max_k_steps_isvalue_like in HcompHcv4; eauto with slow.
      inversion HcompHcv0; subst; fold_terms; GC.
      exists k1 (S k2); dands; try omega; auto.
      * rw @computes_to_value_in_max_k_steps_S.
        eexists; dands; eauto.
      * rw Nat.add_succ_r.
        rw @compute_at_most_k_steps_S2.
        unfold mk_integer, nobnd.
        rw @compute_step_narithop_abs2; simpl; boolvar; tcsp.
        rw Heqc; auto.

  - SSSSCase "NCan".
    rw @compute_step_narithop_ncan1 in Hcomp.
    remember (compute_step lib (oterm (NCan arg1nc) arg1bts)) as c.
    symmetry in Heqc; destruct c; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    make_and Hcomp Hcv.
    apply Hind in HcompHcv; exrepnd; subst; ginv; clear Hind.
    eexists; eexists; dands; eauto.
    eexists; eexists; dands; eauto.
    exists (S k1) k2; dands; try omega; auto.
    * rw @computes_to_value_in_max_k_steps_S.
      eexists; dands; eauto.
    * rw plus_Sn_m.
      rw @compute_at_most_k_steps_S2.
      unfold mk_integer, nobnd.
      rw @compute_step_narithop_ncan1; simpl; boolvar; tcsp.
      rw Heqc; auto.

  - SSSSCase "Exc".
    csunf Hcomp; allsimpl; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    rw @compute_at_most_k_steps_exception in Hcomp; inversion Hcomp; subst; GC.
    allapply @isvalue_exc; sp.

  - SSSSCase "Abs".
    rw @compute_step_narithop_abs1 in Hcomp.
    remember (compute_step_lib lib arg1abs arg1bts) as c.
    symmetry in Heqc; destruct c; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    make_and Hcomp Hcv.
    apply Hind in HcompHcv; exrepnd; subst; ginv; clear Hind.
    eexists; eexists; dands; eauto.
    eexists; eexists; dands; eauto.
    exists (S k1) k2; dands; try omega; auto.
    * rw @computes_to_value_in_max_k_steps_S.
      eexists; dands; eauto.
    * rw plus_Sn_m.
      rw @compute_at_most_k_steps_S2.
      unfold mk_integer, nobnd.
      rw @compute_step_narithop_abs1; simpl; boolvar; tcsp.
      rw Heqc; auto.
Qed.

Lemma if_computes_to_value_steps_ncomp {p} :
  forall lib a k lbt v,
    computes_to_value_in_max_k_steps lib k (oterm (NCan (NCompOp a)) lbt) v
    -> {n1,n2,n3,n4 : @NTerm p $ lbt = [bterm [] n1, bterm [] n2, bterm [] n3, bterm [] n4] #
        { c1,c2 : CanonicalOp $ let tc:= (oterm (NCan (NCompOp a))
                        [bterm [] (oterm (Can c1) []),
                          bterm [] (oterm (Can c2) []),
                          bterm [] n3,
                          bterm [] n4]) in
            { k1,k2 : nat $ k1+k2+1 <=k
                # computes_to_value_in_max_k_steps lib k1 n1 (oterm (Can c1) [])
                # computes_to_value_in_max_k_steps lib k2 n2 (oterm (Can c2) [])
                # compute_at_most_k_steps lib (k1+k2) (oterm (NCan (NCompOp a)) lbt)
                   = csuccess tc
                  }}}.
Proof.
  induction k as [| k Hind]; introv Hcv.

  { allrw @computes_to_value_in_max_k_steps_0; repnd; subst.
    allapply @isvalue_ncan; tcsp. }

  repnud Hcv.
  unfold reduces_in_atmost_k_steps in Hcv0.
  rw @compute_at_most_k_steps_eq_f in Hcv0.
  simpl in Hcv0.
  rename Hcv0 into Hcomp.
  dlist lbt SSCase as [| arg1]; invertsn Hcomp.
  SSCase "conscase".
  destruct arg1 as [arg1vs arg1nt];
  dlist arg1vs SSSCase as [|arg1v1]; [|inverts Hcomp].
  SSSCase "nilcase".
  destruct arg1nt as [v89|f| arg1o arg1bts];[inverts Hcomp| |];[|].

  { csunf Hcomp; allsimpl; ginv. }

  dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase.

  - SSSSCase "Can".
    destruct lbt as [| bt2 lbt].
    { csunf Hcomp; allsimpl; boolvar; ginv; dcwf h. }
    destruct bt2 as [lv2 nt2];[].
    destruct lv2; destruct nt2 as [?|?| arg2o arg2bts];
    try (complete (csunf Hcomp; allsimpl; boolvar; ginv; dcwf h));[].
    dopid arg2o as [arg2c | arg2nc | arg2exc | arg2abs] SSSSSCase; try (complete ginv).

    + SSSSSCase "Can".
      csunf Hcomp; allsimpl; boolvar; tcsp; ginv; dcwf h;[].
      match goal with
        | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7) as c
      end; destruct c; ginv; symmetry in Heqc.

      apply compute_step_compop_success_can_can in Heqc; exrepnd; subst;
      repndors; exrepnd; subst;
      allrw @get_param_from_cop_some; subst; allsimpl;
      unfold nobnd; allsimpl; GC;
      eexists; eexists; eexists; eexists; dands; eauto.
      * exists (@Nint p n1) (@Nint p n2) 0 0; dands; try omega; auto; fold_terms.
        { rw @computes_to_value_in_max_k_steps_0; dands; eauto 3 with slow. }
        { rw @computes_to_value_in_max_k_steps_0; dands; eauto 3 with slow. }
      * exists (pk2can pk1) (pk2can pk2) 0 0; dands; try omega; auto; fold_terms;
        allrw <- @pk2term_eq.
        { rw @computes_to_value_in_max_k_steps_0; dands; eauto 3 with slow. }
        { rw @computes_to_value_in_max_k_steps_0; dands; eauto 3 with slow. }

    + SSSSSCase "NCan".
      rw @compute_step_ncompop_ncan2 in Hcomp; boolvar; tcsp; ginv; dcwf h;[].
      remember (compute_step lib (oterm (NCan arg2nc) arg2bts)) as c.
      symmetry in Heqc; destruct c; ginv.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      make_and Hcomp Hcv.
      apply Hind in HcompHcv; clear Hind.
      exrepnd; ginv.
      eexists; eexists; eexists; eexists; dands; eauto.
      applydup @computes_to_value_in_max_k_steps_isvalue_like in HcompHcv3; eauto with slow.
      inversion HcompHcv0; subst; fold_terms; GC.
      exists c1 c2 k1 (S k2); dands; try omega; auto.
      * rw @computes_to_value_in_max_k_steps_S.
        eexists; dands; eauto.
      * rw Nat.add_succ_r.
        rw @compute_at_most_k_steps_S2.
        unfold nobnd.
        rw @compute_step_ncompop_ncan2; simpl; boolvar; tcsp; dcwf h.
        rw Heqc; auto.

    + SSSSSCase "Exc".
      csunf Hcomp; allsimpl; ginv; dcwf h;[].
      boolvar; tcsp; ginv.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      rw @compute_at_most_k_steps_exception in Hcomp; inversion Hcomp; subst; GC.
      allapply @isvalue_exc; sp.

    + SSSSSCase "Abs".
      rw @compute_step_ncompop_abs2 in Hcomp; boolvar; tcsp; ginv; dcwf h;[].
      remember (compute_step_lib lib arg2abs arg2bts) as c.
      symmetry in Heqc; destruct c; ginv.
      rw <- @compute_at_most_k_steps_eq_f in Hcomp.
      make_and Hcomp Hcv.
      apply Hind in HcompHcv; clear Hind.
      exrepnd; ginv.
      eexists; eexists; eexists; eexists; dands; eauto.
      applydup @computes_to_value_in_max_k_steps_isvalue_like in HcompHcv3; eauto with slow.
      inversion HcompHcv0; subst; fold_terms; GC.
      exists c1 c2 k1 (S k2); dands; try omega; auto.
      * rw @computes_to_value_in_max_k_steps_S.
        eexists; dands; eauto.
      * rw Nat.add_succ_r.
        rw @compute_at_most_k_steps_S2.
        unfold nobnd.
        rw @compute_step_ncompop_abs2; simpl; boolvar; tcsp; dcwf h;[].
        rw Heqc; auto.

  - SSSSCase "NCan".
    rw @compute_step_ncompop_ncan1 in Hcomp; boolvar; tcsp; ginv.
    remember (compute_step lib (oterm (NCan arg1nc) arg1bts)) as c.
    symmetry in Heqc; destruct c; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    make_and Hcomp Hcv.
    apply Hind in HcompHcv; clear Hind.
    exrepnd; ginv.
    eexists; eexists; eexists; eexists; dands; eauto.
    exists c1 c2 (S k1) k2; dands; try omega; auto.
    * rw @computes_to_value_in_max_k_steps_S.
      eexists; dands; eauto.
    * rw Nat.add_succ_l.
      rw @compute_at_most_k_steps_S2.
      unfold nobnd.
      rw @compute_step_ncompop_ncan1; simpl; boolvar; tcsp.
      rw Heqc; auto.

  - SSSSCase "Exc".
    csunf Hcomp; allsimpl; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    rw @compute_at_most_k_steps_exception in Hcomp; inversion Hcomp; subst; GC.
    allapply @isvalue_exc; sp.

  - SSSSCase "Abs".
    rw @compute_step_ncompop_abs1 in Hcomp; boolvar; tcsp; ginv.
    remember (compute_step_lib lib arg1abs arg1bts) as c.
    symmetry in Heqc; destruct c; ginv.
    rw <- @compute_at_most_k_steps_eq_f in Hcomp.
    make_and Hcomp Hcv.
    apply Hind in HcompHcv; clear Hind.
    exrepnd; ginv.
    eexists; eexists; eexists; eexists; dands; eauto.
    exists c1 c2 (S k1) k2; dands; try omega; auto.
    * rw @computes_to_value_in_max_k_steps_S.
      eexists; dands; eauto.
    * rw Nat.add_succ_l.
      rw @compute_at_most_k_steps_S2.
      unfold nobnd.
      rw @compute_step_ncompop_abs1; simpl; boolvar; tcsp.
      rw Heqc; auto.
Qed.

Lemma computes_steps_prinargs_arith {p} :
  forall lib a ntp1 ntp2 lbt k1 k2 ntpc1 ntpc2,
  compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
  -> isinteger ntpc1
  -> compute_at_most_k_steps lib k2 ntp2 = @csuccess p ntpc2
  -> {j : nat $ compute_at_most_k_steps lib j (oterm (NCan (NArithOp a)) 
                        ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                = csuccess (oterm (NCan (NArithOp a)) 
                        ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt))) 
            # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind];  introv H1c H1v H2c.
  - inverts H2c.
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end.
    exrepnd. exists j. dands; spc. omega.
  - duplicate H1v. inverts H1v as Hisp1.
    rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [|?| ntp2o  ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail| |].

    { rw @compute_at_most_k_steps_isvalue_like in Hck; eauto 3 with slow.
      ginv.
      pose proof (Hind (mk_integer x) (sterm n)) as h; clear Hind.
      repeat (autodimp h hyp).
      { rw @compute_at_most_k_steps_isvalue_like; eauto 3 with slow. }
      exrepnd.
      eexists; dands; eauto; try omega. }

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v0 eq_refl) as XX. clear H1v0. exrepnd.
    destruct csk as [sckv|?| csko csklbt]; [inverts Hck; fail| |].

    { csunf Hck; allsimpl; ginv.
      eexists; dands; eauto; try omega. }

    dopid csko as [cskoc| cskon | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j). dands;[|omega]. simpl. rw XX1.
      allunfold @mk_integer.
      rw @compute_step_narithop_ncan2; rw Hck.
      dcwf h.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      exists (S j). dands;[|omega]. simpl. rw XX1. simpl. simpl in Hck. simpl.
      allunfold @mk_integer.
      rw @compute_step_narithop_abs2; boolvar; allsimpl; tcsp.
      csunf Hck; allsimpl.
      rw Hck;sp.
Qed.

(* proof is exactly same as computes_steps_prinargs_arith *)
Lemma computes_steps_prinargs_comp {p} :
  forall lib a ntp1 ntp2 lbt k1 k2 ntpc1 ntpc2,
  compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
  -> iswfpk a ntpc1
  -> compute_at_most_k_steps lib k2 ntp2 = @csuccess p ntpc2
  -> {j : nat $ compute_at_most_k_steps lib j (oterm (NCan (NCompOp a)) 
                        ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                = csuccess (oterm (NCan (NCompOp a)) 
                        ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt))) 
            # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind];  introv H1c H1v H2c.
  - inverts H2c. 
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end. 
    exrepnd. exists j. dands; spc. omega.
  - rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [|?| ntp2o  ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail| |].

    { rw @compute_at_most_k_steps_isvalue_like in Hck; eauto 3 with slow.
      ginv.
      pose proof (Hind ntpc1 (sterm n)) as h; clear Hind.
      repeat (autodimp h hyp).
      { rw @compute_at_most_k_steps_isvalue_like; eauto 3 with slow. }
      exrepnd.
      eexists; dands; eauto; try omega. }

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v eq_refl) as XX; exrepnd.
    destruct csk as [sckv|?| csko csklbt]; [inverts Hck; fail| |].

    { csunf Hck; allsimpl; ginv.
      eexists; dands; eauto; try omega. }

    dopid csko as [cskoc| cskon | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j). dands;[|omega]. simpl. rw XX1.
      destruct a; allsimpl.
      * unfold isinteger in H1v; exrepnd; subst; allunfold @mk_integer.
        rw @compute_step_ncompop_ncan2;rw Hck.
        dcwf h;tcsp.
      * unfold ispk in H1v; exrepnd; subst; allrw @pk2term_eq.
        rw @compute_step_ncompop_ncan2;rw Hck.
        autorewrite with slow; tcsp.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      exists (S j). dands;[|omega]. simpl. rw XX1.
      csunf Hck; allsimpl.
      destruct a; allsimpl.
      * unfold isinteger in H1v; exrepnd; subst; allunfold @mk_integer.
        rw @compute_step_ncompop_abs2; allsimpl; rw Hck; auto.
      * unfold ispk in H1v; exrepnd; subst; allrw @pk2term_eq.
        rw @compute_step_ncompop_abs2;rw Hck.
        autorewrite with slow; tcsp.
Qed.

Lemma reduce_to_prinargs_arith {p} :
  forall lib a ntp1 ntp2 lbt ntpv1 ntpc2,
    computes_to_value lib ntp1 ntpv1
    -> isinteger ntpv1
    -> @reduces_to p lib ntp2  ntpc2
    -> reduces_to lib (oterm (NCan (NArithOp a))
                             ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                  (oterm (NCan (NArithOp a))
                         ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv H1c isi H2c.
  repnud H2c. repnud H1c.  repnud H1c0. exrepnd.
  eapply @computes_steps_prinargs_arith with (lbt:=lbt) 
      (a:=a) (ntpc1:= ntpv1) (ntpc2:= ntpc2) in H1c1; exrepnd; eauto.
  unfolds_base; exists j; eauto.
Qed.

(* %\noindent% The following lemma is also a consequence of the fact
    that the first argument is always principal

*)

Lemma reduce_to_prinargs_comp {p} :
  forall lib a ntp1 ntp2 lbt ntpv1 ntpc2,
    computes_to_value lib ntp1 ntpv1
    -> iswfpk a ntpv1
    -> @reduces_to p lib ntp2 ntpc2
    -> reduces_to lib (oterm (NCan (NCompOp a))
                             ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                  (oterm (NCan (NCompOp a))
                         ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv H1c isw H2c.
  repnud H2c. repnud H1c.  repnud H1c0. exrepnd.
  eapply @computes_steps_prinargs_comp with (lbt:=lbt) 
      (a:=a) (ntpc1:= ntpv1) (ntpc2:= ntpc2) in H1c1; exrepnd; eauto.
  unfolds_base; exists j; eauto.
Qed.

Ltac decomp_progh :=allunfold mk_apply;
match goal with
| [ H1 : (computes_to_value ?lib ?tl _), H2 : (isprogram  ?t1) |- _ ] =>
    let Hf := fresh H1 H2 "pr" in
    pose proof (preserve_program lib _ _ H1 H2) as Hf; hide_hyp  H1
| [ H1 : (compute_at_most_k_steps ?lib _ ?tl = csuccess _), H2 : (isprogram  ?t1) |- _ ] =>
    let Hf := fresh H1 H2 "pr" in
    pose proof (computek_preserves_program lib _ _ _ H1 H2) as Hf; hide_hyp  H1
| [ H : isprogram (oterm _ _) |- _ ] => let Hf := fresh H "bts" in 
     pose proof (isprogram_ot_implies_eauto2 _ _ H) as Hf; simpl in Hf;
     hide_hyp H
| [ H: (forall _:nat, (_< ?m) -> isprogram_bt _)  |- _ ] => 
    fail_if_not_number m;
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps); clear H

| [ H : isprogram_bt (bterm [] ?lbt) |- _ ] => apply isprogram_bt_nobnd in H
end.

Ltac make_reduces_to Hyp :=
  let Hf := fresh Hyp "rd" in
  let T:= type of Hyp in
  match T with
      compute_at_most_k_steps ?lib ?m ?tl = csuccess ?tc =>
      assert (reduces_to lib tl tc) as Hf by (exists m; trivial)
  end.

Ltac reduces_to_step Hyp :=
  let T:= type of Hyp in
  match T with
      reduces_to ?lib _ ?tr =>
      let TRS := eval simpl in
      (compute_step lib tr) in
          match TRS with
            | csuccess ?trs => apply reduces_to_if_split1 with (v:=trs) in Hyp;[|simpl;auto;fail]
            | _ => idtac "RHS did not compute to csuccess _ in 1 step, It computed to: " TRS ;fail
          end
  end.

Ltac decomp_progc2 := unfold_all_mk; let Hlt := fresh "Hltpc" in
match goal with
| [ |- isprogram (oterm _ ?lbt)] => try trivial;apply isprogram_ot_if_eauto2;repeat( simpl_list);[spc|]
| [ |- forall _, _ < _ -> isprogram_bt _ _ ] => introv Hlt;repeat(simpl_list);repeat(dlt Hlt)
| [ |- context[map num_bvars (map  (fun _:_ => lsubst_bterm_aux _ _) _ )]] => try rewrite map_num_bvars_bterms
| [ |- isprogram_bt (bterm [] ?lbt)] => apply implies_isprogram_bt0
 end .

Ltac decomp_progh2 :=allunfold mk_apply;
match goal with 
| [ H1 : (computes_to_value _ ?tl _), H2 : (isprogram  ?t1) |- _ ] =>
    let Hf := fresh H1 H2 "pr" in 
    pose proof (preserve_program _ _ _ H1 H2) as Hf; hide_hyp  H1
| [ H1 : (compute_at_most_k_steps _ _ ?tl = csuccess _), H2 : (isprogram  ?t1) |- _ ] =>
    let Hf := fresh H1 H2 "pr" in 
    pose proof (computek_preserves_program _ _ _ _ H1 H2) as Hf; hide_hyp  H1
| [ H : isprogram (oterm _ _) |- _ ] => let Hf := fresh H "bts" in 
     pose proof (isprogram_ot_implies_eauto2 _ _ H) as Hf; simpl in Hf;
     allrw map_length;
     hide_hyp H
| [ H: (forall _:nat, (_< ?m) -> isprogram_bt _)  |- _ ] => 
    (let XXX:= fresh H "0bt" in
      assert (0<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "1bt" in
      assert (1<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "2bt" in
      assert (2<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps);
    try (let XXX:= fresh H "3bt" in
      assert (3<m) as XXX by omega; apply H in XXX; 
      unfold selectbt in XXX; simphyps); clear H

| [ H : isprogram_bt (bterm [] ?lbt) |- _ ] => apply isprogram_bt_nobnd in H
end.

(** exclude the trivial nop step when the input was
    already canonical.  This notion is what Crary's right arrow(|->) means
    See Proposition 4.2. He says that for canonical terms
    are not allowed at the LHS of this relation*)
Inductive computes_in_1step {p} : @library p -> @NTerm p -> @NTerm p -> [univ] :=
| c1step_nc :
    forall lib (no: NonCanonicalOp) (lbt : list BTerm) (tc : NTerm),
      compute_step lib (oterm (NCan no) lbt) = csuccess tc
      -> computes_in_1step lib (oterm (NCan no) lbt) tc
| c1step_ab :
    forall lib (x: opabs) (lbt : list BTerm) (tc : NTerm),
      compute_step lib (oterm (Abs x) lbt) = csuccess tc
      -> computes_in_1step lib (oterm (Abs x) lbt) tc.


Lemma computes_in_1step_prinarg {p} :
  forall lib op ntp ntpc lbt,
  @computes_in_1step p lib ntp ntpc
  -> computes_in_1step lib (oterm (NCan op) ((bterm [] ntp)::lbt))
                (oterm (NCan op) ((bterm [] ntpc)::lbt)).
Proof.
  introv Hc.
  invertsn Hc; constructor; simpl in Hc; csunf; simpl; rw Hc; sp.
Qed.

Theorem compute_1step_alpha {p} :
  forall lib (t1 t2 t1' : @NTerm p),
    nt_wf t1
    -> alpha_eq t1 t2
    -> computes_in_1step lib t1 t1'
    -> { t2':@NTerm p & computes_in_1step lib t2 t2' # alpha_eq t1' t2'}.
Proof.
  introv wf Hal Hc.
  dup Hal as aeq.
  invertsn Hc; apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst;
  eapply compute_step_alpha in Hal; eauto; exrepnd;
  eexists; dands; try constructor; eauto.
Qed.

Lemma computes_in_1step_program {p} : forall lib t1 t2,
  @computes_in_1step p lib t1 t2
  -> isprogram t1
  -> isprogram t2.
Proof.
  introv Hc.
  invertsn Hc; introv Hp; eauto with slow.
Qed.

Definition computes_step_to_error {p} lib (t : @NTerm p) :=
  match compute_step lib t with
    | csuccess _ => False
    | cfailure _ _ => True
  end.

Definition computes_in_1step_alpha {p} lib (t1 t2 : @NTerm p):=
  {t2a : NTerm $ computes_in_1step lib t1 t2a # alpha_eq t2 t2a}.


Hint Resolve computes_in_1step_program : slow.


Lemma computes_in_1step_alpha2 {o} :
  forall lib (e1 e2 e1a e2a : @NTerm o),
    nt_wf e1
    -> computes_in_1step_alpha lib e1 e2
    -> alpha_eq e1 e1a
    -> alpha_eq e2 e2a
    -> computes_in_1step_alpha lib e1a e2a.
Proof.
  introv wf Hc H1a H2a.
  invertsn Hc.
  repnd.
  apply (compute_1step_alpha _ _ _ _ wf H1a) in Hc0.
  exrepnd.
  unfolds_base.
  eexists; eauto with slow.
Qed.



Ltac destruct_cstep Hyp cs :=
  match type of Hyp with
      context[ compute_step ?lib ?c] =>
      remember (compute_step lib c) as cs;
        let css := fresh cs "s" in
        let csf := fresh cs "f" in
        destruct cs as [css | csf]
  end.


Ltac fold_compute_step t Hyp:=
  let XX := fresh "XX" in
  let tc := eval simpl in
  (compute_step t) in
      assert(tc=compute_step t) as XX by refl; rewrite XX in Hyp; clear XX.

Lemma compute_1step_eq {p} : forall lib t1 t2 t3,
  @computes_in_1step p lib t1 t2
  -> computes_in_1step lib t1 t3
  -> t2=t3.
Proof.
  introv H1c H2c.
  invertsn H1c; invertsn H2c; congruence.
Qed.


Lemma compute_1step_alpha2 {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    nt_wf a1
    -> alpha_eq a1 a2
    -> computes_in_1step lib a1 b1
    -> computes_in_1step lib a2 b2
    -> alpha_eq b1 b2.
Proof.
  introv wf Hal H1c H2c.
  eapply compute_1step_alpha in Hal; eauto.
  exrepnd.
  assert (t2'=b2);[| congruence].
  eapply compute_1step_eq; eauto.
Qed.

Inductive computes_in_kstep_alpha {p} : @library p -> nat -> @NTerm p -> @NTerm p -> [univ]:=
|ckainit : forall lib t1 t2,  alpha_eq t1 t2 -> computes_in_kstep_alpha lib 0 t1 t2
|ckacons : forall lib k t1 t2 t3 ,
                        computes_in_1step_alpha lib t1 t2
                        -> computes_in_kstep_alpha lib k t2 t3
                        -> computes_in_kstep_alpha lib (S k) t1 t3.

Inductive computes_in_kstep {p} : @library p -> nat -> @NTerm p -> @NTerm p -> [univ]:=
|ckinit : forall lib t , computes_in_kstep lib 0 t t
|ckcons : forall lib k t1 t2 t3 ,
                        computes_in_1step lib  t1 t2
                        -> computes_in_kstep lib k t2 t3
                        -> computes_in_kstep lib (S k) t1 t3.

Definition computes_to_alpha_value {p} lib (t1 t2 : @NTerm p) :=
  {t2a : NTerm $ computes_to_value lib t1 t2a # alpha_eq t2a t2}.


Lemma noncan_tricot {p} : forall lib no lbt,
  isprogram (oterm (NCan no) lbt)
  -> { v : @NTerm p
       $ compute_step lib (oterm (NCan no) lbt) = csuccess v
       # isprogram v
       # (isvalue v [+] isnoncan v [+] isexc v [+] isabs v [+] isseq v) }
     [+] computes_step_to_error lib (oterm (NCan no) lbt).
Proof.
  introv Hpr.
  unfold computes_step_to_error.
  remember (compute_step lib (oterm (NCan no) lbt)) as cs.
  destruct cs as [csk | cnk]; auto.

  left.
  eexists; dands; eauto with slow.
  apply isprogram_noncan; eauto with slow.
Qed.

Lemma noncan_tricot_abs {p} :
  forall (lib : @library p) ab lbt,
  isprogram (oterm (Abs ab) lbt)
  -> { v : @NTerm p
       $ compute_step lib (oterm (Abs ab) lbt) = csuccess v
       # isprogram v
       # (isvalue v [+] isnoncan v [+] isexc v [+] isabs v [+] isseq v) }
     [+] computes_step_to_error lib (oterm (Abs ab) lbt).
Proof.
  introv Hpr.
  unfold computes_step_to_error.
  remember (compute_step lib (oterm (Abs ab) lbt)) as cs.
  destruct cs as [csk | cnk]; auto.

  left.
  eexists ; dands; eauto with slow.
  apply isprogram_noncan; eauto with slow.
Qed.

Lemma isprogram_error {p} : forall lib td,
  @isprogram p td
  -> computes_step_to_error lib td
  -> isnoncan td [+] isabs td.
Proof.
  introv Hpr Hce. repnud Hpr.
  destruct td as [?|?| o ?]; invertsn Hpr0.
  - repnud Hce; csunf Hce; allsimpl; tcsp.
  - repnud Hce.
    destruct o; allsimpl; cpx.
Qed.

Lemma computes_in_1step_alpha_r {o} :
  forall lib (tl1 tl2 tr1 tr2 : @NTerm o),
    nt_wf tl1
    -> computes_in_1step_alpha lib tl1 tr1
    -> computes_in_1step_alpha lib tl2 tr2
    -> alpha_eq tl1 tl2
    -> alpha_eq tr1 tr2.
Proof.
  introv wf H1ca H2ca Hal.
  invertsn H1ca.
  invertsn H2ca.
  repnd.
  eapply compute_1step_alpha2 in H2ca0;
    [ | | |exact H1ca0]; eauto 4 with slow.
Qed.

Lemma computes_in_kstep_fun_l {o} :
  forall lib k (tl1 tl2 tr : @NTerm o),
    nt_wf tl1
    -> alpha_eq tl1 tl2
    -> computes_in_kstep_alpha lib k tl1 tr
    -> computes_in_kstep_alpha lib k tl2 tr.
Proof.
  induction k; introv wf Hal H1ck; inverts H1ck as Hstep H1ck; econstructor; eauto with slow;[].
  eapply (computes_in_1step_alpha2 _  _ _ _ _ wf Hstep) in Hal; eauto.
Qed.


Hint Constructors computes_in_kstep : slow.

Lemma computes_in_1step_noncan_or_abs {p} : forall lib t1 t2,
  @computes_in_1step p lib t1 t2
  -> isnoncan t1 [+] isabs t1.
Proof.
  introv Hcs.
  inverts Hcs; simpl; auto.
Qed.

Lemma computes_in_1step_lsubst {p} : forall lib e t1 t2 vy,
  computes_in_1step lib (@lsubst p e [(vy, t1)]) (lsubst e [(vy, t2)])
  -> isnoncan t1
  -> isnoncan t2
  -> isnoncan (lsubst e [(vy, t2)]) [+] isabs (lsubst e [(vy, t2)]).
Proof.
  introv H1c H1n H2n.
  apply computes_in_1step_noncan_or_abs in H1c.
  eapply noncan_or_abs_lsubst; eauto.
Qed.

Lemma computes_in_1step_to_alpha {p} : forall lib t1 t2,
  @computes_in_1step p lib t1 t2
  -> computes_in_1step_alpha lib t1 t2.
Proof.
  intros.
  econstructor; dands; eauto.
Qed.

Lemma compute_step_dicot {p} : forall lib e esk,
  csuccess esk = @compute_step p lib e
  -> (e = esk # isvalue_like esk)
      [+]
     computes_in_1step lib e esk.
Proof.
  introv Hcs.
  destruct e as [|?| oo lbt]; invertsn Hcs.
  { left; dands; eauto 3 with slow. }
  dopid oo as [c|nc|exc|abs] Case;
    csunf Hcs; allsimpl; ginv; tcsp;
    try (complete (right; constructor; csunf; auto));
    try (complete (left; sp; eauto with slow)).
Qed.

Lemma computes_to_value_step {p} :
  forall lib (t1 t2 t3 : @NTerm p),
  computes_to_value lib t2 t3
  -> compute_step lib t1 = csuccess t2
  -> computes_to_value lib t1 t3.
Proof.
  introv Hcv Hcs.
  invertsn Hcv.
  apply reduces_to_if_step in Hcs.
  eapply reduces_to_trans in Hcv; eauto.
  split; auto.
Qed.

Hint Resolve computes_to_value_isvalue_refl: slow.

Lemma computes_in_1step_preserves_nt_wf {p} :
  forall lib (t u : @NTerm p),
    computes_in_1step lib t u
    -> nt_wf t
    -> nt_wf u.
Proof.
  introv comp wf.
  inversion comp as [? ? ? ? comp1|? ? ? ? comp1]; repnd; subst; clear comp;
  apply preserve_nt_wf_compute_step in comp1; auto.
Qed.

Lemma computes_in_1step_alpha_preserves_nt_wf {p} :
  forall lib (t u : @NTerm p),
    computes_in_1step_alpha lib t u
    -> nt_wf t
    -> nt_wf u.
Proof.
  introv comp wf.
  inversion comp as [? xx]; repnd.
  apply computes_in_1step_preserves_nt_wf in xx0; auto.
  apply alphaeq_preserves_wf in xx; apply xx; auto.
Qed.

Lemma computes_in_kstep_alpha2 {p} :
  forall lib k (t tv : @NTerm p),
    nt_wf t
    -> computes_in_kstep_alpha lib k t tv
    -> isvalue tv
    -> computes_to_alpha_value lib t tv.
Proof.
  induction k as [ | k Hind]; introv wf Hcka Hisv; unfolds_base.
  - invertsn Hcka. eexists; dands; eauto with slow.
  - inverts Hcka as HH HHH.
    applydup @computes_in_1step_alpha_preserves_nt_wf in HH as wf2; auto.
    apply Hind in HHH; auto.
    invertsn HHH. repnd.
    invertsn HH.
    repnd.
    eapply compute_to_value_alpha in HH; eauto.
    exrepnd.
    rename HHH0 into Hcv.
    invertsn HH0;
      exists t2'; dands; eauto 3 with slow;
      eapply computes_to_value_step; eauto.
Qed.


Lemma computes_to_value_in_max_k_steps_xx {p} :
  forall lib m (t1 t2 : @NTerm p),
   computes_to_value_in_max_k_steps lib m t1 t2
   -> computes_to_value lib t1 t2.
Proof.
  introv Hcm.
  repnud Hcm.
  constructor; auto.
  eexists; eauto.
Qed.

Lemma computes_step_to_error_no_further {p} :
  forall lib (t : @NTerm p),
  computes_step_to_error lib t
  -> forall tv k, computes_in_kstep_alpha lib (S k) t tv
  -> False.
Proof.
  unfold computes_step_to_error.
  introv Hce Hcs.
  invertsna Hcs Hcs.
  invertsn Hcs.
  exrepnd.
  invertsn Hcs1; rw Hcs1 in Hce; cpx.
Qed.

Lemma computes_in_1step_alpha_program {p} :
  forall lib (t1 t2 : @NTerm p),
  computes_in_1step_alpha lib t1 t2
  -> isprogram t1
  -> isprogram t2.
Proof.
  introv Hc1a H1p.
  invertsn Hc1a. repnd.
  apply computes_in_1step_program in Hc1a0; auto.
  apply alpha_eq_sym in Hc1a.
  eauto with slow.
Qed.

Lemma computes_to_value_wf4 {p} :
  forall lib (x y : @NTerm p),
  computes_to_value lib x y -> nt_wf y.
Proof.
  introv Hc.
  repnud Hc.
  invertsn Hc.
  repnud Hc.
  auto.
Qed.



Lemma compute_xxx {p} :
  forall lib (t v : @NTerm p),
  computes_to_value lib t v
  -> { k: nat $ computes_to_value_in_max_k_steps lib k t v}.
Proof.
  introv Hcv.
  unfold computes_to_value, reduces_to in Hcv.
  exrepnd. exists k. unfolds_base.
  sp.
Qed.

Definition hasvaluew {o} lib (t : @NTerm o) :=
  nt_wf t -> hasvalue lib t.

Lemma r1alhasvalue {p} :
  forall lib, respects1 alpha_eq (@hasvaluew p lib).
Proof.
  introv H1 H2 wf.
  allunfold @hasvaluew.
  allunfold @hasvalue.
  applydup @alphaeq_preserves_wf in H1 as q; applydup q in wf; clear q.
  autodimp H2 hyp; exrepnd.
  eapply compute_to_value_alpha in H1; eauto.
  exrepnd.
  eexists; eauto.
Qed.
Hint Resolve r1alhasvalue : respects.

Lemma hasvalue_implies_hasvaluew {o} :
  forall lib (t : @NTerm o),
    hasvalue lib t
    -> hasvaluew lib t.
Proof.
  introv hv w; auto.
Qed.

Lemma hasvaluew_implies_hasvalue {o} :
  forall lib (t : @NTerm o),
    nt_wf t
    -> hasvaluew lib t
    -> hasvalue lib t.
Proof. sp. Qed.

(*
Lemma if_hasvalue_applyx {p} :
  forall lib f a,
    isprog f
    -> isprog a
    -> hasvalue lib (mk_apply f a)
    -> {b : @NTerm p
        & computes_to_alpha_value lib f (mk_lam nvarx b)
        # hasvalue lib (subst b nvarx a)}
       [+] {s : nseq
            & {n : nat
            & computes_to_value lib f (mk_nseq s)
            # computes_to_value lib a (mk_nat n) }}
       [+] {s : ntseq
            & {n : nat
            & computes_to_value lib f (mk_ntseq s)
            # computes_to_value lib a (mk_nat n)
            # hasvalue lib (s n) }}.
Proof.
  introv H1p H2p Hv.
  apply if_hasvalue_apply in Hv; auto;[].
  repndors; exrepnd; auto.

  - left.
    allrw @isprog_eq.
    duplicate Hv0 as Hcv.
    repnud Hv0.
    invertsn Hv0.
    apply isprogram_ot_iff in Hv0.
    repnd.
    allsimpl.
    dLin_hyp.
    allunfold @num_bvars; allsimpl; GC.
    dimp (alpha_eq_bterm_single_change2 b v nvarx).
    rename hyp into Hal.
    match type of Hal with
        alpha_eq_bterm _ (bterm _ ?nt) => exists nt
    end.
    duplicate Hal as Halb.
    apply apply_bterm_alpha_congr2 with (lnt:=[a]) in Hal ; auto;[].
    allunfold @subst.
    allunfold @apply_bterm.
    allsimpl.
    apply hasvalue_implies_hasvaluew in Hv1.
    rwhg Hal Hv1.
    applydup @isprogram_bt_iff_isprog_vars in Hyp as isp.
    apply isprog_vars_eq in isp; repnd.
    apply hasvaluew_implies_hasvalue in Hv1;
      [|apply lsubst_wf_if_eauto;
         [apply wf_sub_cons;eauto 3 with slow|
          apply lsubst_wf_if_eauto; eauto 3 with slow
         ]
      ].
    dands; auto.
    unfolds_base.
    exists (mk_lam v b).
    dands; auto.
    repeat(prove_alpha_eq4); auto.

  - right; left; eexists; eexists; dands; eauto.
    SearchAbout hasvalue mk_apseq.

  -
Qed.
 *)

Lemma reduces_to_hasvalue {p} :
  forall lib (t1 t2 : @NTerm p),
  reduces_to lib t1 t2
  -> hasvalue lib t2
  -> hasvalue lib t1.
Proof.
  introns X.
  allunfold @hasvalue.
  exrepnd.
  exists t'.
  allunfold @computes_to_value.
  exrepnd. dands; auto;[].
  eauto using reduces_to_trans.
Qed.

(*
apply compute_step_atmost_exact in Xc2. exrepnd.
  eapply reduces_in_k_steps_alpha in Xc1; eauto. exrepnd.
  repnud  Xc1. apply compute_step_exact_implies_atmost in Xc1.
  exists t2'. split; auto;[].
  unfold computes_to_value, reduces_to. split; [eexists; eauto|];[].
  apply alpha_preserves_value in Xc3; auto.
Qed.
*)

Lemma computes_to_value_exception {p} :
  forall lib a (e v : @NTerm p),
    computes_to_value lib (mk_exception a e) v
    -> False.
Proof.
  introv comp.
  destruct comp.
  apply reduces_to_exception in r; subst; tcsp.
  apply isvalue_exc in i; sp.
Qed.

Lemma computes_to_exception_exception {p} :
  forall lib a b (e v : @NTerm p),
    computes_to_exception lib a (mk_exception b e) v
    -> v = e # a = b.
Proof.
  introv comp.
  destruct comp.
  unfold reduces_in_atmost_k_steps in r.
  unfold mk_exception in r.
  rw @compute_at_most_k_steps_exception in r.
  inversion r; subst; sp.
Qed.

Lemma computes_to_exception_refl {p} :
  forall lib a (e : @NTerm p),
    computes_to_exception lib a (mk_exception a e) e.
Proof.
  introv.
  unfold computes_to_exception, reduces_to, reduces_in_atmost_k_steps.
  exists 0; simpl; auto.
Qed.

Lemma norep_disjoint_implies_nr_ut_sub {o} :
  forall sub (t : @NTerm o) u,
    no_repeats (get_utokens_sub sub)
    -> disjoint (get_utokens_sub sub) (get_utokens t)
    -> nr_ut_sub u sub
    -> nr_ut_sub t sub.
Proof.
  induction sub; introv norep disj nrut; allsimpl; auto.
  destruct a as [l w].
  allrw @get_utokens_sub_cons.
  allrw disjoint_app_l; repnd.
  allrw no_repeats_app; repnd.
  allrw @nr_ut_sub_cons_iff; exrepnd; subst; allsimpl.
  allrw disjoint_singleton_l.
  eexists; dands; eauto.
  eapply IHsub; eauto.
  eapply disjoint_eqset_r;[apply eqset_sym;apply get_utokens_subst|].
  allrw disjoint_app_r; dands; auto.
  boolvar; simpl; auto.
  apply disjoint_singleton_r; auto.
Qed.

Lemma reduces_in_atmost_k_steps_change_utok_sub {o} :
  forall lib k (t u : @NTerm o) sub sub',
    nt_wf t
    -> reduces_in_atmost_k_steps lib (lsubst t sub) u k
    -> nr_ut_sub t sub
    -> nr_ut_sub t sub'
    -> dom_sub sub = dom_sub sub'
    -> disjoint (get_utokens_sub sub)  (get_utokens t)
    -> disjoint (get_utokens_sub sub') (get_utokens t)
    -> {w : NTerm
        & {s : NTerm
        & alpha_eq u (lsubst w sub)
        # disjoint (get_utokens_sub sub) (get_utokens w)
        # subvars (free_vars w) (free_vars t)
        # subset (get_utokens w) (get_utokens t)
        # reduces_in_atmost_k_steps lib (lsubst t sub') s k
        # alpha_eq s (lsubst w sub')}}.
Proof.
  induction k; introv wf comp nrut1 nrut2 eqdoms d1 d2.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t (lsubst t sub'); dands; eauto 3 with slow.
    rw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    pose proof (compute_step_subst_utoken lib t u0 sub) as h.
    allsimpl; allrw disjoint_app_r; repnd.
    repeat (autodimp h hyp); exrepnd.

    pose proof (h0 sub') as p; repeat (autodimp p hyp); clear h0; exrepnd.

    applydup @compute_step_preserves in comp1 as wfu; repnd;
    [|apply lsubst_wf_if_eauto; eauto 3 with slow];[].
    applydup @alphaeq_preserves_wf in h1 as q.
    applydup q in wfu as wfw; clear q.
    apply lsubst_wf_iff in wfw; eauto 3 with slow;[].

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u0 (lsubst w sub) wfu h1 k u comp0) as comp'.
    exrepnd.

    pose proof (IHk w t2' sub sub' wfw comp'1) as q; clear IHk.
    repeat (autodimp q hyp); eauto 4 with slow.
    exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib (lsubst w sub') s) as c.
    repeat (autodimp c hyp); eauto 4 with slow.
    pose proof (c k s0 q5) as comp'; clear c; exrepnd.

    exists w0 t2'0; dands; eauto with slow.

    rw @reduces_in_atmost_k_steps_S.
    exists s; dands; auto.
Qed.


Lemma iscan_sterm {o} :
  forall (f : @ntseq o), iscan (sterm f).
Proof.
  introv; simpl; auto.
Qed.
Hint Resolve iscan_sterm : slow.

Lemma is_can_or_exc_sterm {o} :
  forall (f : @ntseq o), is_can_or_exc (sterm f).
Proof.
  introv; left; eauto 3 with slow.
Qed.
Hint Resolve is_can_or_exc_sterm : slow.

(* end hide *)

(* begin hide *)
