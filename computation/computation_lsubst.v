Require Export computation_preserve4.


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
  nterm_ind1s t as [v|op bs ind] Case; introv wf cl sv comp; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "NCan".
      destruct bs; try (complete (allsimpl; ginv)).

      { csunf comp; simpl in *.
        apply compute_step_ncan_nil_success in comp; repnd; subst; simpl in *.
        csunf; simpl; eexists; dands; eauto. }

      destruct b as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [v|op bts]; try (complete (allsimpl; ginv)).

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

              { allunfold @mk_choice_seq; allsimpl; ginv; GC; allsimpl; fold_terms.
                csunf; simpl; dcwf h; simpl; boolvar; try omega.
                rw @Znat.Nat2Z.id; allrw.
                eexists; dands; eauto; autorewrite with slow; auto. }

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

          { SSSCase "NSwapCs1".
            simpl in *; autorewrite with slow in *.
            csunf comp; simpl in *.
            apply compute_step_swap_cs1_success in comp; repndors; exrepnd; subst; simpl in *;
              autorewrite with slow in *.
            { csunf; simpl; eexists; dands; eauto. }
            { csunf; simpl; eexists; dands; eauto. }
            { apply nt_wf_swap_cs1_iff in wf; exrepnd.
              repeat (destruct l; simpl in *; ginv;[]).
              unfold nobnd in wf1; inversion wf1; subst; GC; simpl in *; autorewrite with slow in *.
              rewrite compute_step_swap_cs1_if_isnoncan_like; eauto 3 with slow.
              eapply ind in comp2; try (right; left); eauto; simpl; eauto 3 with slow;
                try (complete (eapply subvars_trans;[|eauto]; eauto 3 with slow)).
              exrepnd; simpl in *; allrw; eexists; dands; eauto.
              apply implies_alpha_eq_mk_swap_cs1; eauto 3 with slow. } }

          { SSSCase "NSwapCs2".
            simpl in *; autorewrite with slow in *.
            csunf comp; simpl in *.
            apply compute_step_swap_cs2_success in comp; repndors; exrepnd; subst; simpl in *;
              autorewrite with slow in *.
            csunf; simpl; eexists; dands; eauto.
            apply alpha_eq_oterm_combine; unfold push_swap_cs_bterms; autorewrite with slow; dands; auto.
            introv i.
            rewrite <- map_combine in i; apply in_map_iff in i; exrepnd; ginv.
            rewrite <- map_combine in i1; apply in_map_iff in i1; exrepnd; ginv.
            apply in_combine_same in i1; repnd; subst.
            destruct a1; simpl; apply alpha_eq_bterm_congr; autorewrite with slow; fold_terms; tcsp;
              try rewrite lsubst_aux_cl_sub_push_swap_cs_sub_term; eauto 3 with slow;
                try (apply disjoint_sym; apply disjoint_dom_sub_filt). }

          { SSSCase "NSwapCs0".
            simpl in *; autorewrite with slow in *.
            csunf comp; simpl in *.
            apply compute_step_swap_cs0_success in comp; repndors; exrepnd; subst; simpl in *;
              autorewrite with slow in *.
            { csunf; simpl; eexists; dands; eauto.

              unfold push_swap_cs0, push_swap_cs_sub_term.
              rewrite free_vars_lsubst_aux_cl; auto.
              rewrite <- lsubst_aux_swap_cs_term.
              rewrite remove_nvars_nil_if_subset; try apply subvars_eq; auto;[].
              simpl; autorewrite with slow.

(* It looks like those will be computationally equivalent but not alpha-equal *)

SearchAbout (remove_nvars _ _ = []).
              SearchAbout swap_cs_term lsubst_aux.

 }
            { csunf; simpl; eexists; dands; eauto. }
            { apply nt_wf_swap_cs0_iff in wf; exrepnd.
              repeat (destruct l; simpl in *; ginv;[]).
              unfold nobnd in wf1; inversion wf1; subst; GC; simpl in *; autorewrite with slow in *.
              rewrite compute_step_swap_cs0_if_isnoncan_like; eauto 3 with slow.
              eapply ind in comp2; try (right; left); eauto; simpl; eauto 3 with slow;
                try (complete (eapply subvars_trans;[|eauto]; eauto 3 with slow)).
              exrepnd; simpl in *; allrw; eexists; dands; eauto.
              apply implies_alpha_eq_mk_swap_cs1; eauto 3 with slow. } }

          { SSSCase "NLDepth".
            csunf comp; simpl in *; ginv. }

          { SSSCase "NLastCs".
            csunf comp; allsimpl.
            apply compute_step_last_cs_success in comp; exrepnd; subst; simpl in *.
            csunf; simpl; allrw.
            eexists; dands; eauto.
            rewrite lsubst_aux_find_last_entry_default.
            autorewrite with slow in *; auto.
          }

          { SSSCase "NCompSeq1".
            csunf comp; allsimpl.
            apply compute_step_comp_seq1_success in comp; exrepnd; subst; simpl in *.
            csunf; simpl.
            repndors; repnd; subst; simpl in *; boolvar; subst; autorewrite with slow in *; try omega;
              eexists; dands; eauto.
          }

          { SSSCase "NCompSeq2".
            csunf comp; allsimpl.
            apply compute_step_comp_seq2_success in comp; exrepnd; subst; simpl in *.
            csunf; simpl.
            repndors; repnd; subst; simpl in *; boolvar; subst; autorewrite with slow in *; try omega;
              eexists; dands; eauto.
          }

          { SSSCase "NCompOp".

            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b as [l t].
            destruct l; destruct t as [v|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

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
            destruct l; destruct t as [v|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

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

          remember (get_fresh_atom lib t) as a'.
          remember (get_fresh_atom lib (lsubst_aux t (sub_filter sub [n]))) as a''.

          pose proof (get_fresh_atom_prop_and_lib lib t) as fa'; rw <- Heqa' in fa'.
          pose proof (get_fresh_atom_prop_and_lib lib (lsubst_aux t (sub_filter sub [n]))) as fa''; rw <- Heqa'' in fa''.

          pose proof (compute_step_subst_utoken lib t x [(n, mk_utoken a')]) as ch.
          allrw @nt_wf_fresh.
          repeat (autodimp ch hyp); eauto 4 with slow.
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; tcsp. }
          exrepnd.

          pose proof (ch0 [(n,mk_utoken a'')]) as comp'; clear ch0; allsimpl.
          repeat (autodimp comp' hyp).
          { apply nr_ut_sub_cons; auto; introv i j.
            destruct fa''.
            apply get_utokens_lib_lsubst_aux; rw in_app_iff; tcsp. }
          { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; intro i.
            destruct fa''.
            apply get_utokens_lib_lsubst_aux; rw in_app_iff; tcsp. }
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
            allrw @get_utokens_lsubst; allrw @get_utokens_lib_lsubst;
              allrw in_app_iff; allrw not_over_or; repnd.
            repndors; tcsp.

            { apply (get_utokens_subset_get_utokens_lib lib) in h.
              apply ch4 in h.
              unfold get_utokens_lib in h; apply in_app_iff in h; repndors; tcsp. }

            { eapply get_utokens_sub_sub_keep_first_subset in h;
                [|apply subvars_eq in ch3;eauto]; tcsp. }
          }

          apply implies_alpha_eq_mk_fresh.
          apply (alpha_eq_subst_utokens _ _ [(a',mk_var n)] [(a',mk_var n)]) in ch1; eauto 3 with slow.
          pose proof (simple_alphaeq_subst_utokens_subst w n a') as aeq1.
          autodimp aeq1 hyp.
          { intro k.
            apply (get_utokens_subset_get_utokens_lib lib) in k.
            apply ch4 in k; tcsp. }

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

Lemma reduces_to_lsubst_aux {o} :
  forall lib (t u : @NTerm o) sub,
    nt_wf t
    -> prog_sub sub
    -> subvars (free_vars t) (dom_sub sub)
    -> reduces_to lib t u
    -> {v : NTerm
        & reduces_to lib (lsubst_aux t sub) v
        # alpha_eq v (lsubst_aux u sub) }.
Proof.
  introv wf cl sv r.
  unfold reduces_to in r; exrepnd.
  revert dependent u.
  revert dependent t.

  induction k; introv wf sv r.

  - rw @reduces_in_atmost_k_steps_0 in r; subst.
    exists (lsubst_aux u sub); dands; auto.
    exists 0; rw @reduces_in_atmost_k_steps_0; auto.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    pose proof (compute_step_lsubst_aux lib t u0 sub) as h.
    repeat (autodimp h hyp); exrepnd; eauto 3 with slow.

    applydup @compute_step_preserves in r1; repnd; auto.
    assert (subvars (free_vars u0) (dom_sub sub))
      as sv2 by (eapply subvars_trans; eauto).

    pose proof (IHk u0 r2 sv2 u r0) as j; exrepnd.

    pose proof (reduces_to_alpha lib (lsubst_aux u0 sub) v v0) as x;
      repeat (autodimp x hyp);[|apply alpha_eq_sym;auto|];
      exrepnd;
      eauto 3 with slow.
    exists t2'; dands; auto.

    + eapply reduces_to_trans;[|complete eauto].
      apply reduces_to_if_step; auto.

    + eapply alpha_eq_trans;[|complete eauto].
      apply alpha_eq_sym; auto.
Qed.
