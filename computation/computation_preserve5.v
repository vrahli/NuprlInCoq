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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export computation_preserve4.


(** %\noindent% The following lemma expresses a consequence of the fact the
    first argument of a [NonCanonicalOp] is always principal. Hence,
    if an arbitrary non-canonical term [(oterm (NCan op) lbt)] computes
    to a value in at most [S k] steps, [lbt] must be of the form
    [lbt = (bterm [] la)::lbtt] and there is an [m] such that $m \le k$ and
    [la] (the principal argument) computes to some canonical term
    [(oterm (Can c) lbtc)] in m and the whole term computes
    also takes m steps to compute to
    [((oterm (NCan op) ((bterm [] (oterm (Can c) lbtc))::lbtt)))]

 *)

Lemma implies_reduces_in_atmost_k_steps_S {o} :
  forall (lib : library) (t v : @NTerm o) (k : nat),
    reduces_in_atmost_k_steps lib t v (S k)
    -> {u : NTerm
        & compute_step lib t = csuccess u
        # reduces_in_atmost_k_steps lib u v k}.
Proof.
  introv comp.
  apply reduces_in_atmost_k_steps_S; auto.
Qed.

Fixpoint get_names_from_reduces_in_atmost_k_steps {o}
           {lib : @library o}
           {t u : @NTerm o}
           {k : nat} : reduces_in_atmost_k_steps lib t u k
                       -> list (get_patom_set o) :=
  match k with
    | 0 => fun comp => get_utokens_step_seq t
    | S n =>
      fun comp =>
        get_utokens_step_seq t
                 ++ match implies_reduces_in_atmost_k_steps_S lib t u n comp with
                      | existT w (c,r) => get_names_from_reduces_in_atmost_k_steps r
                    end
  end.

Definition get_names_from_computes_to_val_like_in_max_k_steps {o}
           {lib : @library o}
           {t u : @NTerm o}
           {k : nat}
           (c : computes_to_val_like_in_max_k_steps lib t u k)
  : list (get_patom_set o) :=
  get_names_from_reduces_in_atmost_k_steps (fst c).

Definition get_fresh_atom_list {o} (l : list (get_patom_set o)) : get_patom_set o :=
  projT1 (fresh_atom o l).

Lemma compute_decompose_aux {p} :
forall lib (op : NonCanonicalOp) (k: nat) (lbt : list BTerm)  (a : NTerm)
       (comp : computes_to_val_like_in_max_k_steps lib (oterm (NCan op) lbt) a (S k))
       (isp : isprogram (oterm (NCan op) lbt)),
  {la : NTerm
    $ {lbtt: list BTerm
    $ { t : @NTerm p
    $ { m : nat
    $ m <= k
    # lbt = bterm [] la :: lbtt
    # reduces_in_atmost_k_steps lib la t m
    # reduces_in_atmost_k_steps lib
         (oterm (NCan op) lbt)
         (oterm (NCan op) ((bterm [] t)::lbtt))
         m
    # is_can_or_exc t}}}}
   [+]
   {v : NVar
    & {t : NTerm
    & {u : NTerm
    & {x : NTerm
    & {w : NTerm
    & {m : nat
    & m <= k
    # op = NFresh
    # lbt = [bterm [v] t]
    # let names := get_names_from_computes_to_val_like_in_max_k_steps comp in
      let a := get_fresh_atom_list names in
      reduces_in_atmost_k_steps lib (subst t v (mk_utoken a)) x m
      # alpha_eq x (subst u v (mk_utoken a))
      # subset (get_utokens u) (get_utokens t)
      # reduces_in_atmost_k_steps lib (oterm (NCan op) lbt) (mk_fresh v w) m
      # alpha_eq u w
      # isvalue_like u
   }}}}}}.
Proof.
  induction k as [| k Hind]; introv isp.
  - repnud comp.
    unfold reduces_in_atmost_k_steps in comp0.
    simpl in comp0.
    rename comp0 into Hcomp.
    dlist lbt SSCase as [| arg1].
    inversion Hcomp.
    (**takes care of nilcase as no ncop takes 0 bterms*)

    SSCase "conscase".
    destruct arg1 as [arg1vs arg1nt];
      dlist arg1vs SSSCase as [|arg1v1];
      [|].

    { SSSCase "nilcase".
      destruct arg1nt as [v89|f|arg1o arg1bts];[inverts Hcomp| |];[|].

      { csunf Hcomp; allsimpl.
        left.
        exists (sterm f) lbt (sterm f) 0.
        allrw @reduces_in_atmost_k_steps_0.
        dands; eauto 3 with slow. }

      left.
      dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase.

      + SSSSCase "Can".
        exists (oterm (Can arg1c) arg1bts) lbt (oterm (Can arg1c) arg1bts) 0.
        dands; spc; left; sp.

      + SSSSCase "NCan".
        rw @compute_step_ncan_ncan in Hcomp.
        remember (compute_step lib (oterm (NCan arg1nc) arg1bts)).
        destruct c; spc; inverts Hcomp.
        provefalse.
        unfold isvalue_like in Hcv; allsimpl; sp.

      + SSSSCase "Exc".
        csunf Hcomp; allsimpl.
        destruct op;
          try (complete (apply compute_step_catch_success in Hcomp; repdors; exrepnd; subst;
                         try (complete (inversion Hcomp1)); try (complete (inversion Hcv0));
                         unfold reduces_in_atmost_k_steps;
                         exists (oterm Exc arg1bts)
                                lbt
                                (oterm Exc arg1bts) 0; dands; auto;
                                right; sp)).

        apply compute_step_catch_success in Hcomp; exrepnd; subst.
        destruct Hcomp as [Hcomp|Hcomp]; exrepnd; GC; cpx; subst; ginv.

        * exists (mk_exception a' e)
                 [bterm [] a0; bterm [v] b]
                 (mk_exception a' e) 0; dands; simpl; auto;
          allrw @fold_try; allrw @fold_exception;
          unfold reduces_in_atmost_k_steps;
          unfold computes_to_value_in_max_k_steps; simpl; eauto with slow.

      + SSSSCase "Abs".
        rw @compute_step_ncan_abs in Hcomp.
        remember (compute_step_lib lib arg1abs arg1bts).
        destruct c; spc; inverts Hcomp.
        unfold isvalue_like in Hcv; allsimpl; sp.
    }

    { SSSCase "conscase".
      right.
      csunf Hcomp; allsimpl.
      apply compute_step_fresh_success in Hcomp; exrepnd; subst.
      repndors; exrepnd; subst.

      - unfold isvalue_like in Hcv; allsimpl; sp.

      - exists arg1v1 arg1nt arg1nt
               (subst arg1nt arg1v1 (mk_utoken (get_fresh_atom arg1nt)))
               arg1nt
               0; dands; eauto with slow;
        rw @reduces_in_atmost_k_steps_0; auto.

      - unfold isvalue_like in Hcv; allsimpl; tcsp.
    }

  - unfold computes_to_val_like_in_max_k_steps in Hcv; repnd.
    rw @reduces_in_atmost_k_steps_S in Hcv0; exrepnd.
    rename Hcv0 into Hcomp.
    dlist lbt SSCase as [| arg1];
      [dopid_noncan op SSSCase; inverts Hcomp|];[].
             (**takes care of nilcase as no ncop takes 0 bterms*)

    SSCase "conscase".
    destruct arg1 as [arg1vs arg1nt];
    dlist arg1vs SSSCase as [|arg1v1];[|].

    { SSSCase "nilcase".
      destruct arg1nt as [v89|f| arg1o arg1bts]; [inverts Hcomp| |];[|].

      { csunf Hcomp; allsimpl.
        left.
        exists (sterm f) lbt (sterm f) 0.
        allrw @reduces_in_atmost_k_steps_0.
        dands; eauto 3 with slow; try omega. }

      dopid arg1o as [arg1c | arg1nc | arg1exc | arg1abs] SSSSCase.

      + SSSSCase "Can".
        left.
        exists (oterm (Can arg1c) arg1bts) lbt (oterm (Can arg1c) arg1bts) 0.
        dands;spc; try omega; left; sp.

      + SSSSCase "NCan".
        rw @compute_step_ncan_ncan in Hcomp.
        remember (compute_step lib (oterm (NCan arg1nc) arg1bts)) as Hc.
        destruct Hc; ginv.

        make_and Hcv1 Hcv.
        applydup Hind in Hcv1Hcv;
          [| eauto with slow; fail].
        clear Hind; repndors; exrepnd; cpx.

        left.
        exists (oterm (NCan arg1nc) arg1bts) lbtt t (S m); dands; auto; try omega.
        { rw @reduces_in_atmost_k_steps_S.
          rw <- HeqHc; eexists; dands; eauto. }
        { rw @reduces_in_atmost_k_steps_S.
          rw @compute_step_ncan_ncan; rw <- HeqHc.
          eexists; dands; eauto. }

      + SSSSCase "Exc".
        csunf Hcomp; allsimpl.
        left.
        exists (oterm Exc arg1bts) lbt (oterm Exc arg1bts) 0.
        dands; auto; try omega; allrw @reduces_in_atmost_k_steps_0; auto.
        right; sp.

      + SSSSCase "Abs".
        rw @compute_step_ncan_abs in Hcomp.
        remember (compute_step_lib lib arg1abs arg1bts) as Hc.
        destruct Hc; ginv.
        symmetry in HeqHc.

        make_and Hcv1 Hcv.
        applydup Hind in Hcv1Hcv;
          [|apply isprogram_compute_step_lib in HeqHc; eauto with slow].
        clear Hind; repndors; exrepnd; cpx.

        left.
        exists (oterm (Abs arg1abs) arg1bts) lbtt t (S m); dands; auto; try omega.
        { rw @reduces_in_atmost_k_steps_S.
          csunf; simpl; rw HeqHc; eexists; dands; eauto. }
        { rw @reduces_in_atmost_k_steps_S.
          rw @compute_step_ncan_abs; rw HeqHc.
          eexists; dands; eauto. }
    }

    { SSSCase "conscase".
      csunf Hcomp; allsimpl.
      apply compute_step_fresh_success in Hcomp; exrepnd; subst; fold_terms.
      right.
      exists arg1v1 arg1nt.

      repndors; exrepnd; subst.

      - pose proof (reduces_in_atmost_k_step_fresh_id lib arg1v1 a) as h.
        repeat (autodimp h hyp).
        destruct h.
        exists (S k); auto.

      - apply reduces_in_atmost_k_steps_if_isvalue_like in Hcv1; subst; eauto with slow.
        exists arg1nt
               (subst arg1nt arg1v1 (mk_utoken (get_fresh_atom arg1nt)))
               arg1nt
               0;
          dands; eauto with slow; try omega;
          rw @reduces_in_atmost_k_steps_0; auto.

      - fold_terms.
        make_and Hcv1 Hcv.
        apply Hind in Hcv1Hcv; fold_terms; clear Hind.

        + repndors; exrepnd; ginv.
          remember (get_fresh_atom arg1nt) as ua.
          remember (get_fresh_atom (subst_utokens x [(ua, mk_var v)])) as ua'.

          pose proof (get_fresh_atom_prop arg1nt) as fa; rw <- Hequa in fa.
          pose proof (get_fresh_atom_prop (subst_utokens x [(ua,mk_var v)])) as fa'; rw <- Hequa' in fa'.

          applydup @isprog_ntwf_eauto in Hpr as wf.
          allrw @nt_wf_fresh.

          pose proof (compute_step_subst_utoken lib arg1nt x [(v,mk_utoken ua)]) as h.
          repeat (autodimp h hyp); eauto 3 with slow.
          { apply nr_ut_sub_cons_iff; eexists; dands; eauto.
            introv i j.
            apply subset_get_utokens_get_utokens_step_seq in j; sp. }
          { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; tcsp. }
          exrepnd.
          unfold get_utokens_sub in h2; allsimpl; allrw disjoint_singleton_l.
          allrw @fold_subst.

          assert (wf_term x) as wfx.
          { apply compute_step_preserves_wf in Hcomp2; auto;[].
            apply wf_term_subst; eauto 3 with slow. }

          pose proof (reduces_in_atmost_k_steps_change_utok_sub
                        lib m (subst_utokens x [(ua, mk_var v)])
                        x0
                        [(v,mk_utoken ua')]
                        [(v,mk_utoken ua)]) as q.
          repeat (autodimp q hyp); eauto 3 with slow.

          { apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow. }

          { constructor; auto; intros i j.
            apply get_utokens_subst_utokens_subset in j.
            rw in_app_iff in j; allsimpl; repndors; tcsp.
            apply in_remove in j; repnd; tcsp. }

          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; tcsp. }

          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l.
            intro j.
            apply get_utokens_subst_utokens_subset in j.
            rw in_app_iff in j; allsimpl; repndors; tcsp.
            apply in_remove in j; repnd; tcsp. }

          exrepnd; allrw @fold_subst.

          assert (alpha_eq
                    (subst (subst_utokens x [(ua, mk_var v)]) v (mk_utoken ua))
                    (subst w0 v (mk_utoken ua))) as aeq.
          { apply lsubst_alpha_congr3; eauto 3 with slow.
            apply (alpha_eq_trans _ (subst_utokens (subst w0 v (mk_utoken ua)) [(ua, mk_var v)])).
            - apply alpha_eq_subst_utokens; eauto with slow.
            - apply simple_alphaeq_subst_utokens_subst; auto.
          }

          assert (alpha_eq (subst (subst_utokens x [(ua, mk_var v)]) v (mk_utoken ua))
                           x) as aeq2 by eauto with slow.

          dup q5 as c.
          eapply reduces_in_atmost_k_steps_alpha in c; eauto; exrepnd.

          unfold get_utokens_sub in q2; allsimpl; allrw disjoint_singleton_l.

          assert (!LIn ua' (get_utokens u)) as ni.
          { intro j; apply Hcv1Hcv6 in j.
            apply get_utokens_subst_utokens_subset in j.
            rw in_app_iff in j; allsimpl; repndors; tcsp.
            apply in_remove in j; repnd; tcsp.
            destruct fa'.
            apply get_utokens_subst_utokens_subset2; simpl; auto.
            rw in_remove; sp. }

          assert (alpha_eq u w1) as aeq0.
          { assert (alpha_eq (subst u v (mk_utoken ua')) (subst w1 v (mk_utoken ua'))) as h by eauto with slow.
            pose proof (change_bvars_alpha_wspec [v] u) as k1.
            pose proof (change_bvars_alpha_wspec [v] w1) as k2.
            exrepnd.
            allrw disjoint_singleton_l.
            pose proof (lsubst_alpha_congr2 ntcv0 u [(v,mk_utoken ua')]) as p1.
            pose proof (lsubst_alpha_congr2 ntcv w1 [(v,mk_utoken ua')]) as p2.
            autodimp p1 hyp; autodimp p2 hyp; eauto 3 with slow.
            allrw @fold_subst.
            assert (alpha_eq (subst ntcv0 v (mk_utoken ua')) (subst ntcv v (mk_utoken ua'))) as h' by eauto with slow.
            apply alpha_eq_subst_utoken_not_in_implies in h'; eauto with slow.
            { intro j; destruct ni; apply alphaeq_preserves_utokens in k3; rw k3; auto. }
            { intro j; destruct q2; apply alphaeq_preserves_utokens in k0; rw k0; auto. }
          }

          exists w1 t2' w (S m); dands; eauto 3 with slow; try omega.

          { rw @reduces_in_atmost_k_steps_S.
            exists x; dands; auto. }

          { introv j.
            apply q4 in j.
            apply get_utokens_subst_utokens_subset in j.
            rw in_app_iff in j; allsimpl; repndors; tcsp.
            apply in_remove in j; repnd; tcsp.
            apply alphaeq_preserves_utokens in h1; rw h1 in j.
            apply get_utokens_subst in j; boolvar; tcsp; allsimpl; allrw in_app_iff;
            allsimpl; repndors; tcsp.
          }

          { rw @reduces_in_atmost_k_steps_S.
            unfold mk_fresh.
            rw @compute_step_fresh_if_isnoncan_like; auto.
            rw <- Hequa; rw Hcomp2; simpl.
            eexists; dands; eauto; fold_terms. }

          { apply nt_wf_subst; eauto 3 with slow.
            apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow. }

        + allrw @isprogram_fresh.
          apply implies_isprog_vars_subst_utokens; eauto 3 with slow.
          apply compute_step_preserves in Hcomp2; repnd.
          allrw @isprog_vars_eq; repnd; dands; auto.
          { eapply subvars_trans;[exact Hcomp0|].
            rw @cl_subst_subst_aux; eauto 3 with slow; unfold subst_aux.
            rw @free_vars_lsubst_aux_cl; eauto 3 with slow. }
          { apply nt_wf_subst; eauto 3 with slow.
            apply isprog_vars_eq in Hpr; tcsp. }
    }
Qed.

Lemma compute_decompose {p} :
forall lib (op : NonCanonicalOp) (k: nat) (lbt : list BTerm)  (a : NTerm),
  isprogram (oterm (NCan op) lbt)
  -> computes_to_value_in_max_k_steps lib (S k) (oterm (NCan op) lbt) a
  -> { la : NTerm
      $ { lbtt: list BTerm
      $ { t : @NTerm p
      $ { m : nat
        $ m <= k
        # lbt = (bterm [] la)::lbtt
        # reduces_in_atmost_k_steps lib la t m
        # reduces_in_atmost_k_steps lib
             (oterm (NCan op) lbt)
             (oterm (NCan op) ((bterm [] t)::lbtt))
             m
        # is_can_or_exc t}}}}
     [+]
     {v : NVar
      & {t : NTerm
      & {u : NTerm
      & {x : NTerm
      & {w : NTerm
      & {m : nat
      & m <= k
      # op = NFresh
      # lbt = [bterm [v] t]
      # let a := get_fresh_atom t in
        reduces_in_atmost_k_steps lib (subst t v (mk_utoken a)) x m
        # alpha_eq x (subst u v (mk_utoken a))
        # subset (get_utokens u) (get_utokens t)
        # reduces_in_atmost_k_steps lib (oterm (NCan op) lbt) (mk_fresh v w) m
        # alpha_eq u w
        # isvalue_like u
     }}}}}}.
Proof.
  introv isp comp.
  apply @compute_decompose_aux with (a := a); auto.
  unfold computes_to_value_in_max_k_steps in comp; repnd.
  unfold computes_to_val_like_in_max_k_steps; dands; auto.
  left.
  inversion comp; subst; sp.
Qed.

Lemma nterm_trico_like {o} :
  forall (t : @NTerm o),
    isvariable t
    [+] isvalue_like t
    [+] isnoncan_like t.
Proof.
  introv.
  destruct t as [v|f|op bs]; simpl; tcsp; eauto 3 with slow.
  right.
  dopid op as [can|ncan|exc|abs] Case; unfold isvalue_like, isnoncan_like; simpl; sp.
Qed.

(* !!MOVE *)
Lemma alphaeq_vs_implies_alphaeq {o} :
  forall (t1 t2 : @NTerm o) l,
    alphaeq_vs l t1 t2 -> alphaeq t1 t2.
Proof.
  introv aeq.
  apply alphaeq_exists.
  eexists; eauto.
Qed.

Lemma simple_subst_aux_subst_utokens_aux_aeq {o} :
  forall (t1 t2 : @NTerm o) a v,
    wf_term t2
    -> !LIn v (bound_vars t1)
    -> !LIn v (free_vars t1)
    -> alpha_eq t1 t2
    -> alpha_eq
         (subst_aux (subst_utokens_aux t1 [(a, mk_var v)]) v (mk_utoken a))
         t2.
Proof.
  nterm_ind1s t1 as [x|f ind|op bs ind] Case; introv wf ni1 ni2 aeq; auto.

  - Case "vterm".
    allsimpl.
    unfold subst_aux; simpl.
    allrw not_over_or; repnd; GC.
    inversion aeq; subst; clear aeq.
    boolvar; tcsp.

  - Case "oterm".
    rw @subst_utokens_aux_oterm.
    apply alpha_eq_oterm_implies_combine in aeq; exrepnd; subst.
    allrw @wf_oterm_iff; repnd.
    allsimpl.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.

    + allapply @get_utok_some; subst; allsimpl.
      destruct bs'; allsimpl; cpx; allsimpl; GC.
      unfold subst_utok, subst_aux; simpl.
      repeat (boolvar; subst; allsimpl; auto).

    + unfold subst_aux; simpl.
      allrw map_map; unfold compose.
      apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
      introv i.
      rw <- map_combine_left in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      destruct a1 as [l1 t1].
      destruct a0 as [l2 t2].
      allsimpl.
      applydup aeq0 in i1.
      applydup in_combine in i1; repnd.
      allrw lin_flat_map.

      assert (!LIn v l1) as nivl1.
      { intro i; destruct ni1; eexists; dands; eauto; simpl; rw in_app_iff; sp. }

      boolvar; tcsp.

      apply alphaeqbt_eq in i0.
      rw @alphaeqbt_all in i0.
      pose proof (i0 (allvars (lsubst_aux (subst_utokens_aux t1 [(a, mk_var v)]) [(v, mk_utoken a)]))) as aeq.
      inversion aeq as [? ? ? ? ? len1 len2 disj norep ae]; subst; allsimpl.
      allrw disjoint_app_r; repnd.
      apply alphaeq_vs_implies_alphaeq in ae.
      apply alphaeq_eq in ae.

      apply alphaeqbt_eq.
      apply (aeqbt _ vs); simpl; auto.
      { allrw disjoint_app_r; dands; auto. }

      apply alphaeq_eq.
      rw @lsubst_aux_cswap_cswap; eauto 3 with slow; simpl; fold_terms.
      rw @cswap_subst_utokens_aux; simpl.
      apply (ind t1 (cswap (mk_swapping l1 vs) t1) l1); auto.
      { rw @osize_cswap; eauto 3 with slow. }
      { apply wf_term_cswap; apply wf in i2.
        apply wf_bterm_iff in i2; auto. }
      { rw @bound_vars_cswap.
        rw in_swapbvars; intro k; exrepnd.
        apply swapvars_eq in k0; eauto 2 with slow; subst.
        destruct ni1.
        eexists; dands; eauto; simpl; rw in_app_iff; sp. }
      { rw @free_vars_cswap; eauto 2 with slow.
        rw in_swapbvars; intro k; exrepnd.
        apply swapvars_eq in k0; eauto 2 with slow; subst.
        destruct ni2.
        eexists; dands; eauto; simpl; rw in_remove_nvars; sp. }
Qed.

Lemma simple_subst_subst_utokens_aeq {o} :
  forall (t : @NTerm o) a v,
    wf_term t
    -> !LIn v (free_vars t)
    -> alpha_eq
         (subst (subst_utokens t [(a, mk_var v)]) v (mk_utoken a))
         t.
Proof.
  introv wf ni.
  unfsubst.
  pose proof (unfold_subst_utokens [(a,mk_var v)] t) as aeq; exrepnd; allsimpl.
  allrw disjoint_singleton_r.
  rw aeq0.
  apply simple_subst_aux_subst_utokens_aux_aeq; eauto with slow.
  intro i.
  apply alphaeq_preserves_free_vars in aeq1; rw <- aeq1 in i; sp.
Qed.

Lemma reduces_to_fresh {o} :
  forall lib (t : @NTerm o) u v,
    let a := get_fresh_atom t in
    wf_term t
    -> reduces_to lib (subst t v (mk_utoken a)) u
    -> {z : NTerm
        & reduces_to lib (mk_fresh v t) (mk_fresh v z)
        # alpha_eq z (subst_utokens u [(a,mk_var v)])}.
Proof.
  introv; simpl.
  introv wf r.
  unfold reduces_to in r; exrepnd.
  revert t v u wf r0.
  induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t; dands; eauto 1 with slow.
    apply alpha_eq_sym.
    apply simple_alphaeq_subst_utokens_subst.
    pose proof (get_fresh_atom_prop t) as h; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    remember (get_fresh_atom t) as a.
    pose proof (get_fresh_atom_prop t) as gfa.
    rw <- Heqa in gfa.
    allrw in_app_iff; allrw not_over_or; repnd.

    pose proof (nterm_trico_like t) as tri1; repndors.

    {
      apply isvariable_implies in tri1; exrepnd; subst t; allsimpl; GC.
      unfsubst in comp1; allsimpl; boolvar.
      - csunf comp1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 1 with slow; subst.
        exists (@vterm o v0); dands; eauto with slow.
        unfold subst_utokens; simpl.
        unfold subst_utok; simpl; boolvar; tcsp.
      - csunf comp1; allsimpl; ginv.
    }

    {
      assert (isvalue_like (subst t v (mk_utoken a))) as isv.
      { apply isvalue_like_subst; auto. }
      rw @compute_step_value_like in comp1; auto; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 1 with slow; subst.
      exists t; dands; eauto 1 with slow.
      apply alpha_eq_sym; apply simple_alphaeq_subst_utokens_subst; eauto 3 with slow.
    }

    assert (compute_step lib (mk_fresh v t)
            = csuccess (mk_fresh v (subst_utokens u0 [(a,mk_var v)]))) as cs.
    { unfold mk_fresh; rw @compute_step_fresh_if_isnoncan_like; auto.
      rw <- Heqa; rw comp1; simpl; auto. }

    remember (get_fresh_atom (subst_utokens u0 [(a, mk_var v)])) as a'.

    applydup @compute_step_preserves in comp1; eauto 3 with slow; repnd;
    [|apply nt_wf_subst; eauto 3 with slow].

    assert (alpha_eq u0 (subst (subst_utokens u0 [(a, mk_var v)]) v (mk_utoken a))) as aeq.
    { apply alpha_eq_sym.
      apply simple_subst_subst_utokens_aeq; auto.
      - apply compute_step_preserves_wf in comp1; auto.
        apply wf_term_subst; eauto with slow.
      - rw subvars_eq in comp3; intro i; apply comp3 in i.
        unfsubst in i.
        rw @free_vars_lsubst_aux_cl in i; eauto 3 with slow; allsimpl.
        rw in_remove_nvars in i; allsimpl; tcsp.
    }

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u0 (subst (subst_utokens u0 [(a, mk_var v)]) v (mk_utoken a))
                  comp2 aeq k u comp0) as r; exrepnd.

    pose proof (get_fresh_atom_prop (subst_utokens u0 [(a,mk_var v)])) as gfa'.
    rw <- Heqa' in gfa'.

    pose proof (reduces_in_atmost_k_steps_change_utok_sub
                  lib k (subst_utokens u0 [(a, mk_var v)])
                  t2' [(v,mk_utoken a)] [(v,mk_utoken a')]) as chu.
    repeat (autodimp chu hyp).
    { apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow. }
    { apply nr_ut_sub_cons; auto.
      introv j i.
      apply get_utokens_subst_utokens_subset in i; allsimpl.
      unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
      apply in_remove in i; repnd; tcsp. }
    { unfold get_utokens_sub; simpl; apply disjoint_singleton_l.
      introv i.
      apply get_utokens_subst_utokens_subset in i; allsimpl.
      unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r.
      apply in_remove in i; repnd; tcsp. }
    { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; tcsp. }
    exrepnd.
    allrw @fold_subst.

    pose proof (IHk (subst_utokens u0 [(a, mk_var v)]) v s) as ih.
    rw <- Heqa' in ih.
    repeat (autodimp ih hyp).
    { apply wf_subst_utokens; eauto 3 with slow. }
    exrepnd.
    exists z.
    dands.

    { eapply reduces_to_trans;[|exact ih1].
      apply reduces_to_if_step; auto. }

    { eapply alpha_eq_trans;[exact ih0|].
      apply (alpha_eq_subst_utokens _ _ [(a', mk_var v)] [(a', mk_var v)]) in chu1; eauto 3 with slow.
      eapply alpha_eq_trans;[exact chu1|].
      apply (alpha_eq_subst_utokens _ _ [(a, mk_var v)] [(a, mk_var v)]) in r0; eauto 3 with slow.
      eapply alpha_eq_trans;[|apply alpha_eq_sym; exact r0].
      apply (alpha_eq_subst_utokens _ _ [(a, mk_var v)] [(a, mk_var v)]) in chu0; eauto 3 with slow.
      eapply alpha_eq_trans;[|apply alpha_eq_sym; exact chu0].

      allunfold @get_utokens_sub; allsimpl; allrw disjoint_singleton_l.
      pose proof (simple_alphaeq_subst_utokens_subst w v a') as h1.
      autodimp h1 hyp; tcsp.
      pose proof (simple_alphaeq_subst_utokens_subst w v a) as h2.
      autodimp h2 hyp; tcsp.
      eapply alpha_eq_trans;[exact h1|]; eauto with slow.
    }
Qed.

Lemma reduces_to_change_utok_sub {o} :
  forall lib (t u : @NTerm o) sub sub',
    nt_wf t
    -> reduces_to lib (lsubst t sub) u
    -> nr_ut_sub t sub
    -> nr_ut_sub t sub'
    -> dom_sub sub = dom_sub sub'
    -> disjoint (get_utokens_sub sub) (get_utokens t)
    -> disjoint (get_utokens_sub sub') (get_utokens t)
    -> {w, s : NTerm
        $ alpha_eq u (lsubst w sub)
        # disjoint (get_utokens_sub sub) (get_utokens w)
        # subvars (free_vars w) (free_vars t)
        # subset (get_utokens w) (get_utokens t)
        # reduces_to lib (lsubst t sub') s
        # alpha_eq s (lsubst w sub')}.
Proof.
  introv wf r nrut1 nrut2 eqdoms d1 d2.
  allunfold @reduces_to; exrepnd.
  pose proof (reduces_in_atmost_k_steps_change_utok_sub lib k t u sub sub') as h.
  repeat (autodimp h hyp); exrepnd.
  eexists; eexists; dands; eauto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/")
*** End:
*)
