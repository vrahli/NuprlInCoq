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


Require Export compare_cterm.
Require Export stronger_continuity_rule.



Lemma cequivc_nat_implies {o} :
  forall lib (t : @CTerm o) (n : nat),
    cequivc lib t (mkc_nat n)
    -> computes_to_valc lib t (mkc_nat n).
Proof.
  introv ceq.
  apply cequivc_sym in ceq.
  eapply cequivc_nat in ceq;[eauto|].
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma cequivc_fresh_nat_implies {o} :
  forall lib (v : NVar) (t : CVTerm [v]) (a : get_patom_set o) k,
    !LIn a (getcv_utokens [v] t)
    -> cequivc lib (mkc_fresh v t) (mkc_nat k)
    -> cequivc lib (substc (mkc_utoken a) v t) (mkc_nat k).
Proof.
  introv ni ceq.
  apply cequivc_nat_implies in ceq.
  destruct_cterms.
  unfold computes_to_valc in ceq.
  unfold getcv_utokens in ni.
  unfold cequivc; allsimpl.
  unfold computes_to_value in ceq; repnd.
  pose proof (fresh_reduces_to_implies lib v x (mk_nat k) a) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd.
  apply alpha_eq_mk_nat in h0.
  pose proof (unfold_subst_utokens [(a, mk_var v)] u) as q; exrepnd.
  rw q0 in h0; clear q0.
  allsimpl; allrw disjoint_singleton_r.
  destruct t' as [z|f|op bs]; allsimpl; ginv;[].
  dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv;[].
  destruct can; allsimpl; ginv.
  - destruct bs; allsimpl; ginv; GC.
    unfold mk_nat, mk_integer in h0; ginv; fold_terms.
    apply alpha_eq_sym in q1.
    apply alpha_eq_mk_nat in q1; subst; auto.
    apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; apply subst_preserves_isprog; eauto 2 with slow.
  - unfold subst_utok in h0; allsimpl; boolvar; ginv.
Qed.

Lemma computes_to_valc_implies_hasvalue_likec {o} :
  forall lib (t : @CTerm o) v,
    computes_to_valc lib t v
    -> hasvalue_likec lib t.
Proof.
  introv comp; destruct_cterms.
  unfold computes_to_valc in comp; unfold hasvalue_likec; allsimpl.
  unfold hasvalue_like.
  unfold computes_to_value in comp; repnd.
  eexists; dands; eauto 3 with slow.
Qed.

Lemma alpha_eq_subst_bound2_cbv_alpha_eq {o} :
  forall v z (f : @NTerm o) t n a,
    isprog f
    -> alpha_eq
         (subst (mk_less (mk_var v) mk_zero (mk_vbot z)
                         (mk_less (mk_var v) (mk_nat n) (mk_apply f (mk_var v)) (spexc a)))
                v t)
         (mk_less t mk_zero (mk_vbot z) (mk_less t (mk_nat n) (mk_apply f t) (spexc a))).
Proof.
  introv isp.
  pose proof (unfold_lsubst
                [(v,t)]
                (mk_less (mk_var v) mk_zero (mk_vbot z)
                         (mk_less (mk_var v) (mk_nat n) (mk_apply f (mk_var v)) (spexc a))))
    as unf; exrepnd.
  unfold subst.
  rw unf0; clear unf0.
  allapply @alpha_eq_mk_less; exrepnd; subst.
  allapply @alpha_eq_mk_less; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.
  allapply @continuity_defs_ceq.alpha_eq_mk_vbot; exrepnd; subst.
  allapply @alpha_eq_mk_zero; subst.
  allapply @alpha_eq_mk_apply; exrepnd; subst.
  allapply @alpha_eq_mk_var; subst.
  allapply @alpha_eq_mk_nat; subst.
  allapply @alpha_eq_spexc; subst.

  allsimpl; cpx; ginv.

  allrw app_nil_r.
  allrw disjoint_cons_l.
  repnd.
  rename a' into f'.

  allrw memvar_singleton.
  allrw <- @beq_var_refl.
  rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.

  unfold mk_less, mk_apply, mk_vbot, mk_zero, mk_nat, mk_integer, mk_fix, mk_lam, mk_var, nobnd.
  repeat (prove_alpha_eq4; eauto 2 with slow).

  { pose proof (ex_fresh_var (v' :: z :: [])) as fv.
    exrepnd; allsimpl; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v0]); simpl; auto;
    repeat (boolvar; simpl); tcsp;
    allrw disjoint_singleton_l; allsimpl; tcsp. }
Qed.

Lemma reduces_to_exc_refl {o} :
  forall lib (t : @NTerm o),
    reduces_to_exc lib t t.
Proof.
  introv; unfold reduces_to_exc; exists 0.
  rw @reduces_in_atmost_k_steps_exc_0; auto.
Qed.
Hint Resolve reduces_to_exc_refl : slow.

Lemma implies_reduces_to_exc_spexc {o} :
  forall lib (t : @NTerm o) (a : get_patom_set o) n e,
    computes_to_exception lib n t e
    -> computes_to_value lib n (mk_utoken a)
    -> computes_to_value lib e mk_axiom
    -> reduces_to_exc lib t (spexc a).
Proof.
  introv compt compn compe.
  unfold reduces_to_exc.
  allunfold @computes_to_exception.
  allunfold @computes_to_value; repnd.
  allunfold @reduces_to; exrepnd.
  pose proof (reduces_in_atmost_k_steps_exc_exception
                lib k0 k n e (mk_utoken a) mk_axiom) as q.
  repeat (autodimp q hyp); eauto 3 with slow; exrepnd.
  try (fold (spexc a) in q0).
  pose proof (reduces_in_atmost_k_steps_exc_trans2
                lib k1 i t (mk_exception n e) (spexc a)) as l.
  repeat (autodimp l hyp); exrepnd.
  exists i0; auto.
Qed.

(* !!MOVE to opid *)
Lemma dec_op_eq_try : forall ncan, decidable (ncan = NTryCatch).
Proof.
  introv; unfold decidable.
  destruct ncan; try (complete (right; sp; ginv)); sp.
Qed.

Lemma reduces_to_preserves_hasvalue_like {o} :
  forall lib (t1 t2 : @NTerm o),
    reduces_to lib t1 t2
    -> hasvalue_like lib t1
    -> hasvalue_like lib t2.
Proof.
  introv r hv.
  allunfold @hasvalue_like; exrepnd.
  exists v; dands; eauto 3 with slow.
  unfold reduces_to in hv1; exrepnd.
  eapply reduces_in_atmost_k_steps_if_reduces_to in r;
    [|exact hv2|auto].
  exrepnd.
  exists k'; auto.
Qed.

Lemma differ_force_pk2term {o} :
  forall b a f (pk : @param_kind o) t,
    differ_force b a f (pk2term pk) t
    -> (t = pk2term pk # !LIn a (get_utokens_pk pk)).
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len1 len2 nia imp];
    subst; allsimpl; clear d; GC; tcsp; ginv;
    allrw @pk2term_eq; ginv.
  allsimpl; cpx.
  allrw @get_utokens_c_pk2can; tcsp.
Qed.

Lemma differ_force_alpha_pk2term {o} :
  forall b a f (pk : @param_kind o) t,
    differ_force_alpha b a f (pk2term pk) t
    -> (t = pk2term pk # !LIn a (get_utokens_pk pk)).
Proof.
  introv d.
  unfold differ_force_alpha in d; exrepnd.
  allapply @alpha_eq_pk2term; subst.
  allapply @differ_force_pk2term; repnd; subst.
  apply alpha_eq_sym in d2; apply alpha_eq_pk2term in d2.
  subst; tcsp.
Qed.

Lemma differ_force_exception {o} :
  forall b a f (n e t : @NTerm o),
    differ_force b a f (mk_exception n e) t
    -> {n1 : NTerm
        & {e1 : NTerm
        & t = mk_exception n1 e1
        # differ_force b a f n n1
        # differ_force b a f e e1}}.
Proof.
  introv d.
  inversion d as [|?|?|? ? ? len nia imp]; subst; tcsp.
  allsimpl; cpx; GC; allsimpl.
  pose proof (imp (nobnd n) x) as h1; autodimp h1 hyp.
  pose proof (imp (nobnd e) y) as h2; autodimp h2 hyp.
  clear imp.
  inversion h1 as [? ? ? ? d1]; subst; clear h1.
  inversion h2 as [? ? ? ? d2]; subst; clear h2.
  fold_terms.
  eexists; eexists; dands; eauto.
Qed.

Lemma differ_force_alpha_exception {o} :
  forall b a f (n e t : @NTerm o),
    differ_force_alpha b a f (mk_exception n e) t
    -> {n1 : NTerm
        & {e1 : NTerm
        & t = mk_exception n1 e1
        # differ_force_alpha b a f n n1
        # differ_force_alpha b a f e e1}}.
Proof.
  introv d.
  unfold differ_force_alpha in d; exrepnd.
  allapply @alpha_eq_exception; exrepnd; subst.
  allapply @differ_force_exception; exrepnd; subst.
  apply alpha_eq_sym in d2; apply alpha_eq_exception in d2.
  exrepnd; subst.
  eexists; eexists; dands; auto.
  - exists a' n1; dands; eauto 3 with slow.
  - exists e' e1; dands; eauto 3 with slow.
Qed.

Lemma implies_differ_force_alpha_exception {o} :
  forall b a f (n1 n2 e1 e2 : @NTerm o),
    differ_force_alpha b a f n1 n2
    -> differ_force_alpha b a f e1 e2
    -> differ_force_alpha
         b a f
         (mk_exception n1 e1)
         (mk_exception n2 e2).
Proof.
  introv d1 d2.
  allunfold @differ_force_alpha; exrepnd.
  exists (mk_exception u0 u1) (mk_exception u3 u2).
  dands; eauto 3 with slow; try (apply implies_alphaeq_exception; auto).
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; auto.
Qed.

Lemma if_has_value_like_k_ncompop_fst {o} :
  forall lib c k (t u : @NTerm o) a b,
    wf_term t
    -> wf_term u
    -> wf_term a
    -> wf_term b
    -> has_value_like_k
         lib k
         (oterm (NCan (NCompOp c)) [nobnd t, nobnd u, nobnd a, nobnd b])
    -> {j : nat
        & {t' : NTerm
        & j < k
        # reduces_in_atmost_k_steps lib t t' j
        # (ispk t' [+] isexc t')}}.
Proof.
  introv wft wfu wfa wfb hv.
  unfold has_value_like_k in hv; exrepnd.
  apply computes_to_val_like_in_max_k_steps_comp_implies in hv0; auto;[].
  repndors; exrepnd; subst.

  - exists k1 (pk2term pk1); dands; eauto 3 with slow; try omega.

  - exists k1 (mk_exception en e); dands; eauto 3 with slow; try omega.

  - exists k1 (pk2term pk); dands; eauto 3 with slow; try omega.
Qed.

Definition ex_spfexc {o} a (t : @NTerm o) :=
  {vs1 : list NVar
   & {vs2 : list NVar
   & t = spfexc vs1 vs2 a }}.

Lemma ex_spfexc_spexc {o} :
  forall (a : get_patom_set o), ex_spfexc a (spexc a).
Proof.
  introv.
  exists ([] : list NVar) ([] : list NVar); auto.
Qed.
Hint Resolve ex_spfexc_spexc : slow.

Lemma ex_spfexc_spfexc {o} :
  forall vs1 vs2 (a : get_patom_set o), ex_spfexc a (spfexc vs1 vs2 a).
Proof.
  introv.
  exists vs1 vs2; auto.
Qed.
Hint Resolve ex_spfexc_spfexc : slow.

Lemma ex_spfexc_subst_utokens_aux {o} :
  forall a (t : @NTerm o) sub,
    !LIn a (utok_sub_dom sub)
    -> ex_spfexc a t
    -> ex_spfexc a (subst_utokens_aux t sub).
Proof.
  introv nia exs.
  allunfold @ex_spfexc; exrepnd; subst.
  unfold spfexc; simpl.
  allrw @subst_utokens_aux_lfresh.
  simpl.
  unfold subst_utok; simpl.
  remember (utok_sub_find sub a) as sf; destruct sf; symmetry in Heqsf.
  { apply utok_sub_find_some in Heqsf.
    apply in_utok_sub_eta in Heqsf; sp. }
  fold_terms.
  eexists; eexists; eauto.
Qed.

Lemma alpha_eq_spfexc_implies {o} :
  forall vs1 vs2 a (t : @NTerm o),
    alpha_eq (spfexc vs1 vs2 a) t
    -> {vs3 : list NVar
        & {vs4 : list NVar
        & t = spfexc vs3 vs4 a
        # length vs1 = length vs3
        # length vs2 = length vs4 }}.
Proof.
  introv aeq.
  allunfold @spfexc.
  apply alpha_eq_exception in aeq; exrepnd; subst.
  apply alpha_eq_lfresh_implies in aeq1; eauto 3 with slow; exrepnd; subst.
  apply alpha_eq_lfresh_implies in aeq2; eauto 3 with slow; exrepnd; subst.
  allapply @alpha_eq_mk_axiom; subst.
  allapply @alpha_eq_mk_utoken; subst.
  eexists; eexists; dands; eauto.
Qed.

Lemma ex_spfexc_subst_utokens {o} :
  forall a (t : @NTerm o) sub,
    !LIn a (utok_sub_dom sub)
    -> ex_spfexc a t
    -> ex_spfexc a (subst_utokens t sub).
Proof.
  introv nia exs.
  allunfold @ex_spfexc; exrepnd; subst.
  pose proof (unfold_subst_utokens sub (spfexc vs1 vs2 a)) as h.
  exrepnd.
  rw h0.
  apply alpha_eq_spfexc_implies in h1; exrepnd; subst.
  unfold spfexc; simpl.
  allrw @subst_utokens_aux_lfresh.
  simpl.
  unfold subst_utok; simpl.
  remember (utok_sub_find sub a) as sf; destruct sf; symmetry in Heqsf.
  { apply utok_sub_find_some in Heqsf.
    apply in_utok_sub_eta in Heqsf; sp. }
  fold_terms.
  eexists; eexists; eauto.
Qed.

Lemma ex_spfexc_alpha_eq {o} :
  forall a (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> ex_spfexc a t1
    -> ex_spfexc a t2.
Proof.
  introv aeq exspf.
  allunfold @ex_spfexc; exrepnd; subst.
  allapply @alpha_eq_spfexc_implies; exrepnd; subst.
  eexists; eexists; eauto.
Qed.

Lemma eapply_red_lam_exception_implies {o} :
  forall lib (t : @NTerm o) v b a n e,
    reduces_to lib t (mk_lam v b)
    -> (a =e>(n,lib) e)
    -> ((mk_eapply t a) =e>(n,lib) e).
Proof.
  introv comp1 comp2.
  unfold computes_to_value in comp1; repnd.
  allunfold @computes_to_exception.
  eapply reduces_to_trans;
    [apply implies_eapply_red;[|eauto|eauto] |];
    eauto 3 with slow.
Qed.

Lemma computation_step_differ_force2 {o} :
  forall lib (t1 t2 : @NTerm o) b a u f k,
    isprog f
    -> wf_term t1
    -> wf_term t2
    -> !LIn a (get_utokens f)
    -> differ_force b a f t1 t2
    -> compute_step lib t1 = csuccess u
    -> has_value_like_k lib k u
    -> hasvalue_like lib t2
    -> (forall t1 t2 v m, (* induction hypothesis *)
          m < S k
          -> wf_term t1
          -> wf_term t2
          -> isvalue_like v
          -> reduces_in_atmost_k_steps lib t1 v m
          -> hasvalue_like lib t2
          -> differ_force b a f t1 t2
          -> {v2 : NTerm
              & reduces_to lib t2 v2
              # (differ_force_alpha b a f v v2 [+] ex_spfexc a v2)})
    -> {t1' : NTerm
        & {t2' : NTerm
        & reduces_to lib u t1'
        # reduces_to lib t2 t2'
        # (differ_force_alpha b a f t1' t2'
           [+] ex_spfexc a t2' (*reduces_to_exc lib t2' (spexc a)*))}}.
Proof.
  nterm_ind1s t1 as [v1|f1 ind1|op1 bs1 ind1] Case;
  introv ispf wft1 wft2 niaf d comp hv hvt2 indhyp.

  - Case "vterm".
    simpl.
    inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.
    inversion d as [|?|?|]; subst;[]; clear d.
    exists (sterm f1) (sterm f1); dands; eauto 3 with slow.

  - Case "oterm".
    assert (forall (t1 t2 v : NTerm) (m : nat),
              m < S k
              -> wf_term t1
              -> wf_term t2
              -> isvalue_like v
              -> reduces_in_atmost_k_steps lib t1 v m
              -> hasvalue_like lib t2
              -> differ_force_alpha b a f t1 t2
              -> {v2 : NTerm
                  $ reduces_to lib t2 v2
                  # (differ_force_alpha b a f v v2 [+] ex_spfexc a v2)}) as indhyp'.
    { introv x w1 w2 isv r hv' d'.
      unfold differ_force_alpha in d'; exrepnd.
      eapply reduces_in_atmost_k_steps_alpha in r;[| |exact d'0]; exrepnd; eauto 2 with slow;[].
      eapply continuity2_2.alphaeq_preserves_hasvalue_like in hv';[| |exact d'2]; eauto 2 with slow;[].
      apply (indhyp _ _ t2' m) in d'1; eauto 2 with slow.
      exrepnd.
      applydup @alphaeq_preserves_wf_term in d'2 as wfu2; auto;[].
      eapply reduces_to_alpha in d'1;[| |apply alpha_eq_sym; exact d'2]; eauto 2 with slow;[].
      exrepnd.
      eexists; dands; eauto.
      allunfold @differ_force_alpha; exrepnd.
      repndors; exrepnd.
      { left; exists u0 u3; dands; eauto 3 with slow. }
      { right.
        eapply ex_spfexc_alpha_eq;[exact d'4|]; auto.
      }
    }
    clear indhyp; rename indhyp' into indhyp.

    dopid op1 as [can|ncan|exc|abs] SCase; ginv.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      inversion d; subst.
      exists (oterm (Can can) bs1) (oterm (Can can) bs2); dands; eauto with slow.

    + SCase "NCan".
      destruct bs1 as [|b1 bs1]; try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (simpl in comp; ginv)).

      { (* Non fresh case *)

        destruct t1 as [v1|f1|op1 bs1'].

        - destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d)).
          inversion d as [|?|?|?]; subst; simphyps; cpx; ginv.

        - (* sequence case *)
          destruct t2 as [v2|f2|op2 bs2];
          try (complete (inversion d));[].

          csunf comp; allsimpl.

          dopid_noncan ncan SSCase; allsimpl; ginv.

          { SSCase "NApply".
            clear ind1.
            apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl;[].

            inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
            cpx; ginv; allsimpl; GC.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd arg) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3; subst; clear d3.

            fold_terms.

            exists (mk_eapply (sterm f1) arg)
                   (mk_eapply (sterm f1) t0).
            dands; eauto 3 with slow.
            left; apply implies_differ_force_alpha_eapply; eauto 3 with slow.
          }

          { SSCase "NEApply".
            apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl;[].

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].

            rw @wf_term_eq in wft1; rw @nt_wf_eapply_iff in wft1; exrepnd; allunfold @nobnd; ginv.
            simpl in len1; cpx.
            simpl in imp.
            fold_terms.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? d3]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [|?|?|]; subst; clear d3;[].
            fold_terms.

            repndors; exrepnd; subst.

            - apply compute_step_eapply2_success in comp1; repnd; GC.
              repndors; exrepnd; subst; ginv; allsimpl; GC.
              inversion d4 as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d4; GC;[].
              cpx; clear imp; fold_terms.

              exists (f0 n) (f0 n); dands; eauto 3 with slow.

              { apply reduces_to_if_step.
                csunf; simpl.
                dcwf h; simpl; boolvar; try omega.
                rw @Znat.Nat2Z.id; auto. }

              { left; apply differ_force_alpha_refl; auto.
                allrw @nt_wf_sterm_iff.
                pose proof (wft3 n) as h; clear wft3; repnd.
                rw h; simpl; tcsp. }

            - apply isexc_implies2 in comp0; exrepnd; subst.
              inversion d4 as [|?|?|?]; subst; allsimpl; clear d4.
              exists (oterm Exc l) (oterm Exc bs2); dands; eauto 3 with slow.
              left; eauto 3 with slow.

            - pose proof (ind1 b0 b0 []) as h; clear ind1.
              repeat (autodimp h hyp); eauto 3 with slow;[].
              allrw <- @wf_eapply_iff; repnd.

              applydup @preserve_nt_wf_compute_step in comp1; auto.
              applydup @has_value_k_like_eapply_sterm_implies in hv; exrepnd; auto;[].
              applydup @hasvalue_like_eapply_sterm_implies in hvt2; eauto 3 with slow;[].

              pose proof (h t0 b a x f k) as ih; clear h.
              allsimpl; autorewrite with slow in *.
              repeat (autodimp ih hyp); eauto 3 with slow.
              { eapply has_value_like_k_lt; eauto. }
              exrepnd.

              repndors.

              { exists (mk_eapply (sterm f1) t1')
                       (mk_eapply (sterm f1) t2').
                dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { left; apply implies_differ_force_alpha_eapply; eauto 3 with slow. }
              }

              { exists (mk_eapply (sterm f1) x) t2'; dands; eauto 3 with slow.
                unfold ex_spfexc in ih1; exrepnd; subst.
                allunfold @spfexc.
                eapply eapply_sterm_exception_implies; eauto. }
          }

          { SSCase "NFix".
            apply compute_step_fix_success in comp; repnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.
            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? d2]; subst; clear d1.
            inversion d2 as [|?|?|]; subst; clear d2.
            fold_terms.

            exists (mk_apply (sterm f1) (mk_fix (sterm f1)))
                   (mk_apply (sterm f1) (mk_fix (sterm f1))).
            dands; eauto 3 with slow.
            left; apply differ_force_alpha_refl; simpl; tcsp.
          }

          { SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.

            inversion d as [? ? ? ? ? aeq1 d1|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[|].

            { inversion d1; subst; clear d1;[].
              apply has_value_like_k_subst_less_seq in hv; sp. }

            { cpx; allsimpl.
              autorewrite with slow in *.

              pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
              pose proof (imp (bterm [v] x) y) as d2; autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d3; subst; clear d3.
              inversion d2 as [? ? ? d4]; subst; clear d2.
              fold_terms.

              exists (subst x v (sterm f1))
                     (subst t2 v (sterm f1)).
              dands; eauto 3 with slow.
              left; apply differ_force_subst; auto. }
          }

          { SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.

            pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd a0) y) as d2; autodimp d2 hyp.
            pose proof (imp (bterm [v] x) z) as d3; autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d]; subst; clear d1.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [? ? ? d5]; subst; clear d3.

            allrw <- @wf_try_iff; repnd.

            inversion d as [?|?|?|? ? ? len1 nia imp1]; subst; allsimpl; clear d; GC;[].

            exists (mk_atom_eq a0 a0 (sterm f1) mk_bot)
                   (mk_atom_eq t0 t0 (sterm f1) mk_bot);
              dands; eauto 3 with slow.
            left; apply differ_force_implies_differ_force_alpha.
            apply differ_force_oterm; simpl; tcsp.
            introv j; repndors; tcsp; ginv; constructor; eauto 2 with slow.
            apply differ_force_refl; simpl; tcsp.
          }

          { SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.

            inversion d as [|?|?|? ? ? len1 nia imp]; subst; allsimpl; clear d; GC;[].
            cpx; allsimpl; fold_terms.

            pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd a0) y) as d2; autodimp d2 hyp.
            pose proof (imp (nobnd b0) z) as d3; autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? d4]; subst; clear d1.
            inversion d4; subst; clear d4.
            inversion d2 as [? ? ? d4]; subst; clear d2.
            inversion d3 as [? ? ? d5]; subst; clear d3.
            fold_terms.

            exists b0 t0.
            dands; eauto 3 with slow.
          }

        - (* Now destruct op1 *)
          dopid op1 as [can1|ncan1|exc1|abs1] SSCase; ginv.

          + SSCase "Can".
            allsimpl.

            (* Because the principal argument is canonical we can destruct ncan *)
            dopid_noncan ncan SSSCase.

            * SSSCase "NApply".

              clear ind1 indhyp.
              csunf comp; allsimpl.
              apply compute_step_apply_success in comp; repndors; exrepnd; subst.

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; GC.

                pose proof (imp (bterm [] (oterm (Can NLambda) [bterm [v] b0])) x) as d1.
                autodimp d1 hyp;[].
                pose proof (imp (bterm [] arg) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                repeat (allsimpl; cpx).

                pose proof (imp1 (bterm [v] b0) x) as d1; clear imp1.
                autodimp d1 hyp.

                inversion d1 as [? ? ? d2]; subst; clear d1.

                exists (subst b0 v arg) (subst t2 v t0); dands; eauto 3 with slow.
                left; apply differ_force_subst; auto.
              }

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; GC; fold_terms.

                pose proof (imp (nobnd (mk_nseq f0)) x) as d1.
                autodimp d1 hyp;[].
                pose proof (imp (nobnd arg) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                repeat (allsimpl; cpx; GC).
                fold_terms.
                clear imp1.

                exists (mk_eapply (mk_nseq f0) arg) (mk_eapply (mk_nseq f0) t0); dands; eauto 3 with slow.

                left.
                apply differ_force_implies_differ_force_alpha.
                apply differ_force_oterm; simpl; tcsp.
                introv j; repndors; tcsp; ginv; constructor; auto.
                apply differ_force_refl; simpl; tcsp.
              }

            * SSSCase "NEApply".
              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp; exrepnd; subst.
              rw @wf_term_eq in wft1; rw @nt_wf_eapply_iff in wft1; exrepnd; allunfold @nobnd; ginv.

              inversion d as [?|?|?|? ? ? len1 nia imp1]; subst; clear d; GC;[].
              simpl in len1; cpx; simpl in imp1.

              pose proof (imp1 (nobnd (oterm (Can can1) bs1')) x) as d1; autodimp d1 hyp.
              pose proof (imp1 (nobnd b0) y) as d2; autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.
              fold_terms.
              allrw <- @wf_eapply_iff; repnd.
              apply eapply_wf_def_oterm_implies in comp2; exrepnd; ginv; fold_terms.

              destruct comp2 as [comp2|comp2]; exrepnd; subst; ginv; fold_terms.

              { apply differ_force_lam_implies in d3; exrepnd; subst; fold_terms.

                { repndors; exrepnd; subst.

                  + apply compute_step_eapply2_success in comp1; repnd; GC.
                    repndors; exrepnd; subst; ginv; allsimpl; GC.
                    allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                    applydup @differ_force_preserves_iscan in d4; auto.
                    autorewrite with slow in *.

                    { exists (subst b1 v0 b0)
                             (subst u1 v0 t0).
                      dands; eauto 3 with slow.
                      { apply eapply_lam_can_implies.
                        unfold computes_to_can; dands; eauto 3 with slow. }
                      left; apply differ_force_subst; auto.
                    }

                  + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                    apply differ_force_exception in d4; exrepnd; subst;[].

                    exists (mk_exception a0 e)
                           (mk_exception n1 e1).
                    dands; eauto 3 with slow.
                    left; apply implies_differ_force_alpha_exception; eauto 3 with slow.

                  + allsimpl; autorewrite with slow in *.
                    pose proof (ind1 b0 b0 []) as h; clear ind1.
                    repeat (autodimp h hyp); eauto 3 with slow.

                    applydup @preserve_nt_wf_compute_step in comp1; auto.
                    applydup @has_value_like_k_eapply_lam_implies in hv; exrepnd; auto;[].
                    applydup @hasvalue_like_eapply_lam_implies in hvt2; eauto 3 with slow;[].

                    pose proof (h t0 b a x f k) as ih; clear h.
                    repeat (autodimp ih hyp); eauto 3 with slow.
                    { eapply has_value_like_k_lt; eauto. }
                    exrepnd.

                    repndors.

                    { exists (mk_eapply (mk_lam v t) t1')
                             (mk_eapply (mk_lam v u1) t2').
                      dands; eauto 3 with slow.
                      { apply implies_eapply_red_aux; eauto 3 with slow. }
                      { apply implies_eapply_red_aux; eauto 3 with slow. }
                      { left; apply differ_force_alpha_mk_eapply; eauto 3 with slow.
                        apply differ_force_alpha_mk_lam; eauto 3 with slow. }
                    }

                    { exists (mk_eapply (mk_lam v t) x) t2'; dands; eauto 3 with slow.
                      unfold ex_spfexc in ih1; exrepnd; subst.
                      allunfold @spfexc.
                      eapply eapply_red_lam_exception_implies; try (exact ih2).
                      apply reduces_to_symm. }
                }
              }

              { apply differ_force_nseq_implies in d3; exrepnd; subst; fold_terms.

                { repndors; exrepnd; subst.

                  + apply compute_step_eapply2_success in comp1; repnd; GC.
                    repndors; exrepnd; subst; ginv; allsimpl; GC;[].
                    allapply @differ_force_nat_implies; subst.

                    { exists (@mk_nat o (f0 n))
                             (@mk_nat o (f0 n)).
                      dands; eauto 3 with slow.
                      { apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
                        boolvar; try omega; rw @Znat.Nat2Z.id; auto. }
                      left; apply differ_force_alpha_refl; simpl; tcsp.
                    }

                  + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl; eauto 3 with slow;[].
                    apply differ_force_exception in d4; exrepnd; subst;[].

                    exists (mk_exception a0 e)
                           (mk_exception n1 e1).
                    dands; eauto 3 with slow.
                    left; apply implies_differ_force_alpha_exception; eauto 3 with slow.

                  + allsimpl; autorewrite with slow in *.
                    pose proof (ind1 b0 b0 []) as h; clear ind1.
                    repeat (autodimp h hyp); eauto 3 with slow.

                    applydup @preserve_nt_wf_compute_step in comp1; auto.
                    applydup @has_value_like_k_eapply_nseq_implies in hv; exrepnd; auto;[].
                    applydup @hasvalue_like_eapply_nseq_implies in hvt2; eauto 3 with slow;[].

                    pose proof (h t0 b a x f k) as ih; clear h.
                    repeat (autodimp ih hyp); eauto 3 with slow.
                    { eapply has_value_like_k_lt; eauto. }
                    exrepnd.

                    repndors.

                    { exists (mk_eapply (mk_nseq s) t1')
                             (mk_eapply (mk_nseq s) t2').
                      dands; eauto 3 with slow.
                      { apply implies_eapply_red_aux; eauto 3 with slow. }
                      { apply implies_eapply_red_aux; eauto 3 with slow. }
                      { left; apply differ_force_alpha_mk_eapply; eauto 3 with slow. }
                    }

                    { exists (mk_eapply (mk_nseq s) x) t2'; dands; eauto 3 with slow.
                      unfold ex_spfexc in ih1; exrepnd; subst.
                      allunfold @spfexc.
                      eapply reduces_to_trans;
                        [apply implies_eapply_red_aux;[|eauto] |]; eauto 3 with slow. }
                }
              }

(*            * SSSCase "NApseq".

              clear ind1 indhyp.
              csunf comp; allsimpl.
              apply compute_step_apseq_success in comp; repndors; exrepnd; subst.

              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.
              fold_terms.

              pose proof (imp (nobnd (mk_nat n0)) x) as d1.
              autodimp d1 hyp;[].
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx; GC).
              clear imp1.
              fold_terms.

              exists (@mk_nat o (n n0)) (@mk_nat o (n n0)); dands; eauto 3 with slow.

              { apply reduces_to_if_step; csunf; simpl.
                rw @Znat.Nat2Z.id.
                boolvar; try omega; auto. }

              { left.
                apply differ_force_implies_differ_force_alpha.
                apply differ_force_oterm; simpl; tcsp. } *)

            * SSSCase "NFix".
              csunf comp; allsimpl.
              apply compute_step_fix_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.

              pose proof (imp (bterm [] (oterm (Can can1) bs1')) x) as d1.
              autodimp d1 hyp;[].
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).

              exists (mk_apply (oterm (Can can1) bs1') (mk_fix (oterm (Can can1) bs1')))
                     (mk_apply (oterm (Can can1) bs2) (mk_fix (oterm (Can can1) bs2)));
                dands; eauto 3 with slow.

              left.
              apply differ_force_implies_differ_force_alpha.
              apply differ_force_oterm; simpl; tcsp.
              introv j; repndors; tcsp; ginv; constructor; auto.
              apply differ_force_oterm; simpl; tcsp.
              introv j; repndors; tcsp; ginv; constructor; auto.

            * SSSCase "NSpread".
              csunf comp; allsimpl.
              apply compute_step_spread_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can NPair) [nobnd a0, nobnd b0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [va,vb] arg) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd a0) x) as d1.
              autodimp d1 hyp;[].
              pose proof (imp1 (nobnd b0) y) as d2.
              autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              exists (lsubst arg [(va,a0),(vb,b0)])
                     (lsubst t0 [(va,t2),(vb,t3)]); dands; eauto 3 with slow.
              left; apply differ_force_subst; auto.

            * SSSCase "NDsup".
              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.

              pose proof (imp (bterm [] (oterm (Can NSup) [nobnd a0, nobnd b0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [va,vb] arg) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd a0) x) as d1.
              autodimp d1 hyp.
              pose proof (imp1 (nobnd b0) y) as d2.
              autodimp d2 hyp.
              clear imp1.

              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              exists (lsubst arg [(va,a0),(vb,b0)])
                     (lsubst t0 [(va,t2),(vb,t3)]); dands; eauto 3 with slow.
              left.
              apply differ_force_subst; auto.

            * SSSCase "NDecide".
              csunf comp; allsimpl.
              apply compute_step_decide_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.

              pose proof (imp (bterm [] (oterm (Can can1) [nobnd d0])) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v1] t1) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (bterm [v2] t0) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              pose proof (imp1 (nobnd d0) x) as d1.
              autodimp d1 hyp.
              clear imp1.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              repndors; repnd; subst.

              { exists (lsubst t1 [(v1,d0)])
                       (lsubst t4 [(v1,t3)]);
                dands; eauto 3 with slow.
                left; eauto 3 with slow. }

              { exists (lsubst t0 [(v2,d0)])
                       (lsubst t5 [(v2,t3)]);
                dands; eauto 3 with slow.
                left; eauto 3 with slow. }

            * SSSCase "NCbv".
              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp; exrepnd; subst.
              inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

              { (* force case *)
                inversion d' as [|?|?|? ? ? len nia imp]; subst.
                applydup @alpha_eq_preserves_isprog in aeq;auto;[].

                allrw <- @wf_cbv_iff; repnd.

                eapply alphaeq_preserves_has_value_like_k in hv;
                  [| |apply alpha_eq_subst_sp_force_nat_alpha_eq;auto];
                  [|apply nt_wf_subst; eauto 3 with slow];[].

                fold_terms.

                applydup @has_value_like_k_mk_less in hv; eauto 3 with slow;
                try (apply wf_less; eauto 3 with slow);[].

                repndors; exrepnd.

                - apply computes_to_exception_in_max_k_steps_can in hv2; sp.

                - apply computes_to_exception_in_max_k_steps_can in hv3; sp.

                - allunfold @computes_to_can; repnd.
                  apply reduces_in_atmost_k_steps_if_isvalue_like in hv2; eauto 3 with slow;
                    unfold mk_integer in hv2; ginv;[].
                  allsimpl; cpx; GC; fold_terms.
                  unfold mk_zero, mk_nat in hv3.
                  apply reduces_in_atmost_k_steps_if_isvalue_like in hv3; eauto 3 with slow; ginv.
                  fold_terms.

                  clear d' imp.

                  boolvar; tcsp; try (complete (allapply @has_value_like_k_vbot; tcsp));[].

                  pose proof (Wf_Z.Z_of_nat_complete_inf i1) as hi1;
                    autodimp hi1 hyp; exrepnd; subst; fold_terms.

                  destruct (nat_compare_dec b n) as [d|d].

                  + exists (mk_apply f' (mk_nat n)) (mk_apply f' (mk_nat n)).
                    dands; eauto 3 with slow.

                    * unfsubst; simpl; allrw memvar_singleton.
                      allrw <- @beq_var_refl; fold_terms.
                      rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.
                      apply reduces_to_if_step; csunf; simpl.
                      dcwf h; simpl;[].
                      unfold compute_step_comp; simpl.
                      boolvar; tcsp; try omega.

                    * unfold bound2_cbv.
                      eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      unfold apply_bterm; simpl; fold_terms.
                      unflsubst; simpl.
                      allrw <- @beq_var_refl; fold_terms.
                      allrw memvar_singleton.
                      rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.
                      eapply reduces_to_if_split2;
                        [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].

                      match goal with
                        | [ |- context[mk_lam ?v ?t ] ] => remember (mk_lam v t) as xx; clear Heqxx
                      end.

                      boolvar; tcsp; try omega; GC.

                      apply reduces_to_if_step; csunf; simpl.
                      dcwf hh; simpl;[].
                      unfold compute_step_comp; simpl.
                      boolvar; tcsp; try omega.

                    * left.
                      apply differ_force_implies_differ_force_alpha.
                      apply differ_force_refl; simpl; rw app_nil_r.
                      apply alphaeq_preserves_utokens in aeq; rw <- aeq; auto.

                  + exists (subst (mk_less (mk_var v) mk_zero (mk_vbot z)
                                           (mk_apply f' (mk_var v)))
                                  v (mk_nat n))
                           (spexc a).
                    dands; eauto 3 with slow.

                    unfold bound2_cbv.
                    eapply reduces_to_if_split2;[csunf;simpl;auto|].
                    unfold apply_bterm; simpl; fold_terms.
                    unflsubst; simpl.
                    allrw <- @beq_var_refl; fold_terms.
                    allrw memvar_singleton.
                    rw (@lsubst_aux_trivial_cl_term2 o f'); eauto 3 with slow.
                    eapply reduces_to_if_split2;
                      [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].

                    match goal with
                      | [ |- context[mk_lam ?v ?t ] ] => remember (mk_lam v t) as xx; clear Heqxx
                    end.

                    boolvar; tcsp; try omega; GC.

                    apply reduces_to_if_step; csunf; simpl.
                    dcwf hh; simpl;[].
                    unfold compute_step_comp; simpl.
                    boolvar; tcsp; try omega.
              }

              (* non force case *)

              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can can1) bs1')) x0) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v] x) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
              repeat (allsimpl; cpx).

              exists (lsubst x [(v,oterm (Can can1) bs1')])
                     (lsubst t0 [(v,oterm (Can can1) bs2)]);
                dands; eauto 3 with slow.
              left.
              apply differ_force_subst; auto.

            * SSSCase "NSleep".
              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms; GC.

              pose proof (imp (nobnd (mk_integer z)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.

            * SSSCase "NTUni".
              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms; GC.

              pose proof (imp (nobnd (mk_nat n)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_uni o n) (@mk_uni o n); dands; eauto 3 with slow.
              { apply reduces_to_if_step; csunf; simpl.
                unfold compute_step_tuni; simpl; boolvar; tcsp; try omega.
                rw Znat.Nat2Z.id; auto. }

            * SSSCase "NMinus".
              csunf comp; allsimpl.
              apply compute_step_minus_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms; GC.

              pose proof (imp (nobnd (mk_integer z)) x) as d1.
              autodimp d1 hyp.
              clear imp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              clear imp1.
              fold_terms.

              exists (@mk_integer o (- z)) (@mk_integer o (- z)); dands; eauto 3 with slow.

            * SSSCase "NFresh".
              csunf comp; allsimpl; ginv.

            * SSSCase "NTryCatch".
              csunf comp; allsimpl.
              apply compute_step_try_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) x0) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd a0) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (bterm [v] x) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              exists (mk_atom_eq a0 a0 (oterm (Can can1) bs1') mk_bot)
                     (mk_atom_eq t0 t0 (oterm (Can can1) bs2) mk_bot);
                dands; eauto 3 with slow.

              left.

              apply differ_force_implies_differ_force_alpha.
              apply differ_force_oterm; simpl; tcsp.
              introv j; repndors; tcsp; ginv; constructor; eauto 2 with slow.
              apply differ_force_refl; simpl; tcsp.

            * SSSCase "NParallel".
              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; fold_terms; GC.
              destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) b2) as d1.
              autodimp d1 hyp.

              inversion d1 as [? ? ? d2]; subst; clear d1.

              inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].
              repeat (allsimpl; cpx).
              fold_terms.

              exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.
              left; eauto 3 with slow.
              apply differ_force_implies_differ_force_alpha.
              apply differ_force_refl; simpl; tcsp.

            * SSSCase "NCompOp".
              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; subst; allsimpl;[|idtac|].

              { apply compute_step_compop_success_can_can in comp1;
                exrepnd; subst; allsimpl; ginv; GC.

                repndors; exrepnd; subst; allrw @get_param_from_cop_some; subst;
                allsimpl; fold_terms; allrw <- @pk2term_eq.

                - inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                  cpx; allsimpl; fold_terms; GC.

                  pose proof (imp (nobnd (mk_integer n1)) x) as d1.
                  autodimp d1 hyp.
                  pose proof (imp (nobnd (mk_integer n2)) y) as d2.
                  autodimp d2 hyp.
                  pose proof (imp (nobnd t3) z) as d3.
                  autodimp d3 hyp.
                  pose proof (imp (nobnd t4) u) as d4.
                  autodimp d4 hyp.
                  clear imp.

                  inversion d1 as [? ? ? d5]; subst; clear d1.
                  inversion d2 as [? ? ? d6]; subst; clear d2.
                  inversion d3 as [? ? ? d7]; subst; clear d3.
                  inversion d4 as [? ? ? d8]; subst; clear d4.

                  inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].
                  inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].
                  repeat (allsimpl; cpx).
                  clear imp1 imp2.
                  fold_terms.

                  exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                         (if Z_lt_le_dec n1 n2 then t5 else t6);
                    dands; eauto 3 with slow.
                  boolvar; eauto 3 with slow.

                - inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                  cpx; allsimpl; fold_terms.

                  pose proof (imp (nobnd (pk2term pk1)) x) as d1.
                  autodimp d1 hyp.
                  pose proof (imp (nobnd (pk2term pk2)) y) as d2.
                  autodimp d2 hyp.
                  pose proof (imp (nobnd t3) z) as d3.
                  autodimp d3 hyp.
                  pose proof (imp (nobnd t4) u) as d4.
                  autodimp d4 hyp.
                  clear imp.

                  inversion d1 as [? ? ? d5]; subst; clear d1.
                  inversion d2 as [? ? ? d6]; subst; clear d2.
                  inversion d3 as [? ? ? d7]; subst; clear d3.
                  inversion d4 as [? ? ? d8]; subst; clear d4.

                  allrw @pk2term_eq.
                  inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].
                  inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].
                  repeat (allsimpl; cpx).
                  clear imp1 imp2.
                  fold_terms.
                  allrw <- @pk2term_eq.

                  exists (if param_kind_deq pk1 pk2 then t3 else t4)
                         (if param_kind_deq pk1 pk2 then t5 else t6);
                    dands; eauto 3 with slow.
                  { apply reduces_to_if_step; csunf; simpl;
                    allrw @pk2term_eq; allsimpl.
                    dcwf h; allsimpl.
                    unfold compute_step_comp; allsimpl.
                    allrw @get_param_from_cop_pk2can; auto. }

                  boolvar; eauto 3 with slow.
              }

              { apply if_has_value_like_k_ncompop_can1 in hv; exrepnd.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                destruct bs2 as [|b1 bs2];allsimpl;ginv;[].
                destruct bs2 as [|b2 bs2];allsimpl;ginv;[].

                pose proof (imp (nobnd (oterm (Can can1) bs1')) b1) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) b2) as d2.
                autodimp d2 hyp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                pose proof (ind1 t t []) as h; clear ind1.
                repeat (autodimp h hyp);eauto 3 with slow;[].
                pose proof (h t0 b a t' f j) as q; clear h.

                allrw @wf_term_ncompop_iff; exrepnd; allsimpl; ginv.
                allsimpl.

                pose proof (imp (nobnd c0) (nobnd c1)) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd d) (nobnd d0)) as d2.
                autodimp d2 hyp.

                inversion d1 as [? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? d6]; subst; clear d2.

                applydup @if_hasvalue_like_ncompop_can1 in hvt2.

                repeat (autodimp q hyp).
                { introv l w1 w2 isv r hv' d'.
                  apply (indhyp t1 t2 v m); eauto 3 with slow; try omega. }
                exrepnd.

                assert (co_wf_def c can1 bs0) as co2.
                { eapply co_wf_def_len_implies;[|exact comp0];auto. }

                repndors;[|].

                { exists (mk_compop c (oterm (Can can1) bs1') t1' c0 d)
                         (mk_compop c (oterm (Can can1) bs0) t2' c1 d0).
                  dands; eauto 3 with slow.

                  { eapply reduce_to_prinargs_comp2;
                    [apply reduces_to_symm
                    |apply co_wf_def_implies_iswfpk; auto
                    |auto]. }

                  { eapply reduce_to_prinargs_comp2;
                    [apply reduces_to_symm
                    |apply co_wf_def_implies_iswfpk; auto
                    |auto]. }

                  { left;
                    apply differ_force_alpha_oterm; simpl; tcsp.
                    apply implies_differ_force_bterms_alpha; simpl; auto.
                    introv jj; repndors; tcsp; ginv;
                    apply implies_differ_force_b_alpha; eauto 3 with slow.
                  }
                }

                { exists (mk_compop c (oterm (Can can1) bs1') t' c0 d)
                         t2'; dands; eauto 3 with slow.

                  { eapply reduces_to_trans;
                    [apply reduce_to_prinargs_comp2;
                      [apply reduces_to_symm
                      |apply co_wf_def_implies_iswfpk; auto
                      |exact q2]
                    |].
                    unfold ex_spfexc in q1; exrepnd; subst.
                    unfold spfexc.
                    eapply reduces_to_if_step; csunf; simpl.
                    dcwf h. }
                }
              }

              { allunfold @nobnd.
                allrw @wf_term_ncompop_iff; exrepnd; allsimpl; ginv.
                allsimpl.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; GC.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd b0) y) as d2.
                autodimp d2 hyp.
                pose proof (imp (nobnd c0) z) as d3.
                autodimp d3 hyp.
                pose proof (imp (nobnd d0) u) as d4.
                autodimp d4 hyp.
                clear imp.

                inversion d1 as [? ? ? d5]; subst; clear d1.
                inversion d2 as [? ? ? d6]; subst; clear d2.
                inversion d3 as [? ? ? d7]; subst; clear d3.
                inversion d4 as [? ? ? d8]; subst; clear d4.

                inversion d5 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d5;[].

                apply isexc_implies2 in comp1; exrepnd; subst;[].
                inversion d6 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d6;[].

                assert (co_wf_def c can1 bs2) as co2.
                { eapply co_wf_def_len_implies;[|exact comp0];auto. }

                exists (oterm Exc l)
                       (oterm Exc bs0).
                dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h. }

                { left; eauto 3 with slow. }
              }

            * SSSCase "NArithOp".
              apply compute_step_narithop_can1_success in comp; repnd.
              allunfold @nobnd.
              allrw @wf_term_narithop_iff; exrepnd; allsimpl; ginv.
              repndors; exrepnd; subst; allsimpl;ginv;[|idtac|].

              { apply compute_step_arithop_success_can_can in comp1;
                exrepnd; subst; allsimpl; ginv; GC.
                allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl; fold_terms; GC.

                pose proof (imp (nobnd (mk_integer n1)) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd (mk_integer n2)) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].
                inversion d4 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d4;[].
                repeat (allsimpl; cpx).
                clear imp1 imp2.
                fold_terms.

                exists (@mk_integer o (get_arith_op a0 n1 n2))
                       (@mk_integer o (get_arith_op a0 n1 n2)).
                dands; eauto 3 with slow.
              }

              { apply if_has_value_like_k_narithop_can1 in hv; exrepnd.

                inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                pose proof (ind1 t t []) as h; clear ind1.
                repeat (autodimp h hyp);eauto 3 with slow;[].
                allrw @wf_term_narithop_iff; exrepnd; allsimpl; ginv.
                pose proof (h b0 b a t' f j) as q; clear h.

                applydup @if_hasvalue_like_arithop_can1 in hvt2.

                repeat (autodimp q hyp).
                { introv l w1 w2 isv r hv' d'.
                  apply (indhyp t1 t2 v m); eauto 3 with slow; try omega. }
                exrepnd.

                assert (ca_wf_def can1 bs2) as co2.
                { eapply ca_wf_def_len_implies;[|exact comp0];auto. }

                repndors;[|].

                { exists (mk_arithop a0 (oterm (Can can1) bs1') t1')
                         (mk_arithop a0 (oterm (Can can1) bs2) t2').
                  dands; eauto 3 with slow.

                  { eapply reduce_to_prinargs_arith2;
                    [apply reduces_to_symm
                    |
                    |auto]; eauto 3 with slow. }

                  { eapply reduce_to_prinargs_arith2;
                    [apply reduces_to_symm
                    |
                    |auto]; eauto 3 with slow. }

                  { left; apply differ_force_alpha_oterm; simpl; tcsp.
                    apply implies_differ_force_bterms_alpha; simpl; auto.
                    introv jj; repndors; tcsp; ginv;
                    apply implies_differ_force_b_alpha; eauto 3 with slow. }
                }

                { exists (mk_arithop a0 (oterm (Can can1) bs1') t')
                         t2'; dands; eauto 3 with slow.

                  { eapply reduces_to_trans;
                    [apply reduce_to_prinargs_arith2;
                      [apply reduces_to_symm
                      |
                      |exact q2]
                    |]; eauto 3 with slow.
                    unfold ex_spfexc in q1; exrepnd; subst.
                    unfold spfexc.
                    eapply reduces_to_if_step; csunf; simpl.
                    dcwf h. }
                  }
              }

              { inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
                cpx; allsimpl.

                pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
                autodimp d1 hyp.
                pose proof (imp (nobnd t) y) as d2.
                autodimp d2 hyp.
                clear imp.

                inversion d1 as [? ? ? d3]; subst; clear d1.
                inversion d2 as [? ? ? d4]; subst; clear d2.

                inversion d3 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d3;[].

                apply isexc_implies2 in comp1; exrepnd; subst;[].
                inversion d4 as [|?|?|? ? ? len2 nia2 imp2]; subst; clear d4;[].

                assert (ca_wf_def can1 bs2) as co2.
                { eapply ca_wf_def_len_implies;[|exact comp0];auto. }

                exists (oterm Exc l)
                       (oterm Exc bs0).
                dands; eauto 3 with slow.
                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h. }
                { left; eauto 3 with slow. }
              }

            * SSSCase "NCanTest".
              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp; exrepnd; subst.
              inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].
              cpx; allsimpl; GC.

              pose proof (imp (nobnd (oterm (Can can1) bs1')) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd arg2nt) y) as d2.
              autodimp d2 hyp.
              pose proof (imp (nobnd arg3nt) z) as d3.
              autodimp d3 hyp.
              clear imp.

              inversion d1 as [? ? ? d4]; subst; clear d1.
              inversion d2 as [? ? ? d5]; subst; clear d2.
              inversion d3 as [? ? ? d6]; subst; clear d3.

              inversion d4 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d4;[].
              repeat (allsimpl; cpx).

              exists (if canonical_form_test_for c can1 then arg2nt else arg3nt)
                     (if canonical_form_test_for c can1 then t0 else t3);
                dands; eauto 3 with slow.
              remember (canonical_form_test_for c can1) as cc; destruct cc; eauto 3 with slow.

          + SSCase "NCan".
            rw @compute_step_ncan_ncan in comp.
            remember (compute_step lib (oterm (NCan ncan1) bs1')) as cs;
              symmetry in Heqcs; destruct cs; ginv;[].
            applydup @if_has_value_like_k_ncan_primarg in hv; exrepnd.
            allsimpl.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              fold (sp_force_nat (oterm (NCan ncan1) bs1') x z f') in wft1.
              fold (sp_force_nat n x z f').
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.

              pose proof (ind1 (oterm (NCan ncan1) bs1') (oterm (NCan ncan1) bs1') []) as h; clear ind1.
              repeat (autodimp h hyp);eauto 3 with slow;[].
              pose proof (h arg2 b a n f j) as q; clear h.

              applydup @if_hasvalue_like_ncan_primarg in hvt2.

              repeat (autodimp q hyp).
              { introv l w1 w2 isv r hvv' dd'.
                apply (indhyp t1 t2 v m); eauto 3 with slow; try omega. }
              exrepnd.

              repndors;[|].

              { exists (sp_force_nat t1' x z f') (bound2_cbv t2' x z b f' a).
                dands; eauto 3 with slow.
                { eapply reduces_to_prinarg;exact q0. }
                { eapply reduces_to_prinarg;exact q2. }
                { left.
                  apply differ_forces_alpha_nat; auto. }
              }

              { exists (sp_force_nat t1' x z f') t2'.
                dands; eauto 3 with slow.
                { eapply reduces_to_prinarg;exact q0. }
                { eapply reduces_to_trans;
                  [apply reduces_to_prinarg;exact q2
                  |].
                  unfold ex_spfexc in q1; exrepnd; subst.
                  unfold spfexc.
                  eapply reduces_to_if_step; csunf; simpl; auto.
                }
              }
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

            pose proof (imp (nobnd (oterm (NCan ncan1) bs1')) b2) as d1.
            repeat (autodimp d1 hyp).

            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind1 (oterm (NCan ncan1) bs1') (oterm (NCan ncan1) bs1') []) as h.
            repeat (autodimp h hyp);eauto 3 with slow;[].

            allrw @wf_oterm_iff; allsimpl; repnd.
            pose proof (wft1 (nobnd (oterm (NCan ncan1) bs1'))) as w1; autodimp w1 hyp.
            pose proof (wft2 (nobnd t2)) as w2; autodimp w2 hyp.
            allrw @wf_bterm_iff.

            applydup @if_hasvalue_like_ncan_primarg in hvt2.

            pose proof (h t2 b a n f j) as q; clear h.
            repeat (autodimp q hyp).
            { introv ll w11 w22 isv r hvv' dd'.
              apply (indhyp t1 t0 v m); eauto 3 with slow; try omega. }
            exrepnd.

            repndors;[|].

            { exists (oterm (NCan ncan) (nobnd t1' :: bs1))
                     (oterm (NCan ncan) (nobnd t2' :: bs2)).
              dands; eauto 3 with slow.

              { eapply reduces_to_prinarg;exact q0. }

              { eapply reduces_to_prinarg;exact q2. }

              { left.
                apply differ_force_alpha_oterm; simpl; tcsp.
                apply implies_differ_force_bterms_alpha; simpl; auto.
                introv jj; repndors; tcsp; ginv; eauto 3 with slow.
                + apply implies_differ_force_b_alpha; auto.
                + pose proof (imp b1 b2) as h; autodimp h hyp; eauto 3 with slow. }
            }

            { destruct (dec_op_eq_try ncan) as [d|d].

                + subst; allsimpl.

                  repeat (destruct bs2; allsimpl; ginv).
                  destruct b0 as [l u].
                  destruct l; allsimpl; ginv.
                  destruct b1 as [l w].
                  repeat (destruct l; allsimpl; ginv).

                  repeat (destruct bs1; allsimpl; ginv).
                  destruct b0 as [l v].
                  destruct l; allsimpl; ginv.
                  destruct b1 as [l z].
                  repeat (destruct l; allsimpl; ginv).

                  allunfold @num_bvars; allsimpl; GC.

                  unfold ex_spfexc in q1; exrepnd; subst.

                  eapply reduces_to_preserves_hasvalue_like in hvt2;
                    [|apply reduces_to_prinarg;exact q2].
                  eapply reduces_to_preserves_hasvalue_like in hvt2;
                    [|apply reduces_to_if_step;csunf;simpl;auto].
                  eapply has_value_like_k_reduces_to in hv;
                    [|apply reduces_to_prinarg;exact q0].
                  exrepnd.

                  pose proof (imp (nobnd v) (nobnd u)) as d1.
                  autodimp d1 hyp.
                  inversion d1 as [? ? ? d3]; subst; clear d1.

                  applydup @if_has_value_like_k_ncan_primarg in hv2; exrepnd.
                  unfold has_value_like_k in hv5; exrepnd.
                  unfold computes_to_val_like_in_max_k_steps in hv6; repnd.
                  applydup @reduces_in_atmost_k_steps_implies_reduces_to in hv5.

                  eapply has_value_like_k_reduces_to in hv2;
                    [|apply reduces_to_prinarg;exact hv7].
                  exrepnd.

                  pose proof (wft1 (nobnd v)) as wv.
                  autodimp wv hyp.
                  allrw @wf_bterm_iff.

                  pose proof (wft2 (nobnd u)) as wu.
                  autodimp wu hyp.
                  allrw @wf_bterm_iff.

                  pose proof (wft1 (bterm [n1] z)) as wz.
                  autodimp wz hyp.
                  allrw @wf_bterm_iff.

                  applydup @compute_step_preserves_wf in Heqcs as wn; auto;[].
                  applydup @reduces_to_preserves_wf in q0 as wt1'; auto;[].
                  applydup @reduces_to_preserves_wf in hv7 as wu0; auto;[].

                  applydup @if_hasvalue_like_ncan_primarg in hvt2.

                  unfold isvalue_like in hv6.
                  repndors;[|].

                  * eapply has_value_like_k_reduces_to in hv8;
                    [|apply reduces_to_if_step;fold_terms;
                      rw @compute_step_try_iscan;auto].
                    exrepnd.

                    apply if_has_value_like_k_ncompop_can_same in hv9; eauto 2 with slow;[].
                    exrepnd.

                    pose proof (indhyp v u u1 j4) as h.
                    repeat (autodimp h hyp); try omega; eauto 2 with slow.
                    { repndors; eauto 3 with slow. }
                    exrepnd.

                    applydup @reduces_in_atmost_k_steps_preserves_wf in hv11; auto;[].

                    destruct h0 as [h0|h0].

                    { repndors;[|].

                      { unfold ispk in hv9; exrepnd; subst.
                        apply differ_force_alpha_pk2term in h0; repnd; subst.
                        exists (mk_try n v n1 z) (spfexc vs1 vs2 a).
                        dands; eauto 3 with slow.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduce_to_prinargs_comp2;
                              [exact h1
                              |eauto 3 with slow
                              |apply reduces_to_lfresh_utoken]
                            |].
                          eapply reduces_to_if_step.
                          csunf; simpl.
                          rw @pk2term_eq.
                          dcwf h; simpl.
                          { unfold compute_step_comp; simpl.
                            rw @get_param_from_cop_pk2can; boolvar; tcsp.
                            subst; allsimpl; allrw not_over_or; tcsp. }
                          { allrw @co_wf_pk2can; ginv. }
                      }

                      { apply wf_isexc_implies in hv9; exrepnd; subst; eauto 3 with slow;[].
                        apply differ_force_alpha_exception in h0; exrepnd; subst.
                        exists (mk_exception a0 e) (mk_exception n2 e1).
                        dands.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q0|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j1;exact hv5|].
                          eapply reduces_to_if_split2;
                            [fold_terms; rw @compute_step_try_iscan; auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j4; exact hv11|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exact h1|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - left.
                          apply implies_differ_force_alpha_exception; eauto 2 with slow.
                      }
                    }

                    { unfold ex_spfexc in h0; exrepnd; subst.
                      exists (oterm (NCan NTryCatch) [bterm [] n, bterm [] v, bterm [n1] z])
                             (spfexc vs0 vs3 a).
                      dands; eauto 3 with slow.
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact q2|].
                      eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact h1|].
                      apply reduces_to_if_step; csunf; simpl; auto.
                    }

                  * apply wf_isexc_implies in hv6; eauto 3 with slow; exrepnd; subst;[].

                    eapply has_value_like_k_reduces_to in hv8;
                      [|apply reduces_to_if_step; csunf; simpl;auto];[].
                    exrepnd.

                    allrw @wf_exception_iff; repnd.

                    applydup @if_has_value_like_k_ncompop_fst in hv6; eauto 2 with slow;
                    try (apply wf_exception_iff); auto;
                    try (apply wf_term_subst); auto;[].
                    exrepnd.

                    pose proof (indhyp v u t' j4) as h.
                    repeat (autodimp h hyp); try omega; eauto 2 with slow.
                    { repndors; eauto 3 with slow. }
                    exrepnd.

                    applydup @reduces_in_atmost_k_steps_preserves_wf in hv11; auto;[].

                    destruct h0 as [h0|h0].

                    { repndors;[|].

                      { unfold ispk in hv9; exrepnd; subst.
                        apply differ_force_alpha_pk2term in h0; repnd; subst.
                        exists (mk_try n v n1 z) (spfexc vs1 vs2 a).
                        dands; eauto 3 with slow.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduce_to_prinargs_comp2;
                              [exact h1
                              |eauto 3 with slow
                              |apply reduces_to_lfresh_utoken]
                            |].
                          eapply reduces_to_if_step.
                          csunf; simpl.
                          rw @pk2term_eq.
                          dcwf h.
                          { simpl.
                            unfold compute_step_comp; simpl.
                            rw @get_param_from_cop_pk2can; boolvar; tcsp.
                            subst; allsimpl; allrw not_over_or; tcsp. }
                          { allrw @co_wf_pk2can; ginv. }
                      }

                      { apply wf_isexc_implies in hv9; exrepnd; subst; eauto 3 with slow;[].
                        apply differ_force_alpha_exception in h0; exrepnd; subst.
                        exists (mk_exception a1 e0) (mk_exception n2 e1).
                        dands.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q0|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j1;exact hv5|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j4; exact hv11|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exact h1|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - left.
                          apply implies_differ_force_alpha_exception; eauto 2 with slow.
                      }
                    }

                    { unfold ex_spfexc in h0; exrepnd; subst.
                      exists (oterm (NCan NTryCatch) [bterm [] n, bterm [] v, bterm [n1] z])
                             (spfexc vs0 vs3 a).
                      dands; eauto 3 with slow.
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact q2|].
                      eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact h1|].
                      apply reduces_to_if_step; csunf; simpl; auto.
                    }

                + unfold ex_spfexc in q1; exrepnd; subst.
                  exists (oterm (NCan ncan) (bterm [] n :: bs1))
                         (spfexc vs1 vs2 a).
                  dands; eauto 3 with slow.

                  * eapply reduces_to_trans;
                    [apply reduces_to_prinarg;exact q2|].
                    eapply reduces_to_if_split2;
                      [csunf;simpl;auto;rw @compute_step_catch_if_diff; auto|].
                    apply reduces_to_symm.
            }

          + SSCase "Exc".
            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              repndors; repnd; ginv; subst;[].
              fold (sp_force_nat (oterm Exc bs1') x z f') in wft1.
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.
              clear ind1.

              inversion d' as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d'.
              exists (oterm Exc bs1') (oterm Exc bs2); dands; eauto 3 with slow.
              { left; eauto 3 with slow. }
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx;[].

            pose proof (imp (nobnd (oterm Exc bs1')) b2) as d1.
            autodimp d1 hyp.

            inversion d1 as [? ? ? d2]; subst; clear d1.

            inversion d2 as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d2;[].

            repndors; exrepnd; subst; allsimpl; fold_terms; cpx; allsimpl; fold_terms.

            { pose proof (imp1 (nobnd a') x0) as d1.
              autodimp d1 hyp.
              pose proof (imp1 (nobnd e) y0) as d2.
              autodimp d2 hyp.
              clear imp1.
              inversion d1 as [? ? ? d3]; subst; clear d1.
              inversion d2 as [? ? ? d4]; subst; clear d2.

              pose proof (imp (nobnd a0) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [v] b0) y) as d2.
              autodimp d2 hyp.
              clear imp.
              inversion d1 as [? ? ? d5]; subst; clear d1.
              inversion d2 as [? ? ? d6]; subst; clear d2.

              allrw <- @wf_try_iff; repnd.
              allrw @wf_exception_iff; repnd.

              exists (mk_atom_eq a0 a' (subst b0 v e) (mk_exception a' e))
                     (mk_atom_eq t3 t2 (subst t4 v t0) (mk_exception t2 t0)).
              dands; eauto 3 with slow;[].

              left.
              apply differ_force_alpha_oterm; simpl; tcsp.
              apply implies_differ_force_bterms_alpha; simpl; auto.
              introv j; repndors; tcsp; ginv;
              apply implies_differ_force_b_alpha; eauto 3 with slow.

              { apply differ_force_subst; auto. }
              { apply differ_force_alpha_oterm; simpl; tcsp.
                apply implies_differ_force_bterms_alpha; simpl; auto.
                introv j; repndors; tcsp; ginv;
                apply implies_differ_force_b_alpha; eauto 3 with slow. }
            }

            { exists (oterm Exc bs1') (oterm Exc bs3).
              dands; eauto 3 with slow.
              { apply reduces_to_if_step.
                csunf; simpl.
                rw @compute_step_catch_if_diff; auto. }
              { left; eauto 3 with slow. }
            }

          + SSCase "Abs".
            rw @compute_step_ncan_abs in comp.
            remember (compute_step_lib lib abs1 bs1') as cs;
              symmetry in Heqcs; destruct cs; ginv;[].
            applydup @if_has_value_like_k_ncan_primarg in hv; exrepnd.
            allsimpl.

            inversion d as [? ? ? ? ? aeq d'|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[|].

            { (* force case *)
              applydup @alpha_eq_preserves_isprog in aeq;auto;[].
              fold_terms.
              fold (sp_force_nat (oterm (Abs abs1) bs1') x z f') in wft1.
              fold (sp_force_nat n x z f').
              apply wf_sp_force_nat in wft1; repnd.
              apply wf_bound2_cbv in wft2; repnd.

              applydup @if_hasvalue_like_ncan_primarg in hvt2.

              pose proof (ind1 (oterm (Abs abs1) bs1') (oterm (Abs abs1) bs1') []) as h; clear ind1.
              repeat (autodimp h hyp);eauto 3 with slow;[].
              pose proof (h arg2 b a n f j) as q; clear h.
              repeat (autodimp q hyp).
              { introv l w1 w2 isv r hvv' dd'.
                apply (indhyp t1 t2 v m); eauto 3 with slow; try omega. }
              exrepnd.

              repndors;[|].

              { exists (sp_force_nat t1' x z f') (bound2_cbv t2' x z b f' a).
                dands; eauto 3 with slow.
                { eapply reduces_to_prinarg;exact q0. }
                { eapply reduces_to_prinarg;exact q2. }
                { left.
                  apply differ_forces_alpha_nat; auto. }
              }

              { exists (sp_force_nat t1' x z f') t2'.
                dands; eauto 3 with slow.
                { eapply reduces_to_prinarg;exact q0. }
                { eapply reduces_to_trans;
                  [apply reduces_to_prinarg;exact q2
                  |].
                  unfold ex_spfexc in q1; exrepnd; subst.
                  unfold spfexc.
                  eapply reduces_to_if_step; csunf; simpl; auto.
                }
              }
            }

            (* non force case *)

            destruct bs2 as [|b2 bs2]; allsimpl; ginv; cpx.

            pose proof (imp (nobnd (oterm (Abs abs1) bs1')) b2) as d1.
            repeat (autodimp d1 hyp).

            inversion d1 as [? ? ? d2]; subst; clear d1.

            pose proof (ind1 (oterm (Abs abs1) bs1') (oterm (Abs abs1) bs1') []) as h.
            repeat (autodimp h hyp);eauto 3 with slow;[].

            allrw @wf_oterm_iff; allsimpl; repnd.
            pose proof (wft1 (nobnd (oterm (Abs abs1) bs1'))) as w1; autodimp w1 hyp.
            pose proof (wft2 (nobnd t2)) as w2; autodimp w2 hyp.
            allrw @wf_bterm_iff.

            applydup @if_hasvalue_like_ncan_primarg in hvt2.

            pose proof (h t2 b a n f j) as q; clear h.
            repeat (autodimp q hyp).
            { introv ll w11 w22 isv r hvv' dd'.
              apply (indhyp t1 t0 v m); eauto 3 with slow; try omega. }
            exrepnd.

            repndors;[|].

            { exists (oterm (NCan ncan) (nobnd t1' :: bs1))
                     (oterm (NCan ncan) (nobnd t2' :: bs2)).
              dands; eauto 3 with slow.

              { eapply reduces_to_prinarg;exact q0. }

              { eapply reduces_to_prinarg;exact q2. }

              { left.
                apply differ_force_alpha_oterm; simpl; tcsp.
                apply implies_differ_force_bterms_alpha; simpl; auto.
                introv jj; repndors; tcsp; ginv; eauto 3 with slow.
                + apply implies_differ_force_b_alpha; auto.
                + pose proof (imp b1 b2) as h; autodimp h hyp; eauto 3 with slow. }
            }

            { destruct (dec_op_eq_try ncan) as [d|d].

                + subst; allsimpl.

                  repeat (destruct bs2; allsimpl; ginv).
                  destruct b0 as [l u].
                  destruct l; allsimpl; ginv.
                  destruct b1 as [l w].
                  repeat (destruct l; allsimpl; ginv).

                  repeat (destruct bs1; allsimpl; ginv).
                  destruct b0 as [l v].
                  destruct l; allsimpl; ginv.
                  destruct b1 as [l z].
                  repeat (destruct l; allsimpl; ginv).

                  allunfold @num_bvars; allsimpl; GC.

                  unfold ex_spfexc in q1; exrepnd; subst.

                  eapply reduces_to_preserves_hasvalue_like in hvt2;
                    [|apply reduces_to_prinarg;exact q2].
                  eapply reduces_to_preserves_hasvalue_like in hvt2;
                    [|apply reduces_to_if_step;csunf;simpl;auto].
                  eapply has_value_like_k_reduces_to in hv;
                    [|apply reduces_to_prinarg;exact q0].
                  exrepnd.

                  pose proof (imp (nobnd v) (nobnd u)) as d1.
                  autodimp d1 hyp.
                  inversion d1 as [? ? ? d3]; subst; clear d1.

                  applydup @if_has_value_like_k_ncan_primarg in hv2; exrepnd.
                  unfold has_value_like_k in hv5; exrepnd.
                  unfold computes_to_val_like_in_max_k_steps in hv6; repnd.
                  applydup @reduces_in_atmost_k_steps_implies_reduces_to in hv5.

                  eapply has_value_like_k_reduces_to in hv2;
                    [|apply reduces_to_prinarg;exact hv7].
                  exrepnd.

                  pose proof (wft1 (nobnd v)) as wv.
                  autodimp wv hyp.
                  allrw @wf_bterm_iff.

                  pose proof (wft2 (nobnd u)) as wu.
                  autodimp wu hyp.
                  allrw @wf_bterm_iff.

                  pose proof (wft1 (bterm [n1] z)) as wz.
                  autodimp wz hyp.
                  allrw @wf_bterm_iff.

                  applydup @wf_compute_step_lib in Heqcs as wn; auto;[].
                  applydup @reduces_to_preserves_wf in q0 as wt1'; auto;[].
                  applydup @reduces_to_preserves_wf in hv7 as wu0; auto;[].

                  applydup @if_hasvalue_like_ncan_primarg in hvt2.

                  unfold isvalue_like in hv6.
                  repndors;[|].

                  * eapply has_value_like_k_reduces_to in hv8;
                    [|apply reduces_to_if_step;fold_terms;
                      rw @compute_step_try_iscan;auto];[].
                    exrepnd.

                    apply if_has_value_like_k_ncompop_can_same in hv9; eauto 2 with slow;[].
                    exrepnd.

                    pose proof (indhyp v u u1 j4) as h.
                    repeat (autodimp h hyp); try omega; eauto 2 with slow.
                    { repndors; eauto 3 with slow. }
                    exrepnd.

                    applydup @reduces_in_atmost_k_steps_preserves_wf in hv11; auto;[].

                    destruct h0 as [h0|h0].

                    { repndors;[|].

                      { unfold ispk in hv9; exrepnd; subst.
                        apply differ_force_alpha_pk2term in h0; repnd; subst.
                        exists (mk_try n v n1 z) (spfexc vs1 vs2 a).
                        dands; eauto 3 with slow.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduce_to_prinargs_comp2;
                              [exact h1
                              |eauto 3 with slow
                              |apply reduces_to_lfresh_utoken]
                            |].
                          eapply reduces_to_if_step.
                          csunf; simpl.
                          rw @pk2term_eq.
                          dcwf h; simpl.
                          { unfold compute_step_comp; simpl.
                            rw @get_param_from_cop_pk2can; boolvar; tcsp.
                            subst; allsimpl; allrw not_over_or; tcsp. }
                          { allrw @co_wf_pk2can; ginv. }
                      }

                      { apply wf_isexc_implies in hv9; exrepnd; subst; eauto 3 with slow;[].
                        apply differ_force_alpha_exception in h0; exrepnd; subst.
                        exists (mk_exception a0 e) (mk_exception n2 e1).
                        dands.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q0|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j1;exact hv5|].
                          eapply reduces_to_if_split2;
                            [fold_terms; rw @compute_step_try_iscan; auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j4; exact hv11|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exact h1|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - left.
                          apply implies_differ_force_alpha_exception; eauto 2 with slow.
                      }
                    }

                    { unfold ex_spfexc in h0; exrepnd; subst.
                      exists (oterm (NCan NTryCatch) [bterm [] n, bterm [] v, bterm [n1] z])
                             (spfexc vs0 vs3 a).
                      dands; eauto 3 with slow.
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact q2|].
                      eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact h1|].
                      apply reduces_to_if_step; csunf; simpl; auto.
                    }

                  * apply wf_isexc_implies in hv6;eauto 3 with slow; exrepnd; subst;[].

                    eapply has_value_like_k_reduces_to in hv8;
                      [|apply reduces_to_if_step; csunf; simpl;auto];[].
                    exrepnd.

                    allrw @wf_exception_iff; repnd.

                    applydup @if_has_value_like_k_ncompop_fst in hv6; eauto 2 with slow;
                    try (apply wf_exception_iff); auto;
                    try (apply wf_term_subst); auto;[].
                    exrepnd.

                    pose proof (indhyp v u t' j4) as h.
                    repeat (autodimp h hyp); try omega; eauto 2 with slow.
                    { repndors; eauto 3 with slow. }
                    exrepnd.

                    applydup @reduces_in_atmost_k_steps_preserves_wf in hv11; auto;[].

                    destruct h0 as [h0|h0].

                    { repndors;[|].

                      { unfold ispk in hv9; exrepnd; subst.
                        apply differ_force_alpha_pk2term in h0; repnd; subst.
                        exists (mk_try n v n1 z) (spfexc vs1 vs2 a).
                        dands; eauto 3 with slow.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduce_to_prinargs_comp2;
                              [exact h1
                              |eauto 3 with slow
                              |apply reduces_to_lfresh_utoken]
                            |].
                          eapply reduces_to_if_step.
                          csunf; simpl.
                          rw @pk2term_eq.
                          dcwf h.
                          { simpl.
                            unfold compute_step_comp; simpl.
                            rw @get_param_from_cop_pk2can; boolvar; tcsp.
                            subst; allsimpl; allrw not_over_or; tcsp. }
                          { allrw @co_wf_pk2can; ginv. }
                      }

                      { apply wf_isexc_implies in hv9; exrepnd; subst; eauto 3 with slow;[].
                        apply differ_force_alpha_exception in h0; exrepnd; subst.
                        exists (mk_exception a1 e0) (mk_exception n2 e1).
                        dands.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q0|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j1;exact hv5|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exists j4; exact hv11|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - eapply reduces_to_trans;
                          [apply reduces_to_prinarg;exact q2|].
                          eapply reduces_to_if_split2;[csunf;simpl;auto|].
                          eapply reduces_to_trans;
                            [apply reduces_to_prinarg;exact h1|].
                          eapply reduces_to_if_step.
                          csunf; simpl; auto.

                        - left.
                          apply implies_differ_force_alpha_exception; eauto 2 with slow.
                      }
                    }

                    { unfold ex_spfexc in h0; exrepnd; subst.
                      exists (oterm (NCan NTryCatch) [bterm [] n, bterm [] v, bterm [n1] z])
                             (spfexc vs0 vs3 a).
                      dands; eauto 3 with slow.
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact q2|].
                      eapply reduces_to_if_split2;[csunf;simpl;auto|].
                      eapply reduces_to_trans;
                        [apply reduces_to_prinarg;exact h1|].
                      apply reduces_to_if_step; csunf; simpl; auto.
                    }

                + unfold ex_spfexc in q1; exrepnd; subst.
                  exists (oterm (NCan ncan) (bterm [] n :: bs1))
                         (spfexc vs1 vs2 a).
                  dands; eauto 3 with slow.

                  * eapply reduces_to_trans;
                    [apply reduces_to_prinarg;exact q2|].
                    eapply reduces_to_if_split2;
                      [csunf;simpl;auto;rw @compute_step_catch_if_diff; auto|].
                    apply reduces_to_symm.
            }
      }

      { (* fresh case *)

        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; repnd; subst; allsimpl.

        inversion d as [|?|?|? ? ? len1 nia1 imp1]; subst; clear d;[].
        allsimpl; cpx; allsimpl.
        pose proof (imp1 (bterm [n] t1) x) as d1.
        autodimp d1 hyp.
        clear imp1.
        inversion d1 as [? ? ? d2]; subst; clear d1.
        fold_terms.

        repndors; exrepnd; subst; allsimpl.

        - apply has_value_like_k_fresh_id in hv; sp.

        - pose proof (differ_force_isvalue_like b a f t1 t2) as h.
          repeat (autodimp h hyp).
          repnd.
          exists (pushdown_fresh n t1) (pushdown_fresh n t2).
          dands; eauto 3 with slow.
          apply reduces_to_if_step.
          apply compute_step_fresh_if_isvalue_like; auto.

        - (* one reduction step under fresh *)
          pose proof (fresh_atom o (a :: get_utokens t1
                                      ++ get_utokens t2
                                      ++ get_utokens f)) as fa; exrepnd.
          allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a'.

          pose proof (ind1 t1 (subst t1 n (mk_utoken a')) [n]) as q; clear ind1.
          repeat (autodimp q hyp);[rw @simple_osize_subst;eauto 3 with slow|];[].
          allrw @wf_fresh_iff.
          applydup @compute_step_preserves_wf in comp2; auto;
          [|apply wf_term_subst; eauto 3 with slow];[].
          pose proof (has_value_like_k_fresh_implies
                        lib k (get_fresh_atom t1) n
                        (subst_utokens x [(get_fresh_atom t1, mk_var n)])) as hvf.
          repeat (autodimp hvf hyp).
          { apply wf_subst_utokens; eauto 3 with slow. }
          { introv j; apply get_utokens_subst_utokens_subset in j; allsimpl.
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r.
            allrw in_remove; sp. }

          assert (!LIn n (free_vars x)) as ninx.
          { apply compute_step_preserves in comp2; repnd; eauto 4 with slow;[].
            introv j; apply subvars_eq in comp3; apply comp3 in j.
            apply eqset_free_vars_disjoint in j; allsimpl; boolvar; allsimpl;
            allrw app_nil_r; allrw in_remove_nvars; allsimpl; tcsp. }

          eapply alphaeq_preserves_has_value_like_k in hvf;
            [| |apply simple_subst_subst_utokens_aeq; auto];
            [|apply nt_wf_subst; eauto 2 with slow;
              apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow];[].

          pose proof (compute_step_subst_utoken
                        lib t1 x
                        [(n,mk_utoken (get_fresh_atom t1))]) as comp'.
          repeat (autodimp comp' hyp); eauto 3 with slow.
          { apply nr_ut_sub_cons; auto; introv j; apply get_fresh_atom_prop. }
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; apply get_fresh_atom_prop. }
          exrepnd; allsimpl.
          pose proof (comp'0 [(n,mk_utoken a')]) as comp''; allsimpl; clear comp'0.
          repeat (autodimp comp'' hyp).
          { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; auto. }
          exrepnd.
          allrw @fold_subst.

          pose proof (get_fresh_atom_prop t1) as gfpat1.
          remember (get_fresh_atom t1) as at1.
          clear Heqat1.
          dup comp'1 as aeq1.
          apply (alpha_eq_subst_utokens_same _ _ [(at1,mk_var n)]) in aeq1.
          dup aeq1 as aeq'.
          apply alpha_eq_sym in aeq1.
          eapply alpha_eq_trans in aeq1;
            [|apply alpha_eq_sym; apply simple_alphaeq_subst_utokens_subst;
              introv j; apply comp'4 in j; sp].
          dup aeq1 as aeq''.
          apply (lsubst_alpha_congr2 _ _ [(n,mk_utoken a')]) in aeq1.
          allrw @fold_subst.
          dup aeq1 as aeq'''.
          apply alpha_eq_sym in aeq1; eapply alpha_eq_trans in aeq1;
          [|apply alpha_eq_sym; apply simple_subst_subst_utokens_aeq_ren; auto].
          assert (alpha_eq s (ren_utokens [(at1,a')] x)) as aeq2 by (eauto 3 with slow).

          pose proof (q (subst t2 n (mk_utoken a')) b a s f k) as ih; clear q.
          repeat (autodimp ih hyp); try (apply wf_term_subst; eauto 3 with slow).
          { repeat unfsubst.
            apply differ_force_lsubst_aux; simpl; auto.
            apply dfsub_cons; auto;[].
            apply differ_force_oterm; simpl; tcsp. }
          { eapply alphaeq_preserves_has_value_like_k;
            [|apply alpha_eq_sym;exact aeq2|]; eauto 3 with slow.
            apply has_value_like_k_ren_utokens; simpl; eauto 3 with slow.
            apply disjoint_singleton_l; rw in_remove; introv j; repnd.
            apply compute_step_preserves_utokens in comp2; eauto 3 with slow; apply comp2 in j.
            apply get_utokens_subst in j; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp. }
          { pose proof (hasvalue_like_fresh_implies lib a' n t2) as hvts.
            repeat (autodimp hvts hyp). }
          { introv ll w11 w22 isv r hvv' dd'.
            apply (indhyp t0 t3 v m); eauto 3 with slow; try omega. }
          exrepnd.

          applydup @preserve_nt_wf_compute_step in comp''1 as wfs; eauto 3 with slow;[].

          applydup @reduces_to_fresh2 in ih2; auto.
          exrepnd.
          eapply reduces_to_alpha in ih0;
            [| |eapply alpha_eq_trans;[exact comp''0|exact aeq'''] ];
            eauto 3 with slow;[].
          exrepnd.
          applydup @reduces_to_fresh2 in ih0; auto;
          [|apply wf_subst_utokens; eauto 3 with slow
           |introv j; apply get_utokens_subst_utokens_subset in j; allsimpl;
            allunfold @get_utokens_utok_ren; allsimpl; allrw app_nil_r;
            allrw in_remove; repnd;
            apply compute_step_preserves_utokens in comp2; eauto 3 with slow; apply comp2 in j;
            apply get_utokens_subst in j; allsimpl; boolvar; allrw app_nil_r;
            allrw in_app_iff; allsimpl; repndors; tcsp].
          exrepnd.

          repndors;[|].

          { exists (mk_fresh n z0)
                   (mk_fresh n z); dands; eauto 3 with slow.
            left.
            eapply differ_force_alpha_alpha_eq1;
              [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih7|].
            eapply differ_force_alpha_alpha_eq1;
              [apply implies_alpha_eq_mk_fresh;apply alpha_eq_subst_utokens_same;exact ih5|].
            eapply differ_force_alpha_alpha_eq2;
              [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact ih4|].
            apply differ_force_alpha_mk_fresh.

            apply differ_force_alpha_subst_utokens; simpl; tcsp.
            { apply disjoint_singleton_r; auto. }
          }

          { pose proof (ex_spfexc_subst_utokens a t2' [(a',mk_var n)]) as exspf.
            simpl in exspf.
            repeat (autodimp exspf hyp); tcsp.
            eapply ex_spfexc_alpha_eq in exspf;[|apply alpha_eq_sym;exact ih4].
            unfold ex_spfexc in exspf; exrepnd; subst.
            exists (mk_fresh n (subst_utokens x [(at1, mk_var n)]))
                   (spfexc (n :: vs1) (n :: vs2) a).
            dands; eauto 3 with slow.

            { eapply reduces_to_trans;[exact ih3|].
              apply reduces_to_if_step; csunf; simpl.
              unfold maybe_new_var; simpl; auto. }
          }
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.

      inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].

      exists (oterm Exc bs1) (oterm Exc bs2); dands; eauto 3 with slow.
      left; eauto 3 with slow.

    + SCase "Abs".
      csunf comp; allsimpl.

      inversion d as [|?|?|? ? ? len nia imp]; subst; simphyps; clear d;[].

      pose proof (differ_force_bterms_implies_eq_map_num_bvars b a f bs1 bs2) as e.
      autodimp e hyp.
      { unfold differ_force_bterms, br_bterms, br_list; dands; auto. }
      apply compute_step_lib_success in comp; exrepnd; subst.
      exists (mk_instance vars bs1 rhs)
             (mk_instance vars bs2 rhs).
      dands; eauto 3 with slow.
      { apply reduces_to_if_step; csunf; simpl.
        eapply compute_step_lib_success_change_bs;[|exact comp0]; auto. }
      dup comp0 as fe.
      eapply found_entry_change_bs in fe;[|exact e].
      applydup @found_entry_implies_matching_entry in comp0.
      applydup @found_entry_implies_matching_entry in fe.
      left.
      apply differ_force_mk_instance; auto;
      try (complete (allunfold @matching_entry; sp));
      try (complete (allunfold @correct_abs; sp)).
      unfold differ_force_bterms, br_bterms, br_list; sp.
Qed.

Lemma reduces_to_implies_exc {o} :
  forall lib (a b : @NTerm o),
    reduces_to lib a b
    -> reduces_to_exc lib a b.
Proof.
  introv r.
  eapply reduces_to_exc_trans2;[exact r|].
  unfold reduces_to_exc.
  exists 0.
  apply reduces_in_atmost_k_steps_exc_0; auto.
Qed.

(*
Lemma reduces_to_nat_implies_hasvalue_like_except {o} :
  forall lib a (t : @NTerm o) k,
    reduces_to lib t (mk_nat k)
    -> hasvalue_like_except lib a t.
Proof.
  introv r.
  exists (@mk_nat o k); dands; allsimpl; tcsp; eauto 3 with slow.
  apply reduces_to_implies_exc; auto.
Qed.
 *)

Lemma reduces_in_atmost_k_steps_differ_force2 {o} :
  forall lib b a f k (t1 t2 : @NTerm o) u,
    isprog f
    -> wf_term t1
    -> wf_term t2
    -> !LIn a (get_utokens f)
    -> differ_force b a f t1 t2
    -> hasvalue_like lib t2 (* Do we really need that? *)
    -> reduces_in_atmost_k_steps lib t1 u k
    -> isvalue_like u
    -> {u' : NTerm
        & reduces_to lib t2 u'
        # (differ_force_alpha b a f u u' [+] ex_spfexc a u')}.
Proof.
  induction k as [n ind] using comp_ind_type; introv ispf w1 w2 nia d hvt2 r isv.
  destruct n as [|n]; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t2; dands; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    pose proof (computation_step_differ_force2 lib t1 t2 b a u0 f n) as h.
    repeat (autodimp h hyp).
    { exists u; dands; eauto 3 with slow.
      unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }
    { intros tt1 tt2 vv mm xx1 ww1 ww2 hv1 rr1 hv2 dd.
      pose proof (ind mm xx1 tt1 tt2 vv) as h; clear ind.
      repeat (autodimp h hyp). }

    exrepnd.

    assert (forall (t1 t2 v : NTerm) (m : nat),
              m < S n
              -> wf_term t1
              -> wf_term t2
              -> isvalue_like v
              -> reduces_in_atmost_k_steps lib t1 v m
              -> hasvalue_like lib t2
              -> differ_force_alpha b a f t1 t2
              -> {v2 : NTerm
                  $ reduces_to lib t2 v2
                  # (differ_force_alpha b a f v v2 [+] ex_spfexc a v2)}) as ind'.
    { introv x ww1 ww2 isvv rr hv' d'.
      unfold differ_force_alpha in d'; exrepnd.
      eapply reduces_in_atmost_k_steps_alpha in rr;[| |exact d'0]; eauto 2 with slow; exrepnd;[].
      eapply continuity2_2.alphaeq_preserves_hasvalue_like in hv';[| |exact d'2]; eauto 2 with slow;[].
      pose proof (ind m x u1 u2 t2'0) as hh.
      repeat (autodimp hh hyp); eauto 2 with slow;[].
      exrepnd.
      applydup @alphaeq_preserves_wf_term in d'2 as wfu2; eauto 2 with slow;[].
      eapply reduces_to_alpha in hh1;[| |apply alpha_eq_sym; exact d'2]; eauto 2 with slow;[].
      exrepnd.
      eexists; dands; eauto;[].
      destruct hh0.
      { left; eapply differ_force_alpha_alpha_eq1;[apply alpha_eq_sym;exact rr0|].
        eapply differ_force_alpha_alpha_eq2;[exact hh2|]; auto. }
      { right.
        eapply ex_spfexc_alpha_eq;[exact hh2|]; auto.
      }
    }
    clear ind; rename ind' into ind.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to lib n u0 t1' u) as h'.
    repeat (autodimp h' hyp); eauto 3 with slow.
    exrepnd.

    applydup @reduces_to_preserves_wf in h2;auto;[].
    applydup @compute_step_preserves_wf in r1;auto;[].
    applydup @reduces_to_preserves_wf in h0;auto;[].
    applydup @reduces_in_atmost_k_steps_preserves_wf in r0;auto;[].

    repndors;[|].

    + pose proof (ind t1' t2' u k') as ih; clear ind.
      repeat (autodimp ih hyp); try omega.
      { eapply reduces_to_preserves_hasvalue_like; eauto. }
      exrepnd.
      exists v2.
      dands; auto.
      eapply reduces_to_trans; eauto.

    + exists t2'; dands; auto.
Qed.

Lemma reduces_to_differ_force2 {o} :
  forall lib (t1 t2 : @NTerm o) b a f k,
    isprog f
    -> isprog t1
    -> isprog t2
    -> !LIn a (get_utokens f)
    -> differ_force b a f t1 t2
    -> hasvalue_like lib t2 (* Do we really need that? *)
    -> reduces_to lib t1 (mk_nat k)
    -> (reduces_to lib t2 (mk_nat k) [+] cequiv lib t2 (spexc a)).
Proof.
  introv isp w1 w2 niaf diff hvt2 r.
  allunfold @reduces_to; exrepnd.
  pose proof (reduces_in_atmost_k_steps_differ_force2 lib b a f k0 t1 t2 (mk_nat k)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd.

  repndors;[|].

  - left.
    unfold differ_force_alpha in h0; exrepnd.
    allapply @alpha_eq_mk_nat; subst.
    inversion h0; allsimpl; cpx; GC; fold_terms.
    apply alpha_eq_sym in h3; apply alpha_eq_mk_nat in h3; subst.
    unfold reduces_to in h1; exrepnd.
    exists k1; auto.

  - right.
    eapply cequiv_trans;[apply reduces_to_implies_cequiv|]; eauto 3 with slow.
    unfold ex_spfexc in h0; exrepnd; subst.
    apply cequiv_spfexc.
Qed.

Lemma computes_to_valc_differ_force2 {o} :
  forall lib (t1 t2 : @CTerm o) b a f k,
    !LIn a (getc_utokens f)
    -> differ_force b a (get_cterm f) (get_cterm t1) (get_cterm t2)
    -> computes_to_valc lib t1 (mkc_nat k)
    -> hasvalue_likec lib t2
    -> (computes_to_valc lib t2 (mkc_nat k) [+] cequivc lib t2 (spexcc a)).
Proof.
  introv nia d comp hv; allunfold @computes_to_valc; destruct_cterms; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  allunfold @getc_utokens; allsimpl.
  allunfold @hasvalue_likec; allsimpl.
  allunfold @cequivc; allsimpl.
  pose proof (reduces_to_differ_force2 lib x1 x0 b a x k) as h.
  repeat (autodimp h hyp).
  repndors;[left|right]; auto.
Qed.

Lemma computes_to_value_mk_atom_eq_pk_implies {o} :
  forall lib (a b c d : @NTerm o) v,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_value lib (mk_atom_eq a b c d) v
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & computes_to_pk lib a pk1
        # computes_to_pk lib b pk2
        # computes_to_value lib (if param_kind_deq pk1 pk2 then c else d) v }}.
Proof.
  introv wa wb wc wd comp.
  unfold computes_to_value in comp; repnd.
  unfold reduces_to in comp0; exrepnd.

  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpEq a b c d v) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }

  repndors; exrepnd; repndors; exrepnd; subst; allsimpl; ginv;
  try (complete (inversion comp; allsimpl; tcsp));[].

  allunfold @computes_to_can_in_max_k_steps; repnd.
  exists pk1 pk2; dands; auto; try (unfold computes_to_pk; eauto 3 with slow).
  allunfold @computes_to_val_like_in_max_k_steps; repnd.
  unfold computes_to_value; dands; auto.
  boolvar; exists (k - (k1 + k2 + 1)); auto.
Qed.

Lemma computes_to_valc_mkc_atom_eq_pk_implies {o} :
  forall lib (a b c d : @CTerm o) v,
    computes_to_valc lib (mkc_atom_eq a b c d) v
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & computes_to_pkc lib a pk1
        # computes_to_pkc lib b pk2
        # computes_to_valc lib (if param_kind_deq pk1 pk2 then c else d) v }}.
Proof.
  introv comp; destruct_cterms; allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_pkc; allsimpl.
  pose proof (computes_to_value_mk_atom_eq_pk_implies lib x3 x2 x1 x0 x) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd.
  exists pk1 pk2; dands; auto.
  boolvar; simpl; auto.
Qed.

(*
Lemma computes_to_valc_mkc_try_if_exc {o} :
  forall lib (t : @CTerm o) a c e n x v,
    computes_to_excc lib n t x
    -> computes_to_valc lib (mkc_try t a c e) v
    -> computes_to_valc lib (mkc_atom_eq a n (substc x c e) (mkc_exception n x)) v.
Proof.
  introv ce cv.
  destruct_cterms.
  allunfold @computes_to_excc.
  allunfold @computes_to_valc; allsimpl.
  pose proof (implies_reduces_to_trycatch lib x1 x2 x3 x c x4) as h.
  repeat (autodimp h hyp).
  eapply reduces_to_value_eq in cv;[|exact h]; auto.
Qed.

Lemma spM_cond2 {o} :
  forall lib (F f : @CTerm o) n k,
    member lib F (mkc_fun nat2nat mkc_tnat)
    -> member lib f nat2nat
    -> cequivc lib (mkc_apply2 (spM_c F) (mkc_nat n) f) (mkc_nat k)
    -> cequivc lib (mkc_apply F f) (mkc_nat k).
Proof.
  introv mF mf ceq.
  eapply cequivc_trans in ceq;
    [|apply cequivc_sym; apply cequivc_apply2_spM_c].
  rw @test_c_eq in ceq.

  destruct (fresh_atom o (getc_utokens F ++ getc_utokens f)) as [a nia].
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (cequivc_fresh_nat_implies
                lib nvare
                (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f)
                a k) as ceq1.
  repeat (autodimp ceq1 hyp).
  { destruct_cterms; allunfold @getc_utokens; allsimpl.
    allunfold @getcv_utokens; allsimpl; allrw app_nil_r; allrw in_app_iff; sp. }

  rw @substc_test_try2_cv in ceq1.

  eapply cequivc_trans in ceq1;
    [|apply simpl_cequivc_mkc_try;
       [apply implies_cequivc_apply;
         [apply cequivc_refl|apply cequivc_sym; apply cequiv_bound2_c_cbv]
       |apply cequivc_refl]
    ].
  apply cequivc_nat_implies in ceq1.

  pose proof (hasvalue_likec_try
                lib
                (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                (mkc_utoken a) nvarc (mkcv_axiom nvarc)) as hv.
  autodimp hv hyp.
  { eapply computes_to_valc_implies_hasvalue_likec;exact ceq1. }

  apply hasvalue_likec_implies_or in hv; repndors.

  - apply hasvaluec_computes_to_valc_implies in hv; exrepnd.
    pose proof (computes_to_valc_mkc_try
                  lib
                  (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                  (mkc_utoken a) nvarc (mkcv_axiom nvarc)
                  b (PKa a)) as comp.
    repeat (autodimp comp hyp).
    { apply computes_to_pkc_refl; apply mkc_utoken_eq_pk2termc. }

    eapply computes_to_valc_eq in comp;[|exact ceq1]; subst.

    assert (computes_to_valc lib (mkc_apply F (lam_force_nat_c nvarx nvarz f)) (mkc_nat k)) as comp.
    { eapply (computes_to_valc_differ_force2 _ _ _ n a f);[|exact hv0].
      allrw @get_cterm_apply.
      simpl.
      fold (@mk_vbot o nvarz).
      fold (sp_force_nat (mk_var nvarx) nvarx nvarz (get_cterm f)).
      fold (spexc a).
      fold (bound2_cbv (mk_var nvarx) nvarx nvarz n (get_cterm f) a).
      apply differ_force_oterm; simpl; auto.
      introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow.
      apply differ_force_oterm; simpl; auto.
      introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow. }

    pose proof (equality_lam_force_nat_c_in_nat2nat lib nvarx nvarz f mf) as h.
    apply equality_in_fun in mF; repnd.
    apply mF in h.
    apply equality_in_tnat in h.
    apply equality_of_nat_imp_tt in h.
    unfold equality_of_nat_tt in h; exrepnd.
    computes_to_eqval.
    allapply @eq_mkc_nat_implies; subst; auto.
    apply computes_to_valc_implies_cequivc; auto.

  - provefalse.

    apply raises_exceptionc_as_computes_to_excc in hv; exrepnd.
    eapply computes_to_valc_mkc_try_if_exc in ceq1;[|exact hv1].
    apply computes_to_valc_mkc_atom_eq_pk_implies in ceq1; exrepnd.
    allrw @substc_mkcv_axiom.
    boolvar.

    + apply computes_to_valc_isvalue_eq in ceq1; eauto 3 with slow; ginv.

    + eapply computes_to_valc_and_excc_false in ceq1; tcsp.
      apply computes_to_excc_iff_reduces_toc.
      apply reduces_to_symm.
Qed.
*)


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
