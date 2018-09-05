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

  Authors: Abhishek Anand & Vincent Rahli

 *)


Require Export computation9.
Require Export continuity_defs_ceq.
Require Export psquash.
Require Export substc_more.
Require Export per_props_isect.
Require Export per_props_equality.
Require Export per_props_nat.
Require Export per_props_pertype.


Lemma chaltsc_axiom {o} :
  forall (lib : @library o), chaltsc lib mkc_axiom.
Proof.
  introv; spcast.
  unfold hasvaluec, hasvalue; simpl.
  exists (@mk_axiom o); eauto 3 with slow.
Qed.
Hint Resolve chaltsc_axiom : slow.

Lemma chaltsc_zero {o} :
  forall (lib : @library o), chaltsc lib mkc_zero.
Proof.
  introv; spcast.
  unfold hasvaluec, hasvalue; simpl.
  exists (@mk_zero o); eauto 3 with slow.
Qed.
Hint Resolve chaltsc_zero : slow.

Lemma mkc_isaxiom_axiom {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_isaxiom mkc_axiom a b) a.
Proof.
  introv; destruct_cterms.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_isaxiom; eauto 3 with slow.
Qed.

Lemma mkc_isaxiom_zero {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_isaxiom mkc_zero a b) b.
Proof.
  introv; destruct_cterms.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_isaxiom; eauto 3 with slow.
Qed.

Lemma implies_cequiv_halts {o} :
  forall lib (a b : @NTerm o),
    cequiv lib a b
    -> cequiv lib (mk_halts a) (mk_halts b).
Proof.
  introv ceq.
  unfold mk_halts.
  apply cequiv_decomp_approx; dands; eauto 3 with slow.
  apply cequiv_mk_cbv; eauto 3 with slow.
Qed.

Lemma implies_cequivc_halts {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_halts a) (mkc_halts b).
Proof.
  introv ceq; destruct_cterms; allunfold @cequivc; allsimpl.
  apply implies_cequiv_halts; auto.
Qed.

Lemma approx_mk_isaxiom {o} :
  forall lib (a1 a2 b1 b2 c1 c2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib (mk_isaxiom a1 b1 c1) (mk_isaxiom a2 b2 c2).
Proof.
  introv apra aprb aprc.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  applydup @approx_isprog in aprc.
  repnd.

  apply howetheorem1; allrw @isprogram_eq; try (apply isprog_isaxiom); auto.
  apply (apso _ _ _ _ [nobnd a2, nobnd b2, nobnd c2]); simpl; auto.

  - apply lblift_sub_eq; simpl; dands; auto.
    introv i; repndors; tcsp; ginv;
    apply blift_sub_nobnd_congr; auto;
    apply le_bin_rel_approx1_eauto; auto.

  - apply approx_open_refl.
    apply nt_wf_isaxiom; dands; eauto 3 with slow.
Qed.

Lemma cequiv_mk_isaxiom {o} :
  forall lib (a1 a2 b1 b2 c1 c2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib (mk_isaxiom a1 b1 c1) (mk_isaxiom a2 b2 c2).
Proof.
  introv ceqa ceqb ceqc.
  allunfold @cequiv; repnd; dands; apply approx_mk_isaxiom; auto.
Qed.

Lemma cequivc_mkc_isaxiom {o} :
  forall lib (a1 a2 b1 b2 c1 c2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib (mkc_isaxiom a1 b1 c1) (mkc_isaxiom a2 b2 c2).
Proof.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_isaxiom; auto.
Qed.

Lemma decidable_mkc_axiom {o} :
  forall (t : @CTerm o), decidable (t = mkc_axiom).
Proof.
  introv.
  destruct_cterms.
  destruct x as [v|f|op bs]; try (complete (right; intro xx; ginv)).
  dopid op as [c|nc|e|a] Case; try (complete (right; intro xx; ginv)).
  destruct c; try (complete (right; intro xx; ginv)).
  destruct bs; try (complete (right; intro xx; ginv)).
  fold_terms.
  left.
  apply cterm_eq; simpl; auto.
Qed.

Lemma isprogram_axiom_implies {p} :
  forall bs : list (@BTerm p),
    isprogram (oterm (Can NAxiom) bs) -> bs = [].
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  destruct bs; allsimpl; tcsp.
Qed.

Lemma isprog_axiom_implies {p} :
  forall bs : list (@BTerm p),
    isprog (oterm (Can NAxiom) bs) -> bs = [].
Proof.
  introv isp.
  apply isprog_eq in isp.
  apply isprogram_axiom_implies in isp;auto.
Qed.

Lemma mkc_isaxiom_not_axiom {o} :
  forall lib t (a b : @CTerm o),
    iscvalue t
    -> t <> mkc_axiom
    -> cequivc lib (mkc_isaxiom t a b) b.
Proof.
  introv isc d; destruct_cterms.
  unfold cequivc; simpl.
  unfold iscvalue in isc; allsimpl.
  assert (x1 <> mk_axiom) as d'.
  { intro xx; subst; destruct d; apply cterm_eq; simpl; auto. }
  clear d.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  { apply isprogram_isaxiom; eauto 3 with slow. }
  apply reduces_to_if_step; csunf; simpl.
  destruct x1 as [v|f|op bs]; try (complete (inversion isc; allsimpl; tcsp));[].
  dopid op as [c|nc|e|a] Case; try (complete (inversion isc; allsimpl; tcsp));[].
  destruct c; auto.
  apply isprog_axiom_implies in i1; subst; fold_terms.
  provefalse; tcsp.
Qed.

Lemma tequality_mkc_uand {o} :
  forall lib (t1 t2 u1 u2 : @CTerm o),
    tequality lib (mkc_uand t1 t2) (mkc_uand u1 u2)
    <=> (tequality lib t1 u1 # tequality lib t2 u2).
Proof.
  introv.

  split; introv k; repnd.

  - eapply tequality_respects_alphaeqc_left in k;
    [|apply (mkc_uand_aeq nvarx)].
    eapply tequality_respects_alphaeqc_right in k;
    [|apply (mkc_uand_aeq nvarx)].

    apply tequality_isect in k; repnd.
    clear k0.

    (* ---- first the LHS ----  *)
    pose proof (k mkc_axiom mkc_axiom) as q.
    autodimp q hyp.
    { apply equality_in_base_iff; spcast; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left in q;
      [|apply substc_mkcv_ufun].
    eapply tequality_respects_alphaeqc_right in q;
      [|apply substc_mkcv_ufun].

    allrw @mkcv_isaxiom_substc.
    allrw @mkcv_halts_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_ufun in q; repnd.
    clear q0.
    autodimp q hyp.
    { apply inhabited_halts; eauto 3 with slow. }

    eapply tequality_respects_cequivc_left in q;[|apply mkc_isaxiom_axiom].
    eapply tequality_respects_cequivc_right in q;[|apply mkc_isaxiom_axiom].
    dands; auto.

    (* ---- now the RHS ----  *)
    clear q.
    pose proof (k mkc_zero mkc_zero) as q.
    autodimp q hyp.
    { apply equality_in_base_iff; spcast; eauto 3 with slow. }

    eapply tequality_respects_alphaeqc_left in q;
      [|apply substc_mkcv_ufun].
    eapply tequality_respects_alphaeqc_right in q;
      [|apply substc_mkcv_ufun].

    allrw @mkcv_isaxiom_substc.
    allrw @mkcv_halts_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_ufun in q; repnd.
    clear q0.
    autodimp q hyp.
    { apply inhabited_halts; eauto 3 with slow. }

    eapply tequality_respects_cequivc_left in q;[|apply mkc_isaxiom_zero].
    eapply tequality_respects_cequivc_right in q;[|apply mkc_isaxiom_zero].
    auto.

  - eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym;apply (mkc_uand_aeq nvarx)|].
    eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym;apply (mkc_uand_aeq nvarx)|].

    apply tequality_isect.
    dands; eauto 3 with slow.

    introv eb.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_mkcv_ufun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_mkcv_ufun|].

    allrw @mkcv_isaxiom_substc.
    allrw @mkcv_halts_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply equality_in_base in eb; spcast.

    apply tequality_mkc_ufun.
    dands.

    { eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;apply implies_cequivc_halts;exact eb|].
      apply tequality_mkc_halts; sp. }

    introv inh.

    eapply tequality_respects_cequivc_right;
      [apply cequivc_mkc_isaxiom;
        [exact eb
        |apply cequivc_refl
        |apply cequivc_refl]
      |].

    clear dependent a'.

    apply inhabited_halts in inh; spcast.
    apply hasvaluec_computes_to_valc_implies in inh; exrepnd.
    rw @computes_to_valc_iff_reduces_toc in inh0; repnd.

    apply (tequality_respects_cequivc_left _ (mkc_isaxiom b t1 t2));
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        destruct_cterms; allunfold @reduces_toc; allsimpl;
        apply reduces_to_prinarg; auto
      |].

    apply (tequality_respects_cequivc_right _ _ (mkc_isaxiom b u1 u2));
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        destruct_cterms; allunfold @reduces_toc; allsimpl;
        apply reduces_to_prinarg; auto
      |].

    clear dependent a.

    destruct (decidable_mkc_axiom b) as [d|d]; subst.

    { eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply mkc_isaxiom_axiom|].
      eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply mkc_isaxiom_axiom|].
      dands; auto. }

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
    auto.
Qed.

Lemma type_mkc_uand {o} :
  forall lib (t1 t2 : @CTerm o),
    type lib (mkc_uand t1 t2)
    <=> (type lib t1 # type lib t2).
Proof.
  introv.
  rw @tequality_mkc_uand; sp.
Qed.

Lemma type_mkc_member {o} :
  forall lib (a A : @CTerm o),
    type lib (mkc_member a A)
    <=> type lib A.
Proof.
  introv.
  rw @tequality_mkc_member_sp.
  split; intro k; repnd; dands; auto.
  right; spcast; auto.
Qed.

Lemma equality_in_uand {o} :
  forall lib (a b t u : @CTerm o),
    equality lib a b (mkc_uand t u)
    <=> (equality lib a b t
         # equality lib a b u).
Proof.
  introv; split; intro k; repnd; tcsp.

  - eapply alphaeqc_preserving_equality in k;
    [|apply (mkc_uand_aeq nvarx)].
    apply equality_in_isect2 in k; repnd.
    clear k0.

    (* LHS *)

    pose proof (k mkc_axiom mkc_axiom) as q.
    autodimp q hyp.
    { apply equality_in_base_iff; spcast; eauto 3 with slow. }
    repnd.

    clear q.
    eapply alphaeqc_preserving_equality in q0;
      [|apply substc_mkcv_ufun].

    allrw @mkcv_isaxiom_substc.
    allrw @mkcv_halts_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply equality_in_ufun in q0; repnd.
    clear q1 q2.
    autodimp q0 hyp.
    { apply inhabited_halts; eauto 3 with slow. }

    eapply cequivc_preserving_equality in q0;[|apply mkc_isaxiom_axiom].
    dands; auto.

    (* RHS *)

    clear q0.
    pose proof (k mkc_zero mkc_zero) as q.
    autodimp q hyp.
    { apply equality_in_base_iff; spcast; eauto 3 with slow. }
    repnd.

    clear q.
    eapply alphaeqc_preserving_equality in q0;
      [|apply substc_mkcv_ufun].

    allrw @mkcv_isaxiom_substc.
    allrw @mkcv_halts_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply equality_in_ufun in q0; repnd.
    clear q1 q2.
    autodimp q0 hyp.
    { apply inhabited_halts; eauto 3 with slow. }

    eapply cequivc_preserving_equality in q0;[|apply mkc_isaxiom_zero].
    auto.

  - applydup @inhabited_implies_tequality in k.
    applydup @inhabited_implies_tequality in k0.

    eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym;apply (mkc_uand_aeq nvarx)].

    apply equality_in_isect2; dands.
    { apply tequality_base. }

    introv eb.
    apply equality_in_base_iff in eb; spcast.

    dands.

    + eapply alphaeqc_preserving_equality;
      [|apply alphaeqc_sym;apply substc_mkcv_ufun].

      allrw @mkcv_isaxiom_substc.
      allrw @mkcv_halts_substc.
      allrw @csubst_mk_cv.
      allrw @mkc_var_substc.

      apply equality_in_ufun.

      dands.

      * apply type_mkc_halts.

      * introv inh.
        clear dependent a'.

        apply inhabited_halts in inh; spcast.
        apply hasvaluec_computes_to_valc_implies in inh; exrepnd.
        rw @computes_to_valc_iff_reduces_toc in inh0; repnd.

        apply (type_respects_cequivc _ (mkc_isaxiom b0 t u));
          [apply cequivc_sym;
            apply reduces_toc_implies_cequivc;
            destruct_cterms; allunfold @reduces_toc; allsimpl;
            apply reduces_to_prinarg; auto
          |].

        clear dependent a0.

        destruct (decidable_mkc_axiom b0) as [d|d]; subst.

        { eapply type_respects_cequivc;
          [apply cequivc_sym;apply mkc_isaxiom_axiom|];
          auto. }

        eapply type_respects_cequivc;
          [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|];
          auto.

      * introv inh.
        clear dependent a'.

        apply inhabited_halts in inh; spcast.
        apply hasvaluec_computes_to_valc_implies in inh; exrepnd.
        rw @computes_to_valc_iff_reduces_toc in inh0; repnd.

        apply (cequivc_preserving_equality _ _ _ (mkc_isaxiom b0 t u));
          [|apply cequivc_sym;
             apply reduces_toc_implies_cequivc;
             destruct_cterms; allunfold @reduces_toc; allsimpl;
             apply reduces_to_prinarg; auto].

        clear dependent a0.

        destruct (decidable_mkc_axiom b0) as [d|d]; subst.

        { eapply cequivc_preserving_equality;
          [|apply cequivc_sym;apply mkc_isaxiom_axiom];
          auto. }

        eapply cequivc_preserving_equality;
          [|apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto];
          auto.

    + eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_mkcv_ufun|].
      eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_mkcv_ufun|].

      allrw @mkcv_isaxiom_substc.
      allrw @mkcv_halts_substc.
      allrw @csubst_mk_cv.
      allrw @mkc_var_substc.

      apply tequality_mkc_ufun.
      dands.

      { eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;apply implies_cequivc_halts;exact eb|].
        apply tequality_mkc_halts; sp. }

      introv inh.

      eapply tequality_respects_cequivc_right;
        [apply cequivc_mkc_isaxiom;
          [exact eb
          |apply cequivc_refl
          |apply cequivc_refl]
        |].

      clear dependent a'.
      rw @fold_type.

      apply inhabited_halts in inh; spcast.
      apply hasvaluec_computes_to_valc_implies in inh; exrepnd.
      rw @computes_to_valc_iff_reduces_toc in inh0; repnd.

      apply (type_respects_cequivc _ (mkc_isaxiom b0 t u));
        [apply cequivc_sym;
          apply reduces_toc_implies_cequivc;
          destruct_cterms; allunfold @reduces_toc; allsimpl;
          apply reduces_to_prinarg; auto
        |].

      clear dependent a.

      destruct (decidable_mkc_axiom b0) as [d|d]; subst.

      { eapply type_respects_cequivc;
        [apply cequivc_sym;apply mkc_isaxiom_axiom|];
        auto. }

      eapply type_respects_cequivc;
        [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
      auto.
Qed.

Lemma inhabited_mkc_uand {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_uand a b)
    <=> {t : CTerm , member lib t a # member lib t b}.
Proof.
  introv.
  unfold inhabited_type.
  split; introv inh; exrepnd.
  - rw @equality_in_uand in inh0; repnd.
    exists t; dands; auto.
  - exists t.
    apply equality_in_uand; sp.
Qed.

Lemma member_iff_inhabited_mkc_apply2_mkc_psquash_per {o} :
  forall lib (t1 t2 T : @CTerm o),
    inhabited_type lib (mkc_apply2 (mkc_psquash_per nvarx nvary T) t1 t2)
    <=> (member lib t1 T # member lib t2 T).
Proof.
  introv.

  split; introv inh.

  - eapply inhabited_type_respects_cequivc in inh;
    [|apply cequivc_beta2].
    rw @mkcv_lam_substc in inh; try (complete (intro xx; ginv)).

    eapply inhabited_type_respects_cequivc in inh;
      [|apply cequivc_beta].

    eapply inhabited_type_respects_alphaeqc in inh;
      [|apply substc_alphaeqcv;apply substc2_uand].

    eapply inhabited_type_respects_alphaeqc in inh;
      [|apply substc_mkcv_uand].

    allrw @substc2_member.
    allrw @mkcv_member_substc.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in inh; try (complete (intro xx; ginv)).
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    allrw @inhabited_mkc_uand.
    exrepnd.
    allrw @equality_in_member; repnd; auto.

  - eapply inhabited_type_respects_cequivc;
    [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply inhabited_type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    eapply inhabited_type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_alphaeqcv;
        apply substc2_uand|].

    eapply inhabited_type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_mkcv_uand
      |].

    allrw @substc2_member.
    allrw @mkcv_member_substc.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r; try (complete (intro xx; ginv)).
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    allrw @inhabited_mkc_uand.
    exists (@mkc_axiom o).
    allrw <- @member_member_iff.
    auto.
Qed.

Lemma implies_tequality_mkc_psquash {o} :
  forall lib (t1 t2 : @CTerm o),
    type lib t1
    -> type lib t2
    -> (forall t, member lib t t1 <=> member lib t t2)
    -> tequality lib (mkc_psquash t1) (mkc_psquash t2).
Proof.
  introv tt1 tt2 tiff.
  unfold mkc_psquash.
  rw @tequality_mkc_pertype.
  dands.

  (* type 1 *)
  - introv.
    unfold mkc_psquash_per.

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_alphaeqcv;
        apply substc2_uand|].

    eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_mkcv_uand
      |].

    allrw @substc2_member.
    allrw @mkcv_member_substc.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r; try (complete (intro xx; ginv)).
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    apply type_mkc_uand.
    allrw @type_mkc_member.
    sp.

  (* type 2 *)
  - introv.
    unfold mkc_psquash_per.

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_alphaeqcv;
        apply substc2_uand|].

    eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;
        apply substc_mkcv_uand
      |].

    allrw @substc2_member.
    allrw @mkcv_member_substc.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r; try (complete (intro xx; ginv)).
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    apply type_mkc_uand.
    allrw @type_mkc_member.
    sp.

  (* extensional eq *)
  - introv.
    allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per.
    split; introv mem; repnd; dands; apply tiff; auto.

  (* PER *)
  - unfold is_per_type; dands.

    (* symmetry *)
    + introv inh.
      allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per; sp.

    (* transitivity *)
    + introv inh1 inh2.
      allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per; sp.
Qed.

Lemma tequality_mkc_psquash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib (mkc_psquash t1) (mkc_psquash t2)
    <=> (type lib t1
         # type lib t2
         # (forall t, member lib t t1 <=> member lib t t2)).
Proof.
  introv; split; intro k; try (apply implies_tequality_mkc_psquash; tcsp);[].

  unfold mkc_psquash in k.
  rw @tequality_mkc_pertype in k; repnd.

  (* let's get that t1 is a type *)
  pose proof (k0 mkc_axiom mkc_axiom) as tt1.
  unfold mkc_psquash_per in tt1.

  eapply type_respects_cequivc in tt1;[|apply cequivc_beta2].
  rw @mkcv_lam_substc in tt1; try (complete (intro xx; ginv)).
  eapply type_respects_cequivc in tt1;[|apply cequivc_beta].
  eapply type_respects_alphaeqc in tt1;[|apply substc_alphaeqcv; apply substc2_uand].
  eapply type_respects_alphaeqc in tt1;[|apply substc_mkcv_uand].

  allrw @substc2_member.
  allrw @mkcv_member_substc.
  allrw @substc2_mk_cv_app_l.
  rw @substc2_mk_cv_app_r in tt1; try (complete (intro xx; ginv)).
  allrw @substc2_mk_cv.
  allrw @csubst_mk_cv.
  allrw @mkc_var_substc.
  apply type_mkc_uand in tt1; repnd.
  allrw @type_mkc_member; GC.

  (* let's get that t2 is a type *)
  pose proof (k1 mkc_axiom mkc_axiom) as tt2.
  unfold mkc_psquash_per in tt2.

  eapply type_respects_cequivc in tt2;[|apply cequivc_beta2].
  rw @mkcv_lam_substc in tt2; try (complete (intro xx; ginv)).
  eapply type_respects_cequivc in tt2;[|apply cequivc_beta].
  eapply type_respects_alphaeqc in tt2;[|apply substc_alphaeqcv; apply substc2_uand].
  eapply type_respects_alphaeqc in tt2;[|apply substc_mkcv_uand].

  allrw @substc2_member.
  allrw @mkcv_member_substc.
  allrw @substc2_mk_cv_app_l.
  rw @substc2_mk_cv_app_r in tt2; try (complete (intro xx; ginv)).
  allrw @substc2_mk_cv.
  allrw @csubst_mk_cv.
  allrw @mkc_var_substc.
  apply type_mkc_uand in tt2; repnd.
  allrw @type_mkc_member; GC.

  dands; auto.
  introv.

  pose proof (k2 t t) as q.
  allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per.
  destruct q as [q1 q2].
  split; intro mem.
  - autodimp q1 hyp; sp.
  - autodimp q2 hyp; sp.
Qed.

Lemma sp_implies_tequality_mkc_psquash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> tequality lib (mkc_psquash t1) (mkc_psquash t2).
Proof.
  introv teq.
  apply tequality_mkc_psquash.
  dands.

  - apply tequality_refl in teq; auto.

  - apply tequality_sym in teq; apply tequality_refl in teq; auto.

  - introv; split; intro mem.

    + eapply tequality_preserving_equality;[exact mem|]; auto.

    + eapply tequality_preserving_equality;[exact mem|]; auto.
      apply tequality_sym; auto.
Qed.

Lemma implies_equality_in_mkc_psquash {o} :
  forall lib (a b T : @CTerm o),
    member lib a T
    -> member lib b T
    -> equality lib a b (mkc_psquash T).
Proof.
  introv mem1 mem2.
  unfold mkc_psquash.

  apply equality_in_mkc_pertype2; dands.

  - apply member_iff_inhabited_mkc_apply2_mkc_psquash_per; sp.

  - apply sp_implies_tequality_mkc_psquash.
    apply inhabited_implies_tequality in mem1; sp.
Qed.

Lemma equality_in_mkc_psquash {o} :
  forall lib (a b T : @CTerm o),
    equality lib a b (mkc_psquash T)
    <=> (member lib a T # member lib b T).
Proof.
  introv; split; introv k; try (apply implies_equality_in_mkc_psquash; sp).
  unfold mkc_psquash in k.

  apply equality_in_mkc_pertype2 in k; repnd.
  apply member_iff_inhabited_mkc_apply2_mkc_psquash_per in k0; sp.
Qed.

Ltac ntsi :=
  match goal with
      [ p : POpid , H : context[nuprli ?lib ?i] |- _ ] =>
      pose proof (@nuprli_type_system p lib i) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprli_value_respecting_left {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> cequivc lib t1 t3
    -> nuprli lib i t3 t2 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli lib i t1 t3 eq) as eq13
      by (apply nts_tyv; auto; apply nts_tyt with (T2 := t2); auto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprli_value_respecting_right {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> cequivc lib t2 t3
    -> nuprli lib i t1 t3 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli lib i t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Hint Resolve alphaeqc_implies_cequivc : slow.

Lemma nuprli_respects_alphaeqc_left {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> alphaeqc t1 t3
    -> nuprli lib i t3 t2 eq.
Proof.
  intros.
  eapply nuprli_value_respecting_left; eauto; eauto 3 with slow.
Qed.

Lemma nuprli_respects_alphaeqc_right {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq,
    nuprli lib i t1 t2 eq
    -> alphaeqc t2 t3
    -> nuprli lib i t1 t3 eq.
Proof.
  intros.
  eapply nuprli_value_respecting_right; eauto; eauto 3 with slow.
Qed.

Hint Rewrite @substc2_member : slow.
Hint Rewrite @mkcv_member_substc : slow.
Hint Rewrite @mkc_var_substc : slow.
Hint Rewrite @mkcv_halts_substc : slow.
Hint Rewrite @mkcv_isaxiom_substc : slow.
Hint Resolve approxc_refl : slow.

Lemma mkc_halts_mkc_axiom {o} :
  forall (lib : @library o),
    cequivc lib (mkc_halts mkc_axiom) mkc_true.
Proof.
  introv.
  rewrite <- fold_mkc_halts.
  rewrite mkc_true_eq.
  apply cequivc_decomp_approx; dands; eauto 3 with slow.
  unfold cequivc; simpl.
  apply computes_to_value_implies_cequiv; eauto 3 with slow.
  apply isprogram_cbv_iff; dands; eauto 3 with slow.
Qed.

Lemma not_cbv_bot_reduces_to_is_value_like {p} :
  forall lib v u (t : @NTerm p),
    is_value_like lib t
    -> !reduces_to lib (mk_cbv mk_bot v u) t.
Proof.
  introv isv r.
  unfold reduces_to in r; sp.
  revert t isv r.
  induction k as [? ind] using comp_ind_type; sp; allsimpl.
  destruct k.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold is_value_like, isvalue_like in isv; simpl in *; repndors; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; simpl in r1; ginv.
    destruct k.

    + allrw @reduces_in_atmost_k_steps_0; subst.
      unfold is_value_like, isvalue_like in isv; simpl in *; repndors; tcsp.

    + allrw @reduces_in_atmost_k_steps_S; exrepnd.
      csunf r0; simpl in r0; ginv.
      unfold apply_bterm, lsubst in r1; allsimpl.
      apply ind in r1; tcsp.
Qed.

Lemma mkc_halts_mkc_bot {o} :
  forall (lib : @library o),
    cequivc lib (mkc_halts mkc_bot) mkc_false.
Proof.
  introv.
  rewrite <- fold_mkc_halts.
  rewrite mkc_false_eq.
  apply cequivc_decomp_approx; dands; eauto 3 with slow.
  unfold cequivc; simpl.
  split;[|apply bottom_approx_any;apply isprogram_cbv_iff;dands;eauto 3 with slow];[].
  apply approx_assume_hasvalue; eauto 3 with slow;
    try (complete (apply isprogram_cbv_iff;dands;eauto 3 with slow));[].
  introv hv.
  assert False; tcsp.
  unfold hasvalue_like in hv; exrepnd.
  apply not_cbv_bot_reduces_to_is_value_like in hv1; tcsp.
Qed.

Lemma mkc_halts_mkc_zero {o} :
  forall (lib : @library o),
    cequivc lib (mkc_halts mkc_zero) mkc_true.
Proof.
  introv.
  rewrite <- fold_mkc_halts.
  rewrite mkc_true_eq.
  apply cequivc_decomp_approx; dands; eauto 3 with slow.
  unfold cequivc; simpl.
  apply computes_to_value_implies_cequiv; eauto 3 with slow.
  apply isprogram_cbv_iff; dands; eauto 3 with slow.
Qed.

Lemma nuprli_mkc_uand_implies {o} :
  forall lib i (t1 t2 t3 t4 : @CTerm o) per,
    nuprli lib i (mkc_uand t1 t2) (mkc_uand t3 t4) per
    -> (exists per1, nuprli lib i t1 t3 per1) # (exists per2, nuprli lib i t2 t4 per2).
Proof.
  introv h.
  eapply nuprli_respects_alphaeqc_left  in h;[|apply (mkc_uand_aeq nvarx)].
  eapply nuprli_respects_alphaeqc_right in h;[|apply (mkc_uand_aeq nvarx)].
  inversion h; subst; try not_univ;[].
  clear h.

  match goal with
  | [ H : context[per_isect] |- _ ] => rename H into pi
  end.
  unfold per_isect in *; exrepnd.
  unfold type_family in *; exrepnd.
  computes_to_value_isvalue; GC.

  fold (nuprli lib i) in *.
  inversion pi4; subst; try not_univ;[].
  clear pi4.
  match goal with
  | [ H : context[per_base] |- _ ] => rename H into pb
  end.
  unfold per_base in *; repnd.
  computes_to_value_isvalue; GC.

  dands.

  {
    assert (mkc_axiom ~=~(lib) mkc_axiom) as ea by (spcast; eauto 3 with slow).
    apply pb in ea.

    pose proof (pi0 _ _ ea) as pa.
    eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_mkcv_ufun].
    eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_mkcv_ufun].
    autorewrite with slow in *.

    repeat (rewrite <- fold_mkc_ufun in pa).
    inversion pa; subst; try not_univ;[].
    clear pa.

    match goal with
    | [ H : context[per_isect] |- _ ] => rename H into pi
    end.
    unfold per_isect in *; exrepnd.
    unfold type_family in *; exrepnd.
    computes_to_value_isvalue; GC.
    fold (nuprli lib i) in *.

    eapply nuprli_value_respecting_left  in pi6;[|apply mkc_halts_mkc_axiom].
    eapply nuprli_value_respecting_right in pi6;[|apply mkc_halts_mkc_axiom].

    assert (eqa0 <=2=> (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom)) as eqae.
    {
      rewrite mkc_true_eq in pi6.
      inversion pi6; subst; try not_univ;[].
      clear pi6.
      match goal with
      | [ H : context[per_approx] |- _ ] => rename H into pax
      end.
      unfold per_approx in *; exrepnd.
      computes_to_value_isvalue; GC.
      introv.
      rw pax1.
      split; intro q; repnd; dands; auto; spcast; eauto 3 with slow.
    }

    assert (eqa0 mkc_axiom mkc_axiom) as eax.
    { apply eqae; dands; spcast; eauto 3 with slow. }

    pose proof (pi2 _ _ eax) as eq1.
    autorewrite with slow in *.

    eapply nuprli_value_respecting_left  in eq1;[|apply mkc_isaxiom_axiom].
    eapply nuprli_value_respecting_right in eq1;[|apply mkc_isaxiom_axiom].
    eauto.
  }

  {
    assert (mkc_zero ~=~(lib) mkc_zero) as ea by (spcast; eauto 3 with slow).
    apply pb in ea.

    pose proof (pi0 _ _ ea) as pa.
    eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_mkcv_ufun].
    eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_mkcv_ufun].
    autorewrite with slow in *.

    repeat (rewrite <- fold_mkc_ufun in pa).
    inversion pa; subst; try not_univ;[].
    clear pa.

    match goal with
    | [ H : context[per_isect] |- _ ] => rename H into pi
    end.
    unfold per_isect in *; exrepnd.
    unfold type_family in *; exrepnd.
    computes_to_value_isvalue; GC.
    fold (nuprli lib i) in *.

    eapply nuprli_value_respecting_left  in pi6;[|apply mkc_halts_mkc_zero].
    eapply nuprli_value_respecting_right in pi6;[|apply mkc_halts_mkc_zero].

    assert (eqa0 <=2=> (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom)) as eqae.
    {
      rewrite mkc_true_eq in pi6.
      inversion pi6; subst; try not_univ;[].
      clear pi6.
      match goal with
      | [ H : context[per_approx] |- _ ] => rename H into pax
      end.
      unfold per_approx in *; exrepnd.
      computes_to_value_isvalue; GC.
      introv.
      rw pax1.
      split; intro q; repnd; dands; auto; spcast; eauto 3 with slow.
    }

    assert (eqa0 mkc_axiom mkc_axiom) as eax.
    { apply eqae; dands; spcast; eauto 3 with slow. }

    pose proof (pi2 _ _ eax) as eq1.
    autorewrite with slow in *.

    eapply nuprli_value_respecting_left  in eq1;[|apply mkc_isaxiom_zero].
    eapply nuprli_value_respecting_right in eq1;[|apply mkc_isaxiom_zero].
    eauto.
  }
Qed.

Lemma nuprli_mkc_member_implies {o} :
  forall lib i (t1 t2 T1 T2 : @CTerm o) per,
    nuprli lib i (mkc_member t1 T1) (mkc_member t2 T2) per
    -> exists per1, nuprli lib i T1 T2 per1.
Proof.
  introv h.
  repeat (rewrite <- fold_mkc_member in h).
  inversion h; subst; try not_univ;[].
  clear h.

  match goal with
  | [ H : context[per_eq] |- _ ] => rename H into pi
  end.
  unfold per_eq in *; exrepnd.
  computes_to_value_isvalue; GC; eauto.
Qed.

Hint Resolve mkc_uni_in_nuprl : slow.

Lemma equality_base_in_uni {o} :
  forall (lib : @library o) i,
    equality lib mkc_base mkc_base (mkc_uni i).
Proof.
  introv.
  exists (fun A A' => {eqa : per(o) , close lib (univi lib i) A A' eqa}).
  dands; eauto 3 with slow.
  exists (fun t t' => (t) ~=~(lib) (t')).
  apply CL_base; unfold per_base; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve equality_base_in_uni : slow.

Definition approx_mk_isect {o} :
  forall lib (a1 a2 : @NTerm o) v b1 b2,
    isprog_vars [v] b1
    -> isprog_vars [v] b2
    -> approx lib a1 a2
    -> approx_open lib b1 b2
    -> approx lib (mk_isect a1 v b1) (mk_isect a2 v b2).
Proof.
  introv ispb1 ispb2 apr1 apr2.
  applydup @approx_isprog in apr1.
  repnd.
  unfold mk_isect.
  repeat (prove_approx; tcsp; eauto 2 with slow).
  fold (approx_open_bterm lib).
  apply approx_open_implies_approx_open_bterm; auto.
Qed.

Definition cequiv_mk_isect {o} :
  forall lib (a1 a2 : @NTerm o) v b1 b2,
    isprog_vars [v] b1
    -> isprog_vars [v] b2
    -> cequiv lib a1 a2
    -> cequiv_open lib b1 b2
    -> cequiv lib (mk_isect a1 v b1) (mk_isect a2 v b2).
Proof.
  introv isp1 isp2 ceq1 ceq2.
  allunfold @cequiv; repnd.
  allapply @olift_cequiv_approx; repnd.
  dands; apply approx_mk_isect; auto.
Qed.

Lemma implies_cequivc_ufun {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a b
    -> cequivc lib c d
    -> cequivc lib (mkc_ufun a c) (mkc_ufun b d).
Proof.
  introv ceqa ceqb.
  destruct_cterms.
  unfold cequivc in *; simpl in *.
  unfold mk_ufun.
  repeat (rewrite newvar_prog; auto;[]).
  apply cequiv_mk_isect; eauto 3 with slow.
  apply cequiv_implies_cequiv_open; auto.
Qed.

Lemma equality_mkc_psquash_in_uni {o} :
  forall lib (t1 t2 : @CTerm o) i,
    equality lib (mkc_psquash t1) (mkc_psquash t2) (mkc_uni i)
    <=> (member lib t1 (mkc_uni i)
         # member lib t2 (mkc_uni i)
         # (forall t, member lib t t1 <=> member lib t t2)).
Proof.
  introv.
  sp_iff Case; introv h; repnd.

  - Case "->".
    unfold equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ;[].
    duniv j q.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ; try (unfold mkc_psquash in *; not_univ).

    match goal with
    | [ H : context[per_pertype] |- _ ] => rename H into per
    end.
    unfold per_pertype in *; exrepnd.

    computes_to_value_isvalue; GC.
    apply mkc_pertype_eq in per0; subst.
    apply mkc_pertype_eq in per2; subst.
    fold (nuprli lib j0) in *.

    dands.

    { exists eq; dands; auto.
      apply t.

      pose proof (per3 mkc_axiom mkc_axiom) as pa.
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta2].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta2].
      repeat (rw @mkcv_lam_substc in pa; try (complete (intro xx; ginv));[]).
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_mkcv_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_mkcv_uand].
      autorewrite with slow in *.
      rewrite substc2_mk_cv_app_r in pa;[|introv xx;ginv];[].
      autorewrite with slow in *.
      apply nuprli_mkc_uand_implies in pa; exrepnd.
      apply nuprli_mkc_member_implies in pa2; auto. }

    { exists eq; dands; auto.
      apply t.

      pose proof (per4 mkc_axiom mkc_axiom) as pa.
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta2].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta2].
      repeat (rw @mkcv_lam_substc in pa; try (complete (intro xx; ginv));[]).
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_mkcv_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_mkcv_uand].
      autorewrite with slow in *.
      rewrite substc2_mk_cv_app_r in pa;[|introv xx;ginv];[].
      autorewrite with slow in *.
      apply nuprli_mkc_uand_implies in pa; exrepnd.
      apply nuprli_mkc_member_implies in pa2; auto. }

    { introv.

      pose proof (per3 t0 t0) as pa.
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta2].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta2].
      repeat (rw @mkcv_lam_substc in pa; try (complete (intro xx; ginv));[]).
      eapply nuprli_value_respecting_left   in pa;[|apply cequivc_beta].
      eapply nuprli_value_respecting_right  in pa;[|apply cequivc_beta].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_left  in pa;[|apply substc_mkcv_uand].
      eapply nuprli_respects_alphaeqc_right in pa;[|apply substc_mkcv_uand].
      autorewrite with slow in *.
      rewrite substc2_mk_cv_app_r in pa;[|introv xx;ginv];[].
      autorewrite with slow in *.

      pose proof (per4 t0 t0) as pb.
      eapply nuprli_value_respecting_left   in pb;[|apply cequivc_beta2].
      eapply nuprli_value_respecting_right  in pb;[|apply cequivc_beta2].
      repeat (rw @mkcv_lam_substc in pb; try (complete (intro xx; ginv));[]).
      eapply nuprli_value_respecting_left   in pb;[|apply cequivc_beta].
      eapply nuprli_value_respecting_right  in pb;[|apply cequivc_beta].
      eapply nuprli_respects_alphaeqc_left  in pb;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_right in pb;[|apply substc_alphaeqcv; apply substc2_uand].
      eapply nuprli_respects_alphaeqc_left  in pb;[|apply substc_mkcv_uand].
      eapply nuprli_respects_alphaeqc_right in pb;[|apply substc_mkcv_uand].
      autorewrite with slow in *.
      rewrite substc2_mk_cv_app_r in pb;[|introv xx;ginv];[].
      autorewrite with slow in *.

      pose proof (per5 t0 t0) as pc.

      assert ((inhabited_type lib (mkc_uand (mkc_member t0 t1) (mkc_member t0 t1)))
                <=> inhabited_type lib (mkc_uand (mkc_member t0 t2) (mkc_member t0 t2))) as inh.
      { split; intro h.
        - eapply inhabited_type_iff_inhabited_i;[eauto|]; apply pc.
          eapply inhabited_type_iff_inhabited_i;[eauto|]; auto.
        - eapply inhabited_type_iff_inhabited_i;[eauto|]; apply pc.
          eapply inhabited_type_iff_inhabited_i;[eauto|]; auto. }
      clear pc.
      repeat (rw @inhabited_mkc_uand in inh).
      destruct inh as [inh1 inh2].

      split; intro mem.

      { autodimp inh1 hyp; auto.
        - exists (@mkc_axiom o); dands; eauto 3 with slow;
            rw <- @member_member_iff; auto.
        - exrepnd; GC.
          apply equality_in_member in inh1; tcsp. }

      { autodimp inh2 hyp; auto.
        - exists (@mkc_axiom o); dands; eauto 3 with slow;
            rw <- @member_member_iff; auto.
        - exrepnd; GC.
          apply equality_in_member in inh2; tcsp. }
    }

  - unfold mkc_psquash.
    apply mkc_pertype_equality_in_uni.
    dands; introv;
      [| | |].

    { eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      repeat (rw @mkcv_lam_substc; try (complete (intro xx; ginv));[]).
      eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply substc_alphaeqcv; apply substc2_uand|].
      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply substc_mkcv_uand|].
      autorewrite with slow.
      rewrite substc2_mk_cv_app_r;[|introv xx;ginv];[].
      autorewrite with slow in *.

      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply (mkc_uand_aeq nvarx)|].
      apply equality_isect; dands; eauto 3 with slow;[].
      introv eb.
      apply equality_in_base in eb; spcast.

      eapply equality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_ufun|].
      eapply equality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_ufun|].
      autorewrite with slow.

      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;apply implies_cequivc_ufun;
         [apply implies_cequivc_halts;eauto
         |apply cequivc_mkc_isaxiom;
          [eauto|apply cequivc_refl|apply cequivc_refl] ] |].
      clear dependent a.
      rename a' into a.

      repeat rewrite <- fold_mkc_ufun.
      apply equality_isect; dands; eauto 3 with slow.

      { apply equality_in_uni_mkc_halts; eauto 3 with slow. }

      introv eh.
      autorewrite with slow.
      apply equality_in_halts in eh; repnd; spcast.
      clear dependent a0.
      clear dependent a'.
      apply hasvaluec_computes_to_valc_implies in eh0; exrepnd.

      eapply equality_respects_cequivc_left;
        [apply cequivc_mkc_isaxiom;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
         |apply cequivc_refl
         |apply cequivc_refl]
        |].

      eapply equality_respects_cequivc_right;
        [apply cequivc_mkc_isaxiom;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
         |apply cequivc_refl
         |apply cequivc_refl]
        |].

      rw @computes_to_valc_iff_reduces_toc in eh1; repnd.
      clear eh0.

      destruct (decidable_mkc_axiom b); subst.

      { eapply equality_respects_cequivc_left;
          [apply cequivc_sym;apply mkc_isaxiom_axiom|].
        eapply equality_respects_cequivc_right;
          [apply cequivc_sym;apply mkc_isaxiom_axiom|].
        repeat rewrite <- fold_mkc_member.
        apply equality_mkc_equality2_sp_in_uni; dands; auto.
        split; right; spcast; eauto 3 with slow. }

      { eapply equality_respects_cequivc_left;
          [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
        eapply equality_respects_cequivc_right;
          [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
        repeat rewrite <- fold_mkc_member.
        apply equality_mkc_equality2_sp_in_uni; dands; auto.
        split; right; spcast; eauto 3 with slow. }
    }

    { eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      repeat (rw @mkcv_lam_substc; try (complete (intro xx; ginv));[]).
      eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply substc_alphaeqcv; apply substc2_uand|].
      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply substc_mkcv_uand|].
      autorewrite with slow.
      rewrite substc2_mk_cv_app_r;[|introv xx;ginv];[].
      autorewrite with slow in *.

      eapply member_respects_alphaeqc_l;[apply alphaeqc_sym;apply (mkc_uand_aeq nvarx)|].
      apply equality_isect; dands; eauto 3 with slow;[].
      introv eb.
      apply equality_in_base in eb; spcast.

      eapply equality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_ufun|].
      eapply equality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_ufun|].
      autorewrite with slow.

      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;apply implies_cequivc_ufun;
         [apply implies_cequivc_halts;eauto
         |apply cequivc_mkc_isaxiom;
          [eauto|apply cequivc_refl|apply cequivc_refl] ] |].
      clear dependent a.
      rename a' into a.

      repeat rewrite <- fold_mkc_ufun.
      apply equality_isect; dands; eauto 3 with slow.

      { apply equality_in_uni_mkc_halts; eauto 3 with slow. }

      introv eh.
      autorewrite with slow.
      apply equality_in_halts in eh; repnd; spcast.
      clear dependent a0.
      clear dependent a'.
      apply hasvaluec_computes_to_valc_implies in eh0; exrepnd.

      eapply equality_respects_cequivc_left;
        [apply cequivc_mkc_isaxiom;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
         |apply cequivc_refl
         |apply cequivc_refl]
        |].

      eapply equality_respects_cequivc_right;
        [apply cequivc_mkc_isaxiom;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto
         |apply cequivc_refl
         |apply cequivc_refl]
        |].

      rw @computes_to_valc_iff_reduces_toc in eh1; repnd.
      clear eh0.

      destruct (decidable_mkc_axiom b); subst.

      { eapply equality_respects_cequivc_left;
          [apply cequivc_sym;apply mkc_isaxiom_axiom|].
        eapply equality_respects_cequivc_right;
          [apply cequivc_sym;apply mkc_isaxiom_axiom|].
        repeat rewrite <- fold_mkc_member.
        apply equality_mkc_equality2_sp_in_uni; dands; auto.
        split; right; spcast; eauto 3 with slow. }

      { eapply equality_respects_cequivc_left;
          [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
        eapply equality_respects_cequivc_right;
          [apply cequivc_sym;apply mkc_isaxiom_not_axiom;auto|].
        repeat rewrite <- fold_mkc_member.
        apply equality_mkc_equality2_sp_in_uni; dands; auto.
        split; right; spcast; eauto 3 with slow. }
    }

    { repeat rw @member_iff_inhabited_mkc_apply2_mkc_psquash_per.
      split; intro q; repnd; dands; apply h; tcsp. }

    { unfold is_per_type; dands.

      + introv inh.
        allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per; sp.

      + introv inh1 inh2.
        allrw @member_iff_inhabited_mkc_apply2_mkc_psquash_per; sp. }
Qed.
