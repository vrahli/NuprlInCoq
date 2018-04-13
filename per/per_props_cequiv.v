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


Require Export per_props_tacs.
Require Export per_props_util.


(*(* MOVE *)
Lemma mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies {o} :
  forall {lib} (bar : @BarLib o lib) a b c d,
    (mkc_cequiv a b) ==b==>(bar) (mkc_cequiv c d)
    -> all_in_bar bar (fun lib => a ~=~(lib) c # b ~=~(lib) d).
Proof.
  introv comp br ext.
  pose proof (comp lib' br lib'0 ext) as comp; simpl in *; exrepnd; spcast.
  eapply ccequivc_ext_cequiv in comp1.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow; subst.
  apply dest_close_tacs.cequivc_decomp_cequiv in comp0; repnd; dands; spcast; auto.
Qed.

(* MOVE *)
Lemma mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies {o} :
  forall {lib} (bar : @BarLib o lib) a b c d,
    (mkc_approx a b) ==b==>(bar) (mkc_approx c d)
    -> all_in_bar bar (fun lib => a ~=~(lib) c # b ~=~(lib) d).
Proof.
  introv comp br ext.
  pose proof (comp lib' br lib'0 ext) as comp; simpl in *; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow; subst.
  apply cequivc_decomp_approx in comp0; repnd; dands; spcast; auto.
Qed.*)

Lemma dest_nuprl_cequiv {o} :
  forall (lib : @SL o) (a b c d : @CTerm o) eq,
    nuprl lib (mkc_cequiv a b) (mkc_cequiv c d) eq
    -> per_bar (per_cequiv nuprl) lib (mkc_cequiv a b) (mkc_cequiv c d) eq.
Proof.
  introv cl.
  eapply dest_close_per_cequiv_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_cequiv {o} :
  forall i (lib : @SL o) (a b c d : @CTerm o) eq,
    nuprli i lib (mkc_cequiv a b) (mkc_cequiv c d) eq
    -> per_bar (per_cequiv (nuprli i)) lib (mkc_cequiv a b) (mkc_cequiv c d) eq.
Proof.
  introv cl.
  eapply dest_close_per_cequiv_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_approx {o} :
  forall i (lib : @SL o) (a b c d : @CTerm o) eq,
    nuprli i lib (mkc_approx a b) (mkc_approx c d) eq
    -> per_bar (per_approx (nuprli i)) lib (mkc_approx a b) (mkc_approx c d) eq.
Proof.
  introv cl.
  eapply dest_close_per_approx_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma implies_in_ext_cequivc_iff {o} :
  forall lib (a a' b b' c c' d d' : @CTerm o),
    ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> ccequivc_ext lib c c'
    -> ccequivc_ext lib d d'
    -> in_ext lib (fun lib => a' ~=~(lib) b' <=> c' ~=~(lib) d')
    -> in_ext lib (fun lib => a ~=~(lib) b <=> c ~=~(lib) d).
Proof.
  introv ceqa ceqb ceqc ceqd h ext.
  pose proof (ceqa _ ext) as ceqa.
  pose proof (ceqb _ ext) as ceqb.
  pose proof (ceqc _ ext) as ceqc.
  pose proof (ceqd _ ext) as ceqd.
  pose proof (h _ ext) as h.
  simpl in *.
  split; intro q; spcast.

  { eapply cequivc_trans;[eauto|].
    eapply cequivc_trans;[|apply cequivc_sym;eauto].
    apply cequiv_stable; apply h; spcast.
    eapply cequivc_trans;[apply cequivc_sym;eauto|].
    eapply cequivc_trans;[|eauto];auto. }

  { eapply cequivc_trans;[eauto|].
    eapply cequivc_trans;[|apply cequivc_sym;eauto].
    apply cequiv_stable; apply h; spcast.
    eapply cequivc_trans;[apply cequivc_sym;eauto|].
    eapply cequivc_trans;[|eauto];auto. }
Qed.

Lemma dest_nuprl_cequiv2 {o} :
  forall lib (eq : per(o)) a b c d,
    nuprl lib (mkc_cequiv a b) (mkc_cequiv c d) eq
    ->
    exists (bar : BarLib lib),
      (eq <=2=> (per_bar_eq bar (per_cequiv_eq_bar_lib_per lib a b)))
        # all_in_bar bar (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  introv u.
  apply dest_nuprl_cequiv in u.
  unfold per_bar in u; exrepnd.
  exists bar.

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same; simpl; auto.
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_cequiv in *; exrepnd; spcast.
    repeat ccomputes_to_valc_ext_val.
    eapply eq_term_equals_trans;[eauto|].
    introv; split; intro xx; eapply per_cequiv_eq_bar_respects_ccequivc_ext; eauto 3 with slow.
  }

  {
    apply all_in_bar_in_ext_implies.
    introv br ext.
    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (u0 _ br _ ext xt) as u0; simpl in *.
    unfold per_cequiv in *; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply implies_in_ext_cequivc_iff; eauto.
  }
Qed.

Lemma dest_nuprli_cequiv2 {o} :
  forall i lib (eq : per(o)) a b c d,
    nuprli i lib (mkc_cequiv a b) (mkc_cequiv c d) eq
    ->
    exists (bar : BarLib lib),
      (eq <=2=> (per_bar_eq bar (per_cequiv_eq_bar_lib_per lib a b)))
        # all_in_bar bar (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  introv u.
  apply dest_nuprli_cequiv in u.
  unfold per_bar in u; exrepnd.
  exists bar.

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same; simpl; auto.
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_cequiv in *; exrepnd; spcast.
    repeat ccomputes_to_valc_ext_val.
    eapply eq_term_equals_trans;[eauto|].
    introv; split; intro xx; eapply per_cequiv_eq_bar_respects_ccequivc_ext; eauto 3 with slow.
  }

  {
    apply all_in_bar_in_ext_implies.
    introv br ext.
    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (u0 _ br _ ext xt) as u0; simpl in *.
    unfold per_cequiv in *; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply implies_in_ext_cequivc_iff; eauto.
  }
Qed.

Lemma dest_nuprli_approx2 {o} :
  forall i lib (eq : per(o)) a b c d,
    nuprli i lib (mkc_approx a b) (mkc_approx c d) eq
    ->
    exists (bar : BarLib lib),
      (eq <=2=> (per_bar_eq bar (per_approx_eq_bar_lib_per lib a b)))
        # all_in_bar bar (fun lib => (capproxc lib a b <=> capproxc lib c d)).
Proof.
  introv u.
  apply dest_nuprli_approx in u.
  unfold per_bar in u; exrepnd.
  exists bar.

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same; simpl; auto.
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_approx in *; exrepnd; spcast.
    repeat ccomputes_to_valc_ext_val.
    eapply eq_term_equals_trans;[eauto|].
    introv; split; intro xx; eapply per_approx_eq_bar_respects_ccequivc_ext; eauto 3 with slow.
  }

  {
    apply all_in_bar_in_ext_implies.
    introv br ext.
    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (u0 _ br _ ext xt) as u0; simpl in *.
    unfold per_approx in *; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply implies_in_ext_ccequiv_iff; eauto.
  }
Qed.

Lemma mkc_cequiv_equality_in_uni {o} :
  forall lib (a b c d : @CTerm o) i,
    equality lib (mkc_cequiv a b) (mkc_cequiv c d) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    allunfold @nuprl.

    apply dest_nuprl_uni in e1.
    apply univ_implies_univi_bar3 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (univi_eq_lib_per lib i) (mkc_cequiv a b) (mkc_cequiv c d)) as h by (exists bar; auto).
    clear dependent bar.
    unfold per_bar_eq in h; simpl in *.

    pose proof (@collapse2bars_ext o lib (fun lib' x => univi_eq (univi_bar i) lib' (mkc_cequiv a b) (mkc_cequiv c d))) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in h; clear q.
    exrepnd.
    unfold univi_eq in h0; fold (@nuprli o i) in *.

    apply collapse2bars.
    exists bar.
    introv br ext x.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.

    apply dest_nuprli_cequiv2 in h1; exrepnd.
    exists bar0; auto.

  - Case "<-".
    unfold all_in_ex_bar in *; exrepnd.

    exists (per_bar_eq bar (univi_eq_lib_per lib i)).
    dands; auto; eauto 3 with slow;[].

    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv; simpl.
    unfold univi_eq.

    exists (per_cequiv_eq_bar lib'1 a b).
    apply CL_cequiv.
    exists a b c d; dands; spcast; auto; eauto 3 with slow.

    introv xt.
    eapply (e0 _ br); eauto 3 with slow.
Qed.

Lemma mkc_approx_equality_in_uni {o} :
  forall lib (a b c d : @CTerm o) i,
    equality lib (mkc_approx a b) (mkc_approx c d) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => (capproxc lib a b <=> capproxc lib c d)).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    unfold nuprl in e1.

    apply dest_nuprl_uni in e1.
    apply univ_implies_univi_bar3 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (univi_eq_lib_per lib i) (mkc_approx a b) (mkc_approx c d)) as h by (exists bar; auto).
    clear dependent bar.
    unfold per_bar_eq in h; simpl in *.

    pose proof (@collapse2bars_ext o lib (fun lib' x => univi_eq (univi_bar i) lib' (mkc_approx a b) (mkc_approx c d))) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in h; clear q.
    exrepnd.
    unfold univi_eq in h0; fold (@nuprli o i) in *.

    apply collapse2bars.
    exists bar.
    introv br ext x.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.

    apply dest_nuprli_approx2 in h1; exrepnd.
    exists bar0; auto.

  - Case "<-".
    unfold all_in_ex_bar in *; exrepnd.

    exists (per_bar_eq bar (univi_eq_lib_per lib i)).
    dands; auto; eauto 3 with slow;[].

    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv; simpl.
    unfold univi_eq.

    exists (per_approx_eq_bar lib'1 a b).
    apply CL_approx.
    exists a b c d; dands; spcast; auto; eauto 3 with slow.

    introv xt.
    eapply (e0 _ br); eauto 3 with slow.
Qed.

Lemma member_approx_refl {p} :
  forall lib t, @member p lib mkc_axiom (mkc_approx t t).
Proof.
  intros.
  exists (per_approx_eq_bar lib t t).
  dands; auto.

  {
    apply CL_approx.
    exists t t t t; dands; spcast; auto; eauto 3 with slow refl.
  }

  {
    exists (trivial_bar lib); introv br ext.
    unfold per_approx_eq; dands; spcast;
      eauto 3 with slow refl; try apply computes_to_valc_refl; eauto 3 with slow.
  }
Qed.

Lemma member_cequiv_refl {p} :
  forall lib t, @member p lib mkc_axiom (mkc_cequiv t t).
Proof.
  intros.
  exists (per_cequiv_eq_bar lib t t).
  dands; auto.

  {
    apply CL_cequiv.
    exists t t t t; dands; spcast; auto; eauto 3 with slow.
  }

  {
    exists (trivial_bar lib); introv br ext; unfold per_cequiv_eq; dands; spcast;
      eauto 3 with slow refl; try apply computes_to_valc_refl; eauto 3 with slow.
  }
Qed.

Lemma equal_approx {p} :
  forall lib t u,
    @tequality p lib (mkc_approx t t) (mkc_approx u u).
Proof.
  intros.
  exists (per_approx_eq_bar lib t t).
  apply CL_approx.
  exists t t u u; dands; spcast; eauto 3 with slow.
Qed.

Lemma equal_cequiv {p} :
  forall lib t u,
    @tequality p lib (mkc_cequiv t t) (mkc_cequiv u u).
Proof.
  intros.
  exists (per_cequiv_eq_bar lib t t).
  apply CL_cequiv.
  exists t t u u; dands; spcast; eauto 3 with slow.
Qed.

Lemma member_base {p} :
  forall lib t, @member p lib t mkc_base.
Proof.
  introv.
  exists (per_base_eq lib); dands; auto.
  {
    apply CL_base.
    unfold per_base; dands; spcast; eauto 3 with slow.
  }
  exists (trivial_bar lib).
  introv br ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve member_base : slow.

Lemma member_cequiv {o} :
  forall lib (t1 t2 : @CTerm o),
    ccequivc_ext lib t1 t2
    -> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  introv ceq.
  exists (per_cequiv_eq_bar lib t1 t2); dands; auto.

  {
    apply CL_cequiv.
    exists t1 t2 t1 t2; dands; spcast; auto; eauto 3 with slow.
  }

  exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar.
  introv x.
  unfold per_cequiv_eq; dands; eauto 3 with slow; spcast; eauto 3 with slow.
Qed.

Lemma member_cequiv_bar {o} :
  forall (lib : SL) (t1 t2 : @CTerm o),
    all_in_ex_bar lib (fun lib => ccequivc lib t1 t2)
    -> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  introv ceq.
  exists (per_cequiv_eq_bar lib t1 t2); dands; auto.

  {
    apply CL_cequiv.
    exists t1 t2 t1 t2; dands; spcast; eauto 3 with slow.
  }

  unfold all_in_ex_bar in *; exrepnd.
  exists bar.
  introv br x.
  pose proof (ceq0 _ br _ x) as ceq0; simpl in *.
  unfold per_cequiv_eq; dands; spcast; eauto 2 with slow.
Qed.

Lemma member_approx {o} :
  forall lib (t1 t2 : @CTerm o),
    in_ext lib (fun lib => capproxc lib t1 t2)
    -> member lib mkc_axiom (mkc_approx t1 t2).
Proof.
  introv apr.
  exists (per_approx_eq_bar lib t1 t2); dands; auto.

  {
    apply CL_approx.
    exists t1 t2 t1 t2; dands; spcast; eauto 3 with slow.
  }

  exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar.
  introv x.
  unfold per_approx_eq; dands; eauto 3 with slow; spcast; eauto 3 with slow.
Qed.

Lemma member_approx_bar {o} :
  forall (lib : SL) (bar : BarLib lib) (t1 t2 : @CTerm o),
    all_in_bar bar (fun lib => capproxc lib t1 t2)
    -> member lib mkc_axiom (mkc_approx t1 t2).
Proof.
  introv apr.
  exists (per_approx_eq_bar lib t1 t2); dands; auto.

  {
    apply CL_approx.
    exists t1 t2 t1 t2; dands; spcast; eauto 3 with slow.
  }

  exists bar.
  introv br ext.
  pose proof (apr _ br _ ext) as apr; simpl in *.
  unfold per_approx_eq; dands; spcast; eauto 3 with slow.
Qed.

Lemma member_approx_iff {o} :
  forall (lib : SL) (t1 t2 : @CTerm o),
    all_in_ex_bar lib (fun lib => capproxc lib t1 t2)
    <=> member lib mkc_axiom (mkc_approx t1 t2).
Proof.
  introv; split; intro e;
    try (complete (unfold all_in_ex_bar in *; exrepnd; eapply member_approx_bar; eauto)).

  unfold member, equality in *; exrepnd.
  apply dest_nuprl_approx2 in e1.
  exrepnd.
  apply e1 in e0.
  clear dependent eq.

  assert (exists (bar : BarLib lib), per_bar_eq bar (per_approx_eq_bar_lib_per lib t1 t2) mkc_axiom mkc_axiom) as per by (exists bar; auto).
  clear dependent bar.
  pose proof (@collapse2bars_ext o lib (fun lib' x => per_approx_eq_bar lib' t1 t2 mkc_axiom mkc_axiom)) as q.
  simpl in q; autodimp q hyp; tcsp;[].
  apply q in per; clear q.

  apply collapse2bars.
  exrepnd.
  exists bar.
  introv br ext x.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  unfold per_approx_eq_bar in per0; exrepnd.
  exists bar0; introv br' ext'.
  pose proof (per1 _ br' _ ext') as per1; simpl in *.
  unfold per_approx_eq in *; tcsp.
Qed.

Lemma member_halts_iff {p} :
  forall (lib : SL) (t : @CTerm p),
    all_in_ex_bar lib (fun lib => chaltsc lib t)
    <=> member lib mkc_axiom (mkc_halts t).
Proof.
  introv.
  rewrite <- fold_mkc_halts.
  pose proof (member_approx_iff lib mkc_axiom (mkc_cbv t nvarx (mkcv_axiom nvarx))) as i.
  rw <- i; clear i.
  unfold all_in_ex_bar.

  sp_iff Case.

  - Case "->".
    intro hv; exrepnd.
    exists bar.
    introv br ext.
    pose proof (hv0 lib' br lib'0 ext) as hv0; simpl in *.
    destruct_cterms; simpl in *.
    spcast; allunfold @approxc; allunfold @hasvaluec; allsimpl.
    allrw @isprog_eq.
    generalize (hasvalue_as_approx lib'0 x i); intro e.
    allrw <-; sp.

  - Case "<-".
    intro a; exrepnd.
    exists bar; introv br ext.
    pose proof (a0 lib' br lib'0 ext) as a0; simpl in *.
    destruct_cterms; simpl in *.
    spcast; allunfold @approxc; allunfold @hasvaluec; allsimpl.
    allrw @isprog_eq.
    generalize (hasvalue_as_approx lib'0 x i); intro e.
    allrw; sp.
Qed.

Lemma dest_nuprl_base {o} :
  forall (lib : @SL o) eq,
    nuprl lib mkc_base mkc_base eq
    -> per_bar (per_base nuprl) lib mkc_base mkc_base eq.
Proof.
  introv cl.
  eapply dest_close_per_base_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
  unfold per_base_bar in *; exrepnd.
  exists bar (per_base_eq_lib_per lib).
  dands; auto.

  {
    introv br ext; introv.
    unfold per_base; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym;apply per_bar_eq_per_base_eq_lib_per.
  }
Qed.

Lemma dest_nuprl_base2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_base mkc_base eq
    -> eq <=2=> (per_base_eq lib).
Proof.
  introv u.
  apply dest_nuprl_base in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_per_base_eq_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_base in *; exrepnd; spcast; auto.
Qed.

Lemma equality_in_base {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_base
    -> per_base_eq lib t1 t2.
Proof.
  unfold equality, nuprl; introv e; exrepnd.
  apply dest_nuprl_base2 in e1.
  apply e1 in e0; auto.
Qed.

Lemma equality_in_base_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_base
    <=> per_base_eq lib t1 t2.
Proof.
  intros; split; intro i; try (apply equality_in_base; sp).
  unfold equality, nuprl.
  exists (per_base_eq lib); dands; auto.
  apply CL_base.
  unfold per_base; dands; spcast; eauto 3 with slow.
Qed.

Lemma tequality_base {p} :
  forall lib, @tequality p lib mkc_base mkc_base.
Proof.
  introv.
  exists (per_base_eq lib).
  apply CL_base.
  unfold per_base; dands; spcast; eauto 3 with slow.
Qed.
Hint Immediate tequality_base.

Lemma tequality_mkc_approx {p} :
  forall lib (a b c d : @CTerm p),
    tequality lib (mkc_approx a b) (mkc_approx c d)
    <=>
    all_in_ex_bar lib (fun lib => (capproxc lib a b <=> capproxc lib c d)).
Proof.
  unfold tequality, nuprl; introv; split; intro k; exrepnd.

  {
    apply dest_nuprl_approx2 in k0; exrepnd.
    exists bar; auto.
  }

  {
    unfold all_in_ex_bar in k; exrepnd.
    exists (per_bar_eq bar (per_approx_eq_bar_lib_per lib a b)); dands; auto.
    apply CL_bar.
    exists bar (per_approx_eq_bar_lib_per lib a b); dands; auto;[].
    introv br ext; introv.
    apply CL_approx.
    exists a b c d; dands; spcast; auto 3 with slow.
    introv y.
    apply (k0 _ br); eauto 3 with slow.
  }
Qed.

Lemma chasvaluec_as_capproxc {p} :
  forall lib (a : @CTerm p),
    chaltsc lib a
    <=>
    capproxc lib mkc_axiom (mkc_cbv a nvarx (mkcv_axiom nvarx)).
Proof.
  introv; split; intro k; spcast.
  rw <- @hasvaluec_as_approxc; sp.
  allrw @hasvaluec_as_approxc; sp.
Qed.

Lemma tequality_mkc_halts {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_halts a) (mkc_halts b)
    <=>
    all_in_ex_bar lib (fun lib => (chaltsc lib a <=> chaltsc lib b)).
Proof.
  intros; repeat (rewrite <- fold_mkc_halts).
  rw @tequality_mkc_approx.
  split; intro h; unfold all_in_ex_bar in *; exrepnd; exists bar;
    introv br x; pose proof (h0 lib' br lib'0 x) as h0; simpl in *;
      allrw @chasvaluec_as_capproxc; sp.
Qed.

(*
Lemma tequality_mkc_halts :
  forall a b,
    tequality lib (mkc_halts a) (mkc_halts b)
    <->
    (hasvaluec a <-> hasvaluec b).
Proof.
  sp.
  repeat (rewrite <- fold_mkc_halts).
  rewrite tequality_mkc_approx.
  repeat (rewrite <- hasvaluec_as_approxc); sp.
Qed.
*)

Lemma member_approx_is_axiom {o} :
  forall lib (t t1 t2 : @CTerm o),
    member lib t (mkc_approx t1 t2)
    -> all_in_ex_bar lib (fun lib => t ===>(lib) mkc_axiom).
Proof.
  introv m.
  unfold member, equality in m; exrepnd.
  apply dest_nuprl_approx2 in m1; exrepnd.
  apply m1 in m0.
  clear dependent eq.

  assert (exists (bar : BarLib lib), per_bar_eq bar (per_approx_eq_bar_lib_per lib t1 t2) t t) as per by (exists bar; auto).
  clear dependent bar.
  pose proof (@collapse2bars_ext o lib (fun lib' x => per_approx_eq_bar lib' t1 t2 t t)) as q.
  simpl in q; autodimp q hyp; tcsp;[].
  apply q in per; clear q.

  apply collapse2bars.
  exrepnd.
  exists bar.
  introv br ext x.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  unfold per_approx_eq_bar in per0; exrepnd.
  exists bar0; introv br' ext'.
  pose proof (per1 _ br' _ ext') as per1; simpl in *.
  unfold per_approx_eq in *; tcsp.
Qed.

Lemma member_cequiv_iff {o} :
  forall (lib : SL) (t1 t2 : @CTerm o),
    all_in_ex_bar lib (fun lib => ccequivc lib t1 t2)
    <=> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  sp; split; intro e.

  { spcast; apply member_cequiv_bar; sp. }

  allunfold @member; allunfold @equality; allunfold @nuprl; exrepnd.

  apply dest_nuprl_cequiv2 in e1; exrepnd.
  apply e1 in e0.
  clear dependent eq.

  assert (exists (bar : BarLib lib), per_bar_eq bar (per_cequiv_eq_bar_lib_per lib t1 t2) mkc_axiom mkc_axiom) as per by (exists bar; auto).
  clear dependent bar.
  pose proof (@collapse2bars_ext o lib (fun lib' x => per_cequiv_eq_bar lib' t1 t2 mkc_axiom mkc_axiom)) as q.
  simpl in q; autodimp q hyp; tcsp;[].
  apply q in per; clear q.

  apply collapse2bars.
  exrepnd.
  exists bar.
  introv br ext x.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  unfold per_cequiv_eq_bar in per0; exrepnd.
  exists bar0; introv br' ext'.
  pose proof (per1 _ br' _ ext') as per1; simpl in *.
  unfold per_cequiv_eq in *; tcsp.
Qed.

Lemma tequality_mkc_cequiv {p} :
  forall lib (a b c d : @CTerm p),
    tequality lib (mkc_cequiv a b) (mkc_cequiv c d)
    <=>
    all_in_ex_bar lib (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  unfold tequality, nuprl; sp; split; intro k; exrepnd.

  {
    apply dest_nuprl_cequiv2 in k0; exrepnd.
    exists bar; auto.
  }

  {
    unfold all_in_ex_bar in k; exrepnd.
    exists (per_bar_eq bar (per_cequiv_eq_bar_lib_per lib a b)); dands; auto.
    apply CL_bar.
    exists bar (per_cequiv_eq_bar_lib_per lib a b); dands; auto;[].
    introv br ext; introv.
    apply CL_cequiv.
    exists a b c d; dands; spcast; auto 3 with slow.
    introv y.
    apply (k0 _ br); eauto 3 with slow.
  }
Qed.

Lemma equality_in_approx {o} :
  forall (lib : SL) (a b t1 t2 : @CTerm o),
    all_in_ex_bar lib (fun lib => (capproxc lib t1 t2 # a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom))
    <=> equality lib a b (mkc_approx t1 t2).
Proof.
  sp; split; intro e.

  - unfold all_in_ex_bar in *; exrepnd.
    unfold member, equality.
    exists (per_approx_eq_bar lib t1 t2); dands; auto.

    {
      apply CL_approx.
      exists t1 t2 t1 t2; dands; spcast; eauto 3 with slow.
    }

    {
      exists bar.
      introv br ext.
      apply e0 in ext; tcsp.
      unfold per_approx_eq; tcsp.
    }

  - unfold equality in e; exrepnd.
    apply dest_nuprl_approx2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (per_approx_eq_bar_lib_per lib t1 t2) a b) as per by (exists bar; auto).
    clear dependent bar.
    pose proof (@collapse2bars_ext o lib (fun lib' x => per_approx_eq_bar lib' t1 t2 a b)) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in per; clear q.

    apply collapse2bars.
    exrepnd.
    exists bar.
    introv br ext x.
    pose proof (per0 _ br _ ext x) as per0; simpl in *.
    unfold per_approx_eq_bar in per0; exrepnd.
    exists bar0; introv br' ext'.
    pose proof (per1 _ br' _ ext') as per1; simpl in *.
    unfold per_approx_eq in *; tcsp.
Qed.

Lemma equality_in_mkc_cequiv {o} :
  forall lib a b (t1 t2 : @CTerm o),
    equality lib a b (mkc_cequiv t1 t2)
    <=> all_in_ex_bar lib (fun lib => (a ===>(lib) mkc_axiom
                                       # b ===>(lib) mkc_axiom
                                       # ccequivc lib t1 t2)).
Proof.
  sp; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_cequiv2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (per_cequiv_eq_bar_lib_per lib t1 t2) a b) as per by (exists bar; auto).
    clear dependent bar.
    pose proof (@collapse2bars_ext o lib (fun lib' x => per_cequiv_eq_bar lib' t1 t2 a b)) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in per; clear q.

    apply collapse2bars.
    exrepnd.
    exists bar.
    introv br ext x.
    pose proof (per0 _ br _ ext x) as per0; simpl in *.
    unfold per_cequiv_eq_bar in per0; exrepnd.
    exists bar0; introv br' ext'.
    pose proof (per1 _ br' _ ext') as per1; simpl in *.
    unfold per_cequiv_eq in *; tcsp.

  - unfold all_in_ex_bar in *; exrepnd.
    unfold member, equality.
    exists (per_cequiv_eq_bar lib t1 t2); dands; auto.

    {
      apply CL_cequiv.
      exists t1 t2 t1 t2; dands; spcast; eauto 3 with slow.
    }

    {
      exists bar.
      introv br ext.
      apply e0 in ext; tcsp.
    }
Qed.

Lemma inhabited_cequiv {o} :
  forall lib (t1 t2 : @CTerm o),
    inhabited_type lib (mkc_cequiv t1 t2)
    <=> all_in_ex_bar lib (fun lib => ccequivc lib t1 t2).
Proof.
  unfold inhabited_type.
  introv; split; intro h; exrepnd.
  - rw @equality_in_mkc_cequiv in h0; tcsp.
    unfold all_in_ex_bar in *; exrepnd; exists bar.
    introv br ext; apply h1 in ext; auto; tcsp.
  - exists (@mkc_axiom o).
    apply member_cequiv_iff; auto.
Qed.

Lemma inhabited_halts {o} :
  forall (lib : SL) (t : @CTerm o),
    all_in_ex_bar lib (fun (lib : SL) => chaltsc lib t)
    <=> inhabited_type lib (mkc_halts t).
Proof.
  introv; split; intro h.

  { rw @member_halts_iff in h; exists (@mkc_axiom o); auto. }

  unfold inhabited_type in h; exrepnd.
  unfold member, equality in h0; exrepnd.
  rewrite <- fold_mkc_halts in h0.

  apply dest_nuprl_approx2 in h0; exrepnd.
  apply h0 in h1.
  clear dependent eq.

  assert (exists (bar : BarLib lib), per_bar_eq bar (per_approx_eq_bar_lib_per lib mkc_axiom (mkc_cbv t nvarx (mkcv_axiom nvarx))) t0 t0) as per by (exists bar; auto).
  clear dependent bar.
  pose proof (@collapse2bars_ext o lib (fun lib' x => per_approx_eq_bar lib' mkc_axiom (mkc_cbv t nvarx (mkcv_axiom nvarx)) t0 t0)) as q.
  simpl in q; autodimp q hyp; tcsp;[].
  apply q in per; clear q.

  apply collapse2bars.
  exrepnd.
  exists bar.
  introv br ext x.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  unfold per_approx_eq_bar in per0; exrepnd.
  exists bar0; introv br' ext'.
  pose proof (per1 _ br' _ ext') as per1; simpl in *.
  unfold per_approx_eq in *; repnd; spcast.

  apply hasvaluec_as_approxc; auto.
Qed.

Lemma type_mkc_halts {p} :
  forall (lib : SL) (a : @CTerm p), type lib (mkc_halts a).
Proof.
  introv; rw @tequality_mkc_halts; eauto 3 with slow refl.
Qed.
Hint Immediate type_mkc_halts.

Lemma equality_in_halts {p} :
  forall (lib : SL) (a b t : @CTerm p),
    all_in_ex_bar lib (fun lib => (chaltsc lib t # a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom))
    <=> equality lib a b (mkc_halts t).
Proof.
  introv.
  rewrite <- fold_mkc_halts.
  rw <- @equality_in_approx.
  unfold all_in_ex_bar.
  split; intro k; exrepnd; exists bar;
    introv br ext; apply k0 in ext; auto; clear k0; repnd; dands; auto;
      apply chasvaluec_as_capproxc; auto.
Qed.

Lemma type_mkc_unit {p} : forall lib, @type p lib mkc_unit.
Proof.
  introv; rw @mkc_unit_eq.
  apply equal_approx.
Qed.
Hint Immediate type_mkc_unit.
Hint Resolve type_mkc_unit : slow.

Lemma tequality_unit {o} :
  forall lib, @tequality o lib mkc_unit mkc_unit.
Proof.
  introv; allrw @mkc_unit_eq.
  rw @tequality_mkc_approx; eauto 3 with slow refl.
Qed.
Hint Resolve tequality_unit : slow.

Lemma equality_in_unit {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_unit
    <=> all_in_ex_bar lib (fun lib => (a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom)).
Proof.
  introv.
  allrw @mkc_unit_eq.
  rw <- @equality_in_approx.
  unfold all_in_ex_bar.
  split; introv h; exrepnd; exists bar; introv br ext;
    apply h0 in ext; clear h0; auto; repnd; dands; auto; spcast; eauto 3 with slow refl.
Qed.

Lemma resp_cvc_approxc {p} :
  forall lib, respects2 (computes_to_valc lib) (@approxc p lib).
Proof.
  split; introv Hc Ha;
  apply computes_to_valc_implies_approxc in Hc; repnd;
  destruct_cterms; allunfold @approxc;
  eauto with slow.
Qed.
Hint Resolve resp_cvc_approxc : respects.

Lemma equality_in_uni_mkc_halts {p} :
  forall lib i (a b : @CTerm p),
    equality lib (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => (chaltsc lib a <=> chaltsc lib b)).
Proof.
  intros; repeat (rewrite <- fold_mkc_halts).
  rw @mkc_approx_equality_in_uni.
  unfold all_in_ex_bar; split; intro h; exrepnd; exists bar;
    introv br ext; apply h0 in ext; auto; clear h0;
      allrw @chasvaluec_as_capproxc; sp.
Qed.

Lemma cequorsq_mkc_halts_implies {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_halts a) (mkc_halts b) (mkc_uni i)
    -> all_in_ex_bar lib (fun lib => (chaltsc lib a <=> chaltsc lib b)).
Proof.
  unfold equorsq; introv h; repndors; allrw @equality_in_uni_mkc_halts; tcsp.
  exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar; introv ext; apply h in ext.
  uncast; allrw @cequivc_decomp_halts; sp; split; sp; spcast; discover; sp.
Qed.

Lemma cequorsq_mkc_halts {p} :
  forall lib i (a b : @CTerm p),
    equorsq lib (mkc_halts a) (mkc_halts b) (mkc_uni i)
    <=>
    (chaltsc lib a <=> chaltsc lib b).
Proof.
  unfold equorsq; intros; split; sp; try right;
  allrw @equality_in_uni_mkc_halts; sp; uncast;
  allrw @cequivc_decomp_halts; try split; sp; spcast;
  discover; sp.
Abort.
(* This is not true in Prop with Cast around hasvalue *)
(*Qed.*)

Lemma member_in_base_iff {o} :
  forall lib (t : @CTerm o), member lib t mkc_base <=> True.
Proof.
  intros; split; intro; auto; apply member_base.
Qed.
