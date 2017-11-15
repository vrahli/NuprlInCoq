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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


(* MOVE *)
Lemma mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies {o} :
  forall {lib} (bar : @BarLib o lib) a b c d,
    (mkc_cequiv a b) ==b==>(bar) (mkc_cequiv c d)
    -> all_in_bar bar (fun lib => a ~=~(lib) c # b ~=~(lib) d).
Proof.
  introv comp br ext.
  pose proof (comp lib' br lib'0 ext) as comp; simpl in *; exrepnd; spcast.
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
Qed.

(* MOVE *)
Lemma ccequivc_trans {o} :
  forall lib (a b c : @CTerm o),
    (a) ~=~(lib) (b)
    -> (b) ~=~(lib) (c)
    -> (a) ~=~(lib) (c).
Proof.
  introv h q; spcast; eapply cequivc_trans; eauto.
Qed.

(* MOVE *)
Lemma capproxc_trans {o} :
  forall lib (a b c : @CTerm o),
    (a) ~<~(lib) (b)
    -> (b) ~<~(lib) (c)
    -> (a) ~<~(lib) (c).
Proof.
  introv h q; spcast; eapply approxc_trans; eauto.
Qed.

(* MOVE *)
Lemma ccequivc_implies_capproxc {o} :
  forall lib (a b : @CTerm o),
    (a) ~=~(lib) (b)
    -> (a) ~<~(lib) (b).
Proof.
  introv h; spcast; destruct h; auto.
Qed.

(* MOVE *)
Lemma ccequivc_sym {o} :
  forall lib (a b : @CTerm o),
    (a) ~=~(lib) (b)
    -> (b) ~=~(lib) (a).
Proof.
  introv  q; spcast; eapply cequivc_sym; eauto.
Qed.

(* MOVE *)
Lemma implies_all_in_bar_iff_ccequivc {o} :
  forall lib (bar : @BarLib o lib) a b c d a' b' c' d',
    all_in_bar bar (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> all_in_bar bar (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a') ~=~(lib) (b') <=> (c') ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a) ~=~(lib) (b) <=> (c) ~=~(lib) (d)).
Proof.
  introv alla allb allc br ext.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  pose proof (allc lib' br lib'0 ext) as allc.
  simpl in *.
  repnd.
  split; introv q.

  { eapply ccequivc_trans;[eauto|].
    eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
    apply allc.
    eapply ccequivc_trans;[apply ccequivc_sym;eauto|].
    eapply ccequivc_trans;[|eauto]; auto. }

  { eapply ccequivc_trans;[eauto|].
    eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
    apply allc.
    eapply ccequivc_trans;[apply ccequivc_sym;eauto|].
    eapply ccequivc_trans;[|eauto]; auto. }
Qed.

(* MOVE *)
Lemma implies_all_in_bar_iff_capproxc {o} :
  forall lib (bar : @BarLib o lib) a b c d a' b' c' d',
    all_in_bar bar (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> all_in_bar bar (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a') ~<~(lib) (b') <=> (c') ~<~(lib) (d'))
    -> all_in_bar bar (fun lib => (a) ~<~(lib) (b) <=> (c) ~<~(lib) (d)).
Proof.
  introv alla allb allc br ext.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  pose proof (allc lib' br lib'0 ext) as allc.
  simpl in *.
  repnd.
  split; introv q.

  { eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
    apply allc.
    eapply capproxc_trans;[apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;eauto]; auto. }

  { eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
    apply allc.
    eapply capproxc_trans;[apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;eauto]; auto. }
Qed.

(* MOVE *)
Lemma computes_to_valc_ceq_bar_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    iscvalue v
    -> v ==b==>(bar) v.
Proof.
  introv isv br ext.
  exists v; dands; spcast; eauto 3 with slow.
  apply computes_to_valc_refl; auto.
Qed.
Hint Resolve computes_to_valc_ceq_bar_refl : refl.

(* MOVE *)
Definition all_in_ex_bar {o} (lib : @library o) F :=
  {bar : BarLib lib , all_in_bar bar F}.

Lemma mkc_cequiv_equality_in_uni {p} :
  forall lib (a b c d : @CTerm p) i,
    equality lib (mkc_cequiv a b) (mkc_cequiv c d) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    allunfold @nuprl.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

    not_univ_p1.
    exists bar.
    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in c1.
    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in c2.
    eapply implies_all_in_bar_iff_ccequivc; eauto.

  - Case "<-".
    unfold all_in_ex_bar in *; exrepnd.
    exists (fun A A' => {eqa : per(p) , close (univi i) lib A A' eqa}); sp.

    {
      apply CL_init.
      exists (S i); simpl; left; sp;
        spcast; try computes_to_value_refl.
    }

    exists (per_cequiv_eq_bar lib a b).
    apply CL_cequiv.
    exists a b c d; dands; auto.
    exists bar; dands; spcast; eauto 3 with slow refl.
Qed.

Lemma mkc_approx_equality_in_uni {p} :
  forall lib (a b c d : @CTerm p) i,
    equality lib (mkc_approx a b) (mkc_approx c d) (mkc_uni i)
    <=>
    all_in_ex_bar lib (fun lib => (capproxc lib a b <=> capproxc lib c d)).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

    not_univ_p1.
    exists bar.
    apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in c1.
    apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in c2.
    eapply implies_all_in_bar_iff_capproxc; eauto.

  - Case "<-".
    unfold all_in_ex_bar in *; exrepnd.
    exists (fun A A' => {eqa : per(p) , close (univi i) lib A A' eqa}); sp.

    {
      apply CL_init.
      exists (S i); simpl; left; sp;
        spcast; try computes_to_value_refl.
    }

    exists (per_approx_eq_bar lib a b).
    apply CL_approx.
    exists a b c d; dands; auto.
    exists bar; dands; spcast; eauto 3 with slow refl.
Qed.

(* MOVE *)
Hint Resolve approxc_refl : refl.

(* MOVE *)
Lemma all_in_bar_iff_capproxc_same {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~<~(lib) (a) <=> (b) ~<~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_capproxc_same : slow.

(* MOVE *)
Lemma all_in_bar_iff_capproxc_same2 {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~<~(lib) (b) <=> (a) ~<~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_capproxc_same2 : slow.

(* MOVE *)
Lemma all_in_bar_iff_ccequivc_same {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~=~(lib) (a) <=> (b) ~=~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_ccequivc_same : slow.

(* MOVE *)
Lemma all_in_bar_iff_ccequivc_same2 {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~=~(lib) (b) <=> (a) ~=~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_ccequivc_same2 : slow.

Lemma member_approx_refl {p} :
  forall lib t, @member p lib mkc_axiom (mkc_approx t t).
Proof.
  intros.
  exists (per_approx_eq_bar lib t t).
  dands; auto.

  {
    apply CL_approx.
    exists t t t t; dands; auto.
    exists (trivial_bar lib); dands; eauto 3 with slow refl.
  }

  {
    exists (trivial_bar lib); introv br ext; dands; spcast;
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
    exists t t t t; dands; auto.
    exists (trivial_bar lib); dands; eauto 3 with slow refl.
  }

  {
    exists (trivial_bar lib); introv br ext; dands; spcast;
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
  exists t t u u; dands; auto.
  exists (trivial_bar lib); dands; eauto 3 with slow refl.
Qed.

Lemma equal_cequiv {p} :
  forall lib t u,
    @tequality p lib (mkc_cequiv t t) (mkc_cequiv u u).
Proof.
  intros.
  exists (per_cequiv_eq_bar lib t t).
  apply CL_cequiv.
  exists t t u u; dands; auto.
  exists (trivial_bar lib); dands; eauto 3 with slow refl.
Qed.

(* MOVE *)
Lemma all_in_bar_ccomputes_to_valc_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    iscvalue v
    -> all_in_bar bar (fun lib => v ===>(lib) v).
Proof.
  introv isv br ext; spcast.
  apply computes_to_valc_refl; auto.
Qed.
Hint Resolve all_in_bar_ccomputes_to_valc_refl : refl.

(* MOVE *)
Lemma all_in_bar_ccequivc_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    all_in_bar bar (fun lib => v ~=~(lib) v).
Proof.
  introv br ext; spcast; auto.
Qed.
Hint Resolve all_in_bar_ccequivc_refl : refl.

Lemma member_base {p} :
  forall lib t, @member p lib t mkc_base.
Proof.
  introv.
  exists (per_base_eq lib); dands; auto.
  {
    apply CL_base.
    unfold per_base_bar; dands; auto.
    exists (trivial_bar lib); dands; eauto 3 with slow refl.
  }
  exists (trivial_bar lib).
  unfold per_base_eq1; eauto 3 with slow refl.
Qed.

(* MOVE *)
Lemma implies_all_in_bar_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F
    -> all_in_bar (trivial_bar lib) F.
Proof.
  introv i br ext; simpl in *.
  eapply i; eauto 3 with slow.
Qed.

(* MOVE *)
Hint Resolve computes_to_valc_refl : refl.

Lemma member_cequiv {o} :
  forall lib (t1 t2 : @CTerm o),
    ccequivc_ext lib t1 t2
    -> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  introv ceq.
  exists (per_cequiv_eq_bar lib t1 t2); dands; auto.
  {
    apply CL_cequiv.
    exists t1 t2 t1 t2; dands; auto;[].
    exists (trivial_bar lib); dands; spcast; eauto 3 with slow refl.
  }
  exists (trivial_bar lib).
  unfold per_cequiv_eq_bar1.
  apply implies_all_in_bar_trivial_bar.
  introv x.
  applydup ceq in x.
  dands; spcast; eauto 3 with slow refl.
Qed.

Lemma member_cequiv_bar {o} :
  forall lib (t1 t2 : @CTerm o),
    all_in_ex_bar lib (fun lib => ccequivc lib t1 t2)
    -> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  introv ceq.
  exists (per_cequiv_eq_bar lib t1 t2); dands; auto.
  {
    apply CL_cequiv.
    exists t1 t2 t1 t2; dands; auto;[].
    exists (trivial_bar lib); dands; spcast; eauto 3 with slow refl.
  }
  unfold all_in_ex_bar in *; exrepnd.
  exists bar.
  unfold per_cequiv_eq_bar1.
  introv br x.
  apply ceq0 in x; auto.
  dands; spcast; eauto 3 with slow refl.
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
    exists t1 t2 t1 t2; dands; auto;[].
    exists (trivial_bar lib); dands; spcast; eauto 3 with slow refl.
  }
  exists (trivial_bar lib).
  unfold per_approx_eq_bar1.
  apply implies_all_in_bar_trivial_bar.
  introv x.
  applydup apr in x.
  dands; spcast; eauto 3 with slow refl.
Qed.

Lemma member_approx_bar {o} :
  forall lib (bar : BarLib lib) (t1 t2 : @CTerm o),
    all_in_bar bar (fun lib => capproxc lib t1 t2)
    -> member lib mkc_axiom (mkc_approx t1 t2).
Proof.
  introv apr.
  exists (per_approx_eq_bar lib t1 t2); dands; auto.
  {
    apply CL_approx.
    exists t1 t2 t1 t2; dands; auto;[].
    exists (trivial_bar lib); dands; spcast; eauto 3 with slow refl.
  }
  exists bar.
  unfold per_approx_eq_bar1.
  introv br ext.
  pose proof (apr lib' br lib'0 ext) as apr; simpl in *.
  dands; spcast; eauto 3 with slow refl.
Qed.

Lemma member_approx_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    all_in_ex_bar lib (fun lib => capproxc lib t1 t2)
    <=> member lib mkc_axiom (mkc_approx t1 t2).
Proof.
  introv; split; intro e;
    try (complete (unfold all_in_ex_bar in *; exrepnd; eapply member_approx_bar; eauto)).

  unfold member, equality, nuprl in *; exrepnd.
  inversion e1; subst; try not_univ;[].

  rename_hyp_with @per_approx_bar h.
  unfold per_approx_bar in *; exrepnd.

  apply mkc_approx_computes_to_valc_ceq_bar_implies in h0.
  apply mkc_approx_computes_to_valc_ceq_bar_implies in h3.
  apply h1 in e0.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in e0; exrepnd.

  exists (intersect_bars bar bar0).
  introv br ext; simpl in *; exrepnd.

  pose proof (e2 lib2 br2 lib'0 (lib_extends_trans ext br1)) as e2; simpl in *; repnd.
  pose proof (h0 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h0; simpl in *; repnd.
  pose proof (h3 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h3; simpl in *; repnd.
  pose proof (h2 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h2; simpl in *; repnd.

  eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
  eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
  apply h2; auto.
Qed.

Lemma member_halts_iff {p} :
  forall lib (t : @CTerm p),
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

Lemma equality_in_base {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_base
    -> per_base_eq lib t1 t2.
Proof.
  unfold equality, nuprl; introv e; exrepnd.
  inversion e1; subst; try not_univ;[].

  rename_hyp_with @per_base_bar h.
  unfold per_base_bar in *; exrepnd; GC.
  apply h in e0; auto.
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
  unfold per_base_bar; dands; auto.
  exists (trivial_bar lib); dands; eauto 3 with slow refl.
Qed.

Lemma tequality_base {p} :
  forall lib, @tequality p lib mkc_base mkc_base.
Proof.
  introv.
  exists (per_base_eq lib).
  apply CL_base.
  unfold per_base_bar; dands; auto.
  exists (trivial_bar lib); dands; eauto 3 with slow refl.
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
    inversion k0; subst; try not_univ;[].
    rename_hyp_with @per_approx_bar h.
    unfold per_approx_bar in *; exrepnd.
    exists bar; auto.
    apply mkc_approx_computes_to_valc_ceq_bar_implies in h0.
    apply mkc_approx_computes_to_valc_ceq_bar_implies in h3.
    eapply implies_all_in_bar_iff_capproxc; eauto.
  }

  {
    unfold all_in_ex_bar in *; exrepnd.
    exists (per_approx_eq_bar lib a b); dands; auto.
    apply CL_approx.
    unfold per_approx_bar.
    exists a b c d; dands; auto.
    exists bar.
    dands; spcast; eauto 3 with slow refl.
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

Lemma member_approx_is_axiom {p} :
  forall lib (t t1 t2 : @CTerm p),
    member lib t (mkc_approx t1 t2)
    -> all_in_ex_bar lib (fun lib => t ===>(lib) mkc_axiom).
Proof.
  introv m.
  unfold member, equality, nuprl in m; exrepnd.
  inversion m1; subst; try not_univ.
  rename_hyp_with @per_approx_bar h.
  allunfold @per_approx_bar; exrepnd.
  apply h1 in m0; clear h1.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.
  exists bar0; introv br ext.
  pose proof (m2 lib' br lib'0 ext) as m2; simpl in *; tcsp.
Qed.

Lemma member_cequiv_iff {p} :
  forall lib (t1 t2 : @CTerm p),
    all_in_ex_bar lib (fun lib => ccequivc lib t1 t2)
    <=> member lib mkc_axiom (mkc_cequiv t1 t2).
Proof.
  sp; split; intro e.

  { spcast; apply member_cequiv_bar; sp. }

  allunfold @member; allunfold @equality; allunfold @nuprl; exrepnd.
  inversion e1; subst; try not_univ.

  rename_hyp_with @per_cequiv_bar h.
  allunfold @per_cequiv_bar; exrepnd.
  apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h0.
  apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h3.
  apply h1 in e0.
  unfold per_cequiv_eq_bar, per_cequiv_eq_bar1 in e0; exrepnd.

  exists (intersect_bars bar bar0).
  introv br ext; simpl in *; exrepnd.

  pose proof (e2 lib2 br2 lib'0 (lib_extends_trans ext br1)) as e2; simpl in *; repnd.
  pose proof (h0 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h0; simpl in *; repnd.
  pose proof (h3 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h3; simpl in *; repnd.
  pose proof (h2 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h2; simpl in *; repnd.

  eapply ccequivc_trans;[eauto|].
  eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
  apply h2; auto.
Qed.

Lemma tequality_mkc_cequiv {p} :
  forall lib (a b c d : @CTerm p),
    tequality lib (mkc_cequiv a b) (mkc_cequiv c d)
    <=>
    all_in_ex_bar lib (fun lib => (ccequivc lib a b <=> ccequivc lib c d)).
Proof.
  unfold tequality, nuprl; sp; split; intro k; exrepnd.

  {
    inversion k0; subst; try not_univ; clear k0;[].
    rename_hyp_with @per_cequiv_bar h.
    unfold per_cequiv_bar in *; exrepnd.
    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h0.
    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h3.
    exists bar.
    eapply implies_all_in_bar_iff_ccequivc; eauto.
  }

  {
    unfold all_in_ex_bar in *; exrepnd.
    exists (per_cequiv_eq_bar lib a b); dands; auto.
    apply CL_cequiv.
    exists a b c d; dands; auto.
    exists bar; dands; spcast; eauto 3 with slow refl.
  }
Qed.

Lemma equality_in_approx {p} :
  forall lib (a b t1 t2 : @CTerm p),
    all_in_ex_bar lib (fun lib => (capproxc lib t1 t2 # a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom))
    <=> equality lib a b (mkc_approx t1 t2).
Proof.
  sp; split; intro e.

  - unfold all_in_ex_bar in *; exrepnd.
    unfold member, equality.
    exists (per_approx_eq_bar lib t1 t2); dands; auto.

    {
      apply CL_approx.
      exists t1 t2 t1 t2; dands; auto.
      exists bar; dands; eauto 3 with slow refl.
    }

    {
      exists bar.
      introv br ext.
      apply e0 in ext; tcsp.
    }

  - unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; clear e1; try not_univ;[].
    rename_hyp_with @per_approx_bar h.
    allunfold @per_approx_bar; exrepnd.
    apply h1 in e0; clear h1.
    unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.

    apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in h0.
    apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in h3.

    exists (intersect_bars bar bar0).
    introv br ext; simpl in *; exrepnd.

    pose proof (e1 lib2 br2 lib'0 (lib_extends_trans ext br1)) as e1; simpl in *; repnd.
    pose proof (h0 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h0; simpl in *; repnd.
    pose proof (h3 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h3; simpl in *; repnd.
    pose proof (h2 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h2; simpl in *; repnd.

    dands; auto;[].

    eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
    apply h2; auto.
Qed.

Lemma equality_in_mkc_cequiv {o} :
  forall lib a b (t1 t2 : @CTerm o),
    equality lib a b (mkc_cequiv t1 t2)
    <=> all_in_ex_bar lib (fun lib => (a ===>(lib) mkc_axiom
                                       # b ===>(lib) mkc_axiom
                                       # ccequivc lib t1 t2)).
Proof.
  sp; split; intro e.

  - unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; clear e1; try not_univ;[].
    rename_hyp_with @per_cequiv_bar h.
    allunfold @per_cequiv_bar; exrepnd.
    apply h1 in e0; clear h1.
    unfold per_cequiv_eq_bar, per_cequiv_eq_bar1 in *; exrepnd.

    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h0.
    apply mkc_cequiv_computes_to_valc_ceq_bar_mkc_cequiv_implies in h3.

    exists (intersect_bars bar bar0).
    introv br ext; simpl in *; exrepnd.

    pose proof (e1 lib2 br2 lib'0 (lib_extends_trans ext br1)) as e1; simpl in *; repnd.
    pose proof (h0 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h0; simpl in *; repnd.
    pose proof (h3 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h3; simpl in *; repnd.
    pose proof (h2 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h2; simpl in *; repnd.

    dands; auto;[].

    eapply ccequivc_trans;[eauto|].
    eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
    apply h2; auto.

  - unfold all_in_ex_bar in *; exrepnd.
    unfold member, equality.
    exists (per_cequiv_eq_bar lib t1 t2); dands; auto.

    {
      apply CL_cequiv.
      exists t1 t2 t1 t2; dands; auto.
      exists bar; dands; eauto 3 with slow refl.
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

Lemma inhabited_halts {p} :
  forall lib (t : @CTerm p),
    all_in_ex_bar lib (fun lib => chaltsc lib t)
    <=> inhabited_type lib (mkc_halts t).
Proof.
  introv; split; intro h.

  { rw @member_halts_iff in h; exists (@mkc_axiom p); auto. }

  unfold inhabited_type in h; exrepnd.
  unfold member, equality in h0; exrepnd.
  rewrite <- fold_mkc_halts in h0.
  inversion h0; subst; try not_univ; clear h0;[].
  rename_hyp_with @per_approx_bar h.
  unfold per_approx_bar in *; exrepnd.
  apply h2 in h1; clear h2.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.

  apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in h0.
  apply mkc_approx_computes_to_valc_ceq_bar_mkc_approx_implies in h4.

  exists (intersect_bars bar bar0).
  introv br ext; simpl in *; exrepnd.

  pose proof (h2 lib2 br2 lib'0 (lib_extends_trans ext br1)) as h2; simpl in *; repnd.
  pose proof (h0 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h0; simpl in *; repnd.
  pose proof (h4 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h4; simpl in *; repnd.
  pose proof (h3 lib1 br0 lib'0 (lib_extends_trans ext br3)) as h3; simpl in *; repnd.

  apply chasvaluec_as_capproxc.

  eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
  eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
  apply h3; auto.
Qed.

Lemma all_in_ex_bar_iff_same {o} :
  forall (lib : @library o) (F : library -> Prop),
    all_in_ex_bar lib (fun lib => F lib <=> F lib).
Proof.
  introv; exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar.
  introv ext; tcsp.
Qed.
Hint Resolve all_in_ex_bar_iff_same : refl.

Lemma type_mkc_halts {p} :
  forall lib (a : @CTerm p), type lib (mkc_halts a).
Proof.
  introv; rw @tequality_mkc_halts; eauto 3 with slow refl.
Qed.
Hint Immediate type_mkc_halts.

Lemma equality_in_halts {p} :
  forall lib (a b t : @CTerm p),
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
