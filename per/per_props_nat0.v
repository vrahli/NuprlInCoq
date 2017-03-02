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


Require Export prog.
Require Export cvterm.
Require Export csubst6.

Require Export types_converge.

Require Export per_props_compute.
Require Export per_props_set.
Require Export per_props_not.


(*
Lemma nuprl_mkc_not {o} :
  forall lib (a b : @CTerm o) eq,
    nuprl lib a b eq
    -> nuprl lib (mkc_not a) (mkc_not b) (fun t t' => forall a a', eq a a' -> False).
Proof.
  introv n.
  apply CL_func.
  unfold per_func.
  exists eq (fun (a a' : CTerm) (e : eq a a') (t t' : @CTerm o) => False); dands.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    unfold mkc_not.
    rw <- @fold_mkc_fun.
    apply computes_to_valc_refl.
    apply iscvalue_mkc_function.

    unfold mkc_not.
    rw <- @fold_mkc_fun.
    apply computes_to_valc_refl.
    apply iscvalue_mkc_function.

    auto.

    introv e.
    allrw @csubst_mk_cv.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; auto; spcast;
    try (rw @mkc_void_eq_mkc_false; rw @mkc_false_eq);
    try (apply @computes_to_valc_refl; apply @iscvalue_mkc_approx).
    introv; split; intro k; repnd; sp; spcast.
    apply not_axiom_approxc_bot in k; sp.

  - sp.
Qed.
*)

(*
Lemma nuprl_mkc_true {o} :
  forall lib, @nuprl o lib
                     mkc_true
                     mkc_true
                     (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom).
Proof.
  introv.
  apply CL_approx.
  rw @mkc_true_eq.
  unfold per_approx.
  eexists; eexists; eexists; eexists; dands; spcast.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  sp.
  introv; split; sp; spcast.
  apply approxc_refl.
Qed.
*)

Lemma tequality_int {p} : forall lib, @tequality p lib mkc_int mkc_int.
Proof.
  introv.
  exists (@equality_of_int p lib).
  split; apply CL_int; unfold per_int; dands; tcsp;
    spcast; apply computes_to_valc_refl; eauto 2 with slow.
Qed.
Hint Resolve tequality_int : slow.

Lemma type_int {p} : forall lib, @type p lib mkc_int.
Proof.
  introv.
  apply fold_type; eauto 2 with slow.
Qed.
Hint Resolve type_int : slow.

Lemma equality_in_int {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_int <=> equality_of_int lib t1 t2.
Proof.
  intros; split; intro e.

  - unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_int; sp.
    match goal with
    | [ H : _ <=2=> _ |- _ ] => apply H in e0
    end; auto.

  - unfold equality, nuprl.
    exists (equality_of_int lib); dands; tcsp.
    apply CL_int; unfold per_int; sp;
      spcast; apply computes_to_valc_refl; eauto 2 with slow.
Qed.

Hint Rewrite @substc_mkcv_le   : slow.
Hint Rewrite @substc_mkcv_zero : slow.

Lemma tequality_mkc_less_aux {o} :
  forall lib (a b c d e f g h : @CTerm o) ka kb ke kf,
    computes_to_valc lib a (mkc_integer ka)
    -> computes_to_valc lib b (mkc_integer kb)
    -> computes_to_valc lib e (mkc_integer ke)
    -> computes_to_valc lib f (mkc_integer kf)
    -> (tequality lib (mkc_less a b c d) (mkc_less e f g h)
        <=>
        (
          ((ka < kb)%Z # (ke < kf)%Z # tequality lib c g)
          [+]
          ((kb <= ka)%Z # (kf <= ke)%Z # tequality lib d h)
          [+]
          ((ka < kb)%Z # (kf <= ke)%Z # tequality lib c h)
          [+]
          ((kb <= ka)%Z # (ke < kf)%Z # tequality lib d g)
        )
       ).
Proof.
  introv ca cb ce cf.

  assert (cequivc lib
                  (mkc_less a b c d)
                  (mkc_less (mkc_integer ka) (mkc_integer kb) c d)) as c1.
  { apply reduces_toc_implies_cequivc.
    destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
    apply reduce_to_prinargs_comp; eauto with slow. }

  assert (cequivc lib
                  (mkc_less e f g h)
                  (mkc_less (mkc_integer ke) (mkc_integer kf) g h)) as c2.
  { apply reduces_toc_implies_cequivc.
    destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
    apply reduce_to_prinargs_comp; eauto with slow. }

  split; intro k; repnd.

  - destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; right; left; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; right; right; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; left; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

  - rwg c1.
    rwg c2.
    clear c1 c2 ca cb ce cf.
    repndors; exrepnd.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.
Qed.

Lemma hasvaluec_mkc_less {o} :
  forall lib (a b c d : @CTerm o),
    hasvaluec lib (mkc_less a b c d)
    -> {k1 : Z
        & {k2 : Z
        & reduces_toc lib a (mkc_integer k1)
        # reduces_toc lib b (mkc_integer k2)
        # (((k1 < k2)%Z # hasvaluec lib c)
           [+]
           ((k2 <= k1)%Z # hasvaluec lib d)
          )}}.
Proof.
  introv hv.
  destruct_cterms; allsimpl.
  allunfold @hasvaluec; allsimpl.
  allunfold @reduces_toc; allsimpl.
  apply hasvalue_mk_less in hv; eauto 3 with slow.
Qed.

Lemma computes_to_valc_implies_reduces_toc {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    -> reduces_toc lib t1 t2.
Proof.
  introv comp.
  allrw @computes_to_valc_iff_reduces_toc; sp.
Qed.
Hint Resolve computes_to_valc_implies_reduces_toc : slow.

Lemma tequality_mkc_less {o} :
  forall lib (a b c d e f g h : @CTerm o),
    tequality lib (mkc_less a b c d) (mkc_less e f g h)
    <=>
    {ka : Z
     , {kb : Z
     , {ke : Z
     , {kf : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # e ===>(lib) (mkc_integer ke)
        # f ===>(lib) (mkc_integer kf)
        # (
            ((ka < kb)%Z # (ke < kf)%Z # tequality lib c g)
            {+}
            ((kb <= ka)%Z # (kf <= ke)%Z # tequality lib d h)
            {+}
            ((ka < kb)%Z # (kf <= ke)%Z # tequality lib c h)
            {+}
            ((kb <= ka)%Z # (ke < kf)%Z # tequality lib d g)
          )}}}}.
Proof.
  introv.

  split; intro k; exrepnd.

  - applydup @tequality_refl in k.
    applydup @tequality_sym in k.
    apply tequality_refl in k1.
    allrw @fold_type.
    apply types_converge in k0.
    apply types_converge in k1.
    spcast.

    apply hasvaluec_mkc_less in k0.
    apply hasvaluec_mkc_less in k1.
    exrepnd.

    exists k2 k0 k6 k1; dands; spcast; eauto with slow;
      try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).

    pose proof (tequality_mkc_less_aux
                  lib a b c d e f g h k2 k0 k6 k1) as p.
    repeat (autodimp p hyp);
      try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).
    apply p in k; sp.

  - pose proof (tequality_mkc_less_aux
                  lib a b c d e f g h ka kb ke kf) as p.
    spcast.
    repeat (autodimp p hyp).
    apply p.

    destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.
      repndors; repnd; try omega; auto.

    + right; right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; right; right; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.
Qed.

Lemma equality_in_true {o} :
  forall lib (u v : @CTerm o), equality lib u v mkc_true.
Proof.
  introv.
  rw @mkc_true_eq.
  apply equality_in_approx; spcast; eauto 2 with slow.
Qed.
Hint Resolve equality_in_true : slow.

Lemma tequality_mkc_true {o} :
  forall (lib : @library o), tequality lib mkc_true mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply tequality_mkc_approx; sp.
Qed.
Hint Resolve tequality_mkc_true : slow.

Lemma type_mkc_true {o} :
  forall (lib : @library o), type lib mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply fold_type.
  apply tequality_mkc_approx; sp.
Qed.
Hint Resolve type_mkc_true : slow.

Lemma true_not_equal_to_false {o} :
  forall (lib : @library o),
    !tequality lib mkc_true mkc_false.
Proof.
  introv teq.
  unfold tequality, nuprl in teq; exrepnd.
  destruct teq0 as [teq1 teq2].
  rw @mkc_true_eq in teq1.
  inversion teq1; subst; try not_univ; clear teq1.
  rw @mkc_false_eq in teq2.
  inversion teq2; subst; try not_univ; clear teq2.

  match goal with
  | [ H1 : per_approx _ _ _ _ , H2 : per_approx _ _ _ _ |- _ ] =>
    rename H1 into h; rename H2 into q
  end.

  unfold per_approx in *; exrepnd.
  computes_to_value_isvalue; GC.
  eapply eq_term_equals_trans in q1;[|apply eq_term_equals_sym;exact h1].
  pose proof (q1 (@mkc_axiom o) (@mkc_axiom o)) as w; simpl in w; auto.
  destruct w as [w w']; clear w'.
  autodimp w hyp; spcast; eauto 2 with slow.
  apply not_axiom_approxc_bot in w; sp.
Qed.

Lemma tequality_mkc_less_than {o} :
  forall lib (a b c d : @CTerm o),
    tequality lib (mkc_less_than a b) (mkc_less_than c d)
    <=>
    {ka : Z
     , {kb : Z
     , {kc : Z
     , {kd : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # c ===>(lib) (mkc_integer kc)
        # d ===>(lib) (mkc_integer kd)
        # (
            ((ka < kb)%Z # (kc < kd)%Z)
            {+}
            ((kb <= ka)%Z # (kd <= kc)%Z)
          )}}}}.
Proof.
  introv.
  allrw @mkc_less_than_eq.
  rw (tequality_mkc_less
        lib a b mkc_true mkc_false c d mkc_true mkc_false).

  split; intro k; exrepnd.

  - exists ka kb ke kf; dands; auto.
    repndors; repnd; tcsp.

    + apply true_not_equal_to_false in k1; sp.

    + apply tequality_sym in k1.
      apply true_not_equal_to_false in k1; sp.

  - exists ka kb kc kd; dands; auto.
    repndors; repnd; tcsp.

    left; sp; eauto 2 with slow.
Qed.

Lemma tequality_mkc_le {o} :
  forall lib (a b c d : @CTerm o),
    tequality lib (mkc_le a b) (mkc_le c d)
    <=>
    {ka : Z
     , {kb : Z
     , {kc : Z
     , {kd : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # c ===>(lib) (mkc_integer kc)
        # d ===>(lib) (mkc_integer kd)
        # (
            ((ka <= kb)%Z # (kc <= kd)%Z)
            {+}
            ((kb < ka)%Z # (kd < kc)%Z)
          )}}}}.
Proof.
  introv.
  allrw @mkc_le_eq.
  rw @tequality_not.
  rw @tequality_mkc_less_than.

  split; intro k; exrepnd.

  - exists kb ka kd kc; dands; auto.
    repndors; repnd; tcsp.

  - exists kb ka kd kc; dands; auto.
    repndors; repnd; tcsp.
Qed.

Lemma tnat_type {o} : forall lib, @type o lib mkc_tnat.
Proof.
  introv.
  rw @mkc_tnat_eq.
  rw @type_set.
  dands; eauto 2 with slow.
  introv ea.
  apply equality_in_int in ea.
  unfold equality_of_int in ea; exrepnd; spcast.
  autorewrite with slow in *.

  SearchAbout tequality mkc_le.

  SearchAbout type mkc_int.

XXXXXXXXXXX
  SearchAbout mkc_tnat.
  unfold type, tequality.
  pose proof @nuprl_tnat as h.
  exists
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 0)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}); sp.
Qed.

Lemma nuprl_tnat {o} :
  forall lib,
  @nuprl o
    lib
    mkc_tnat
    mkc_tnat
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 0)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}).
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply CL_set; fold (@nuprl o).
  unfold per_set.
  exists (@equality_of_int o lib).
  exists
    (fun (a a' : @CTerm o)
         (e : equality_of_int lib a a')
         (t t' : @CTerm o) =>
       forall (u v : @CTerm o),
         (forall k,
            computes_to_valc lib a (mkc_integer k)
            -> if (k <? 0)%Z
               then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
               else False)
         -> False);
    dands; auto.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply nuprl_int.

    + introv e.
      allrw @mkcv_le_substc.
      allrw @mkcv_zero_substc.
      allrw @mkc_var_substc.
      allrw @mkc_le_eq.
      unfold equality_of_int in e; exrepnd; spcast.

      apply CL_func.
      unfold per_func.
      exists (fun t t' : @CTerm o =>
                if (k <? 0)%Z
                then t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom
                else False).
      exists (fun (a a' : @CTerm o) (e : if (k <? 0)%Z
                            then a ===>(lib) mkc_axiom # a' ===>(lib) mkc_axiom
                            else False) (t t' : @CTerm o) => False).
      dands; auto.

      * unfold type_family.
        eexists; eexists; eexists; eexists; eexists; eexists;
        dands; auto; spcast; try (fold nuprl).

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        remember ((k <? 0)%Z); symmetry in Heqb; destruct b.

        apply Z.ltb_lt in Heqb.

        pose proof (mkc_less_than_comp1 lib a mkc_zero k 0) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp1 lib a' mkc_zero k 0) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_value_respecting_left with (t1 := mkc_true).
        apply nuprl_value_respecting_right with (t2 := mkc_true).
        apply nuprl_mkc_true.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.

        apply Z.ltb_ge in Heqb.

        pose proof (mkc_less_than_comp2 lib a mkc_zero k 0) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp2 lib a' mkc_zero k 0) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_computes_left with (t1 := mkc_false); auto.
        apply nuprl_computes_right with (t2 := mkc_false); auto.
        rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        introv; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

        introv e; simphyps.
        allrw @csubst_mk_cv.
        rw @mkc_void_eq_mkc_false; rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        sp; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

      * intros; split; intro j; introv m.

        apply j with (u := a0) (v := a'0); auto.
        introv c.
        pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e;
          repeat (autodimp e hyp).
        inversion e; subst; GC; sp.

        pose proof (m k) as l; autodimp l hyp.
        apply j in l; sp.

  - introv.
    split; intro k; exrepnd.
    exists v; sp.
    exists e; sp.
Qed.

(*

  We could also have defined this type using 0 < y.
  I used 1 <= y because the proofs will be similar to the ones for tnat.

 *)
Definition mk_tnatp {o} := @mk_set o mk_int nvary (mk_le mk_one (mk_var nvary)).

Lemma isprog_tnatp {o} : @isprog o mk_tnatp.
Proof.
  rw <- @isprog_set_iff.
  dands; eauto 3 with slow.
Qed.

Definition mkc_tnatp {o} : @CTerm o := exist isprog mk_tnatp isprog_tnatp.

Lemma mkc_tnatp_eq {o} :
  @mkc_tnatp o = mkc_set mkc_int nvary (mkcv_le [nvary] (mkcv_one [nvary]) (mkc_var nvary)).
Proof.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkcv_one_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_one [v]) = mkc_one.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma nuprl_tnatp {o} :
  forall lib,
  nuprl
    lib
    mkc_tnatp
    mkc_tnatp
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 1)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}).
Proof.
  introv.
  rw @mkc_tnatp_eq.
  apply CL_set; fold (@nuprl o).
  unfold per_set.
  exists (@equality_of_int o lib).
  exists
    (fun (a a' : @CTerm o)
         (e : equality_of_int lib a a')
         (t t' : @CTerm o) =>
       forall (u v : @CTerm o),
         (forall k,
            computes_to_valc lib a (mkc_integer k)
            -> if (k <? 1)%Z
               then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
               else False)
         -> False);
    dands; auto.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply nuprl_int.

    + introv e.
      allrw @mkcv_le_substc.
      allrw @mkcv_one_substc.
      allrw @mkc_var_substc.
      allrw @mkc_le_eq.
      unfold equality_of_int in e; exrepnd; spcast.

      apply CL_func.
      unfold per_func.
      exists (fun t t' : @CTerm o =>
                if (k <? 1)%Z
                then t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom
                else False).
      exists (fun (a a' : @CTerm o) (e : if (k <? 1)%Z
                            then a ===>(lib) mkc_axiom # a' ===>(lib) mkc_axiom
                            else False) (t t' : @CTerm o) => False).
      dands; auto.

      * unfold type_family.
        eexists; eexists; eexists; eexists; eexists; eexists;
        dands; auto; spcast; try (fold nuprl).

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        remember ((k <? 1)%Z); symmetry in Heqb; destruct b.

        apply Z.ltb_lt in Heqb.

        pose proof (mkc_less_than_comp1 lib a mkc_one k 1) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp1 lib a' mkc_one k 1) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_value_respecting_left with (t1 := mkc_true).
        apply nuprl_value_respecting_right with (t2 := mkc_true).
        apply nuprl_mkc_true.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.

        apply Z.ltb_ge in Heqb.

        pose proof (mkc_less_than_comp2 lib a mkc_one k 1) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp2 lib a' mkc_one k 1) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_computes_left with (t1 := mkc_false); auto.
        apply nuprl_computes_right with (t2 := mkc_false); auto.
        rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        introv; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

        introv e; simphyps.
        allrw @csubst_mk_cv.
        rw @mkc_void_eq_mkc_false; rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        sp; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

      * intros; split; intro j; introv m.

        apply j with (u := a0) (v := a'0); auto.
        introv c.
        pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e;
          repeat (autodimp e hyp).
        inversion e; subst; GC; sp.

        pose proof (m k) as l; autodimp l hyp.
        apply j in l; sp.

  - introv.
    split; intro k; exrepnd.
    exists v; sp.
    exists e; sp.
Qed.

Lemma tnatp_type {o} : forall lib, @type o lib mkc_tnatp.
Proof.
  introv.
  unfold type, tequality.
  pose proof @nuprl_tnatp as h.
  exists
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 1)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}); sp.
Qed.

Definition reducek_pair {o} lib (t1 t2 : @NTerm o) (k : Z) (n : nat) :=
    reduces_in_atmost_k_steps lib t1 (mk_integer k) n
  # reduces_in_atmost_k_steps lib t2 (mk_integer k) n.

Definition equality_of_int_p_2 {o} lib (n m : @NTerm o) :=
  {x : Z # nat , reducek_pair lib n m (fst x) (snd x)}.

Definition equality_of_int_p_2_c {o} lib (n m : @CTerm o) :=
  equality_of_int_p_2 lib (get_cterm n) (get_cterm m).

Lemma equality_of_int_imp1 {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    <-> equality_of_int_p_2_c lib n m.
Proof.
  introv; split.
  - introv e.
    unfold equality_of_int in e; exrepnd; spcast.
    allunfold @computes_to_valc; allsimpl.
    allunfold @computes_to_value; repnd.
    allunfold @reduces_to; exrepnd.
    allunfold @reduces_in_atmost_k_steps.
    pose proof (no_change_after_value2 lib
                  (get_cterm n) k1 (mk_integer k) e2 e1 (Peano.max k1 k0)) as h1.
    autodimp h1 hyp; try (apply max_prop1).
    pose proof (no_change_after_value2 lib
                (get_cterm m) k0 (mk_integer k) e4 e0 (Peano.max k1 k0)) as h2.
    autodimp h2 hyp; try (apply max_prop2).
    exists ((k,Peano.max k1 k0)); simpl; sp.
    unfold reducek_pair; sp.
  - introv e.
    unfold equality_of_int.
    unfold equality_of_int_p_2_c, equality_of_int_p_2, reducek_pair in e.
    exrepnd; allsimpl.
    exists x0; dands; spcast;
    unfold computes_to_valc, computes_to_value; simpl;
    dands; try (apply isvalue_mk_integer);
    exists x; auto.
Qed.

Lemma compute_step_dec {o} :
  forall lib (t : @NTerm o),
    {u : NTerm $ compute_step lib t = csuccess u}
    [+]
    !{u : NTerm $ compute_step lib t = csuccess u}.
Proof.
  introv.
  remember (compute_step lib t); destruct c.
  - left.
    exists n; sp.
  - right; intro k; exrepnd; inversion k0.
Qed.

(*
Lemma reduces_in_atmost_k_steps_dec {o} :
  forall lib (pc : dec_consts o) k (t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t1 t2 k [+] !(reduces_in_atmost_k_steps lib t1 t2 k).
Proof.
  induction k; introv.

  - rw @reduces_in_atmost_k_steps_0.
    pose proof (deq_nterm pc t1 t2) as h; sp.

  - rw @reduces_in_atmost_k_steps_S.
    pose proof (compute_step_dec lib t1) as h.
    dorn h.

    + exrepnd.
      pose proof (IHk u t2) as j.
      dorn j.

      * left.
        exists u; sp.

      * right.
        intro c; exrepnd.
        rw h0 in c1; inversion c1; subst; sp.

    + right; intro j; exrepnd.
      apply h.
      exists u; sp.
Qed.
*)

Lemma deq_nterm_int {p} :
  forall (t : @NTerm p) z, {t = mk_integer z} + {t <> mk_integer z}.
Proof.
  introv.
  nterm_ind1 t as [v1|f1 ind|o1 lbt1 Hind] Case; intros.

  - Case "vterm".
    right; intro k; inversion k.

  - Case "sterm".
    right; intro k; inversion k.

  - Case "oterm".
    destruct o1; try (complete (right; intro k; inversion k)).
    destruct c; try (complete (right; intro k; inversion k)).
    destruct lbt1; try (complete (right; intro k; inversion k)).
    assert ({z < z0} + {z > z0} + {z = z0})%Z as h by (apply Z_dec).
    destruct h as [ h | h ]; subst.
    destruct h as [ h | h ]; sp; right; sp; inversion H; omega.
    left; sp.
Qed.

Lemma reduces_in_atmost_k_steps_int_dec {o} :
  forall lib k (t : @NTerm o) z,
    reduces_in_atmost_k_steps lib t (mk_integer z) k
    [+]
    !(reduces_in_atmost_k_steps lib t (mk_integer z) k).
Proof.
  induction k; introv.

  - rw @reduces_in_atmost_k_steps_0.
    pose proof (deq_nterm_int t z) as h; sp.

  - rw @reduces_in_atmost_k_steps_S.
    pose proof (compute_step_dec lib t) as h.
    dorn h.

    + exrepnd.
      pose proof (IHk u z) as j.
      dorn j.

      * left.
        exists u; sp.

      * right.
        intro c; exrepnd.
        rw h0 in c1; inversion c1; subst; sp.

    + right; intro j; exrepnd.
      apply h.
      exists u; sp.
Qed.

Lemma reducek_pair_dec {o} :
  forall lib (t1 t2 : @NTerm o) z n,
    reducek_pair lib t1 t2 z n [+] !(reducek_pair lib t1 t2 z n).
Proof.
  introv.
  unfold reducek_pair.
  pose proof (reduces_in_atmost_k_steps_int_dec lib n t1 z) as h1.
  pose proof (reduces_in_atmost_k_steps_int_dec lib n t2 z) as h2.
  dorn h1; dorn h2.
  - left; sp.
  - right; sp.
  - right; sp.
  - right; sp.
Qed.


(*

  The following is an adaptation of:
     http://coq.inria.fr/stdlib/Coq.Logic.ConstructiveEpsilon.html
  This is required to prove equality_of_int_imp_t without using
  the indefinite_description axiom.

*)

Inductive before_witness (P : Z -> nat -> Prop) (k : nat) : Prop :=
  | stop_pos : forall (z n : nat), k = z + n -> P (Z.of_nat z) n -> before_witness P k
  | stop_neg : forall z n, k = z + n -> P (Z.opp (Z.of_nat z)) n -> before_witness P k
  | next : before_witness P (S k) -> before_witness P k.

Fixpoint O_witness
         (P : Z -> nat -> Prop)
         (k : nat) : before_witness P k -> before_witness P 0 :=
  match k return (before_witness P k -> before_witness P 0) with
    | 0 => fun b => b
    | S n => fun b => O_witness P n (next P n b)
  end.

Definition inv_before_witness :
  forall (P : Z -> nat -> Prop) (k : nat),
    before_witness P k
    -> (forall z n : nat, k = z + n -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)
    -> before_witness P (S k) :=
  fun P k b =>
    match b
          in before_witness _ _
          return (forall z n, k = z + n -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)
                 -> before_witness P (S k) with
      | stop_pos _ _ z n e p => fun f => match fst (f z n e) p with end
      | stop_neg _ _ z n e p => fun f => match snd (f z n e) p with end
      | next _ _ b => fun _ => b
    end.

Lemma leS:
  forall n m : nat, n <= S m -> n <= m [+] n = S m.
Proof.
  introv; revert n.
  induction m; simpl; introv e.
  - destruct n; sp.
    destruct n; sp.
    provefalse.
    inversion e as [|x h].
    inversion h.
  - apply leb_correct in e.
    destruct n; allsimpl.
    + left; omega.
    + apply leb_complete in e.
      apply IHm in e; dorn e.
      left; omega.
      right; omega.
Qed.

(* This is the crux of linear_search *)
Lemma P_search :
  forall (P : Z -> nat -> Prop)
         (dec : forall z n, P z n [+] !P z n)
         (k : nat),
    {x : Z # nat & P (fst x) (snd x)}
    [+]
    (forall z n : nat, k = (z + n)%nat -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n).
Proof.
  intros P dec k.

  assert (forall k z,
            {x : Z # nat & P (fst x) (snd x)}
              [+]
              (forall n : nat, n <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp1.
  clear k.
  introv.
  induction k.
  pose proof (dec (Z.of_nat z) 0) as h.
  dorn h.
  left; exists (Z.of_nat z,0); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat z)) 0) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat z),0); simpl; sp.
  right; introv e.
  assert (n = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (dec (Z.of_nat z) (S k)) as h.
  dorn h.
  left; exists (Z.of_nat z,S k); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat z)) (S k)) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat z),S k); simpl; sp.
  right; introv e; simpl.
  apply leS in e.
  dorn e.
  apply IHk in e; sp.
  subst; sp.

  assert (forall k n,
            {x : Z # nat & P (fst x) (snd x)}
              [+]
              (forall z : nat, z <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp2.
  clear k.
  introv.
  induction k.
  pose proof (dec 0%Z n) as h.
  dorn h.
  left; exists (0%Z,n); simpl; sp.
  right; introv e.
  assert (z = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (dec (Z.of_nat (S k)) n) as h.
  dorn h.
  left; exists (Z.of_nat (S k),n); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat (S k))) n) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat (S k)),n); simpl; sp.
  right; introv e; simpl.
  apply leS in e.
  dorn e.
  apply IHk in e; sp.
  subst; sp.

  assert ({x : Z # nat & P (fst x) (snd x)}
            [+]
            (forall z n : nat, z <= k -> n <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp.
  induction k.
  pose proof (dec 0%Z 0) as h.
  dorn h.
  left; exists (0%Z,0); simpl; sp.
  right; introv e1 e2.
  assert (z = 0) by omega; assert (n = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (hyp1 (S k) (S k)) as h1.
  dorn h1.
  left; auto.
  pose proof (hyp2 (S k) (S k)) as h2.
  dorn h2.
  left; auto.
  right; introv e1 e2.
  apply leS in e1.
  apply leS in e2.
  dorn e1; dorn e2; subst.
  apply IHk; auto.
  apply h2; auto.
  apply h1; auto.
  apply h1; sp.

  dorn hyp.
  left; auto.
  right.
  introv e; subst.
  apply hyp; omega.
Qed.

Fixpoint linear_search
      (P : Z -> nat -> Prop)
      (dec : forall z n, P z n [+] !P z n)
      (k : nat)
      (b : before_witness P k) : {x : Z # nat & P (fst x) (snd x)} :=
  match P_search P dec k with
    | inl p => p
    | inr a => linear_search P dec (S k) (inv_before_witness P k b a)
  end.

Definition constructive_indefinite_ground_description_nat {o}
           lib (t1 t2 : @CTerm o) :
  equality_of_int_p_2_c lib t1 t2
  -> {x : Z # nat & reducek_pair lib (get_cterm t1) (get_cterm t2) (fst x) (snd x)}.
Proof.
  introv pex.
  apply linear_search with (k := 0).
  apply reducek_pair_dec; auto.
  unfold equality_of_int_p_2_c, equality_of_int_p_2 in pex; auto.
  exrepnd; allsimpl.
  apply O_witness with (k := Z.abs_nat x0 + x).
  pose proof (Zabs.Zabs_dec x0) as h.
  dorn h.
  - apply stop_pos with (z := Z.abs_nat x0) (n := x); auto.
    rw h in pex0.
    rw Znat.Zabs2Nat.id_abs; auto.
  - apply stop_neg with (z := Z.abs_nat x0) (n := x); auto.
    rw h in pex0.
    rw Znat.Zabs2Nat.id_abs; auto.
Qed.

(*

   Thanks to constructive_indefinite_ground_description_nat,
   the following proof does not need the indefinite_description axiom

 *)

Definition equality_of_int_t {o} lib (n m : @CTerm o) :=
  {k : Z | n ===>(lib) (mkc_integer k)
         # m ===>(lib) (mkc_integer k)}.

Lemma equality_of_int_imp_t {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    -> equality_of_int_t lib n m.
Proof.
  introv e.
  apply equality_of_int_imp1 in e.
  apply constructive_indefinite_ground_description_nat in e; auto.
  exrepnd; allsimpl.
  unfold equality_of_int_t.
  unfold reducek_pair in e0; repnd.
  exists x0; dands; spcast;
  unfold computes_to_valc, computes_to_value; simpl;
  dands; try (apply isvalue_mk_integer);
  exists x; auto.
Qed.

(*
Here is the alternative that uses the indefinite_description axiom.

Axiom indefinite_description :
  forall (A : Type) (P : A -> Prop),
    ex P -> sig P.

Lemma equality_of_int_imp_t :
  forall n m,
    equality_of_int n m
    -> equality_of_int_t n m.
Proof.
  introv e.
  unfold equality_of_int in e.
  unfold equality_of_int_t.
  apply indefinite_description; auto.
Qed.
*)

Definition equality_of_int_tt {o} lib (n m : @CTerm o) :=
  {k : Z & computes_to_valc lib n (mkc_integer k)
         # computes_to_valc lib m (mkc_integer k)}.

Lemma equality_of_int_imp_tt {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    -> equality_of_int_tt lib n m.
Proof.
  introv e.
  apply equality_of_int_imp1 in e.
  apply constructive_indefinite_ground_description_nat in e; auto.
  exrepnd; allsimpl.
  unfold equality_of_int_tt.
  unfold reducek_pair in e0; repnd.
  exists x0; dands; spcast;
  unfold computes_to_valc, computes_to_value; simpl;
  dands; try (apply isvalue_mk_integer);
  exists x; auto.
Qed.
