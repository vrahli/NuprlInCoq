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


Require Export per_props_tacs.
Require Export per_props_util.
Require Export csubst6.



Lemma type_extensionality_per_image_nuprl {o} :
  @type_extensionality o (per_image nuprl).
Proof.
  introv per e.
  unfold per_image in *; exrepnd.
  exists eqa A1 A2 f1 f2; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_image_nuprl : slow.

Lemma type_extensionality_per_image_nuprli {o} :
  forall i, @type_extensionality o (per_image (nuprli i)).
Proof.
  introv per e.
  unfold per_image in *; exrepnd.
  exists eqa A1 A2 f1 f2; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_image_nuprli : slow.

Lemma uniquely_valued_per_image_nuprl {o} :
  @uniquely_valued o (per_image nuprl).
Proof.
  introv pera perb.
  unfold per_image in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq.
  apply cequivc_ext_mkc_image_implies in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprl_refl in pera3.
  apply nuprl_refl in perb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_image_nuprl : slow.

Lemma uniquely_valued_per_image_nuprli {o} :
  forall i, @uniquely_valued o (per_image (nuprli i)).
Proof.
  introv pera perb.
  unfold per_image in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq.
  apply cequivc_ext_mkc_image_implies in ceq0.
  repnd.

  eapply in_ext_ext_nuprli_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow.
  introv.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprli_refl in pera3.
  apply nuprli_refl in perb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_image_nuprli : slow.

Lemma local_per_bar_per_image_nuprl {o} :
  @local_ts o (per_bar (per_image nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_image_nuprl : slow.

Lemma local_per_bar_per_image_nuprli {o} :
  forall i, @local_ts o (per_bar (per_image (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_image_nuprli : slow.

Lemma dest_nuprl_per_image_l {o} :
  forall (ts : cts(o)) lib T A f T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> close ts lib T T' eq
    -> per_bar (per_image (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_image_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_image_l {o} :
  forall i (ts : cts(o)) lib T A f T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> close ts lib T T' eq
    -> per_bar (per_image (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_image_nuprli; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma iscvalue_image {o} :
  forall (A f : @CTerm o), iscvalue (mkc_image A f).
Proof.
  introv.
  split; eauto 3 with slow.
  destruct_cterms; simpl; auto.
Qed.
Hint Resolve iscvalue_image : slow.

Lemma dest_nuprl_image {o} :
  forall (lib : @library o) A f B g eq,
    nuprl lib (mkc_image A f) (mkc_image B g) eq
    -> per_bar (per_image nuprl) lib (mkc_image A f) (mkc_image B g) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_image_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_image {o} :
  forall i (lib : @library o) A f B g eq,
    nuprli i lib (mkc_image A f) (mkc_image B g) eq
    -> per_bar (per_image (nuprli i)) lib (mkc_image A f) (mkc_image B g) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_image_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_image2 {o} :
  forall lib (eq : per(o)) A f B g,
    nuprl lib (mkc_image A f) (mkc_image B g) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_image_eq_bar_lib_per lib eqa f)))
        # all_in_bar_ext bar (fun lib' x => nuprl lib' A B (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => ccequivc_ext lib' f g).
Proof.
  introv u.
  apply dest_nuprl_image in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A B (eqa0 lib'' y))
               # ccequivc_ext lib' f g
               # (eqa lib' x) <=2=> (per_image_eq_bar lib' eqa0 f) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_image in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.

    { eapply ccequivc_ext_trans;[eauto|].
      eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym;eauto]; auto. }

    { eapply eq_term_equals_trans;[eauto|].
      apply implies_eq_term_equals_per_image_eq_bar; eauto 2 with slow. }
  }
  clear u0.

  eapply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.

  exists bar (bar_lib_per2lib_per feqa).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].

    simpl.
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
      unfold type_family_ext in q; exrepnd; spcast.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprl_refl in q0.
      apply nuprl_refl in u0.
      eapply nuprl_uniquely_valued in q0; try exact u0.
      apply q0; auto.

    - exrepnd.
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib1 br0 _ ext0 x0) as q; repnd.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprl_refl in q0.
      apply nuprl_refl in u0.
      eapply nuprl_uniquely_valued in q0; try exact u0.
      apply q0; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h0 _ (lib_extends_refl lib'0)) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e1 _ (lib_extends_refl lib'0)) as e1; simpl in *.
      apply nuprl_refl in e1.
      apply nuprl_refl in h0.
      eapply nuprl_uniquely_valued in e1; try exact h0.
      apply e1; auto.
  }

  {
    introv br ext x.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd; auto.
  }
Qed.

Lemma dest_nuprli_image2 {o} :
  forall i lib (eq : per(o)) A f B g,
    nuprli i lib (mkc_image A f) (mkc_image B g) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_image_eq_bar_lib_per lib eqa f)))
        # all_in_bar_ext bar (fun lib' x => nuprli i lib' A B (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => ccequivc_ext lib' f g).
Proof.
  introv u.
  apply dest_nuprli_image in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A B (eqa0 lib'' y))
               # ccequivc_ext lib' f g
               # (eqa lib' x) <=2=> (per_image_eq_bar lib' eqa0 f) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_image in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.

    { eapply ccequivc_ext_trans;[eauto|].
      eapply ccequivc_ext_trans;[|apply ccequivc_ext_sym;eauto]; auto. }

    { eapply eq_term_equals_trans;[eauto|].
      apply implies_eq_term_equals_per_image_eq_bar; eauto 2 with slow. }
  }
  clear u0.

  eapply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.

  exists bar (bar_lib_per2lib_per feqa).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].

    simpl.
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
      unfold type_family_ext in u0; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
      unfold type_family_ext in q; exrepnd; spcast.
      computes_to_value_isvalue.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprli_refl in q0.
      apply nuprli_refl in u0.
      eapply nuprli_uniquely_valued in q0; try exact u0.
      apply q0; auto.

    - exrepnd.
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib1 br0 _ ext0 x0) as q; repnd.
      pose proof (q0 _ (lib_extends_refl lib'1)) as q0; simpl in *.
      apply nuprli_refl in q0.
      apply nuprli_refl in u0.
      eapply nuprli_uniquely_valued in q0; try exact u0.
      apply q0; auto.
  }

  {
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h0 _ (lib_extends_refl lib'0)) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e1 _ (lib_extends_refl lib'0)) as e1; simpl in *.
      apply nuprli_refl in e1.
      apply nuprli_refl in h0.
      eapply nuprli_uniquely_valued in e1; try exact h0.
      apply e1; auto.
  }

  {
    introv br ext x.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd; auto.
  }
Qed.

Lemma per_bar_eq_per_image_eq_bar_lib_per_iff {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) f p1 p2,
    (per_bar_eq bar (per_image_eq_bar_lib_per lib eqa f) p1 p2)
      <=>
      exists bar,
        all_in_bar_ext
          bar
          (fun lib' x => per_image_eq lib' (eqa lib' x) f p1 p2).
Proof.
  introv; split; intro h.

  - apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_eq_image_eq; apply lib_per_cond. }
    unfold per_bar_eq in *; simpl in *.
    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.

    apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_eq_image_eq; apply lib_per_cond. }
    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.
    unfold per_image_eq_bar in h0; exrepnd.
    exists bar0; simpl in *.
    unfold raise_ext_per_fam in *; simpl in *.
    unfold raise_ext_per in *.

    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
    eapply implies_eq_term_equals_eq_image_eq; try exact h1; apply lib_per_cond.

  - unfold per_bar_eq; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x).
    introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h0 _ br'1 lib'3 (lib_extends_trans (lib_extends_trans e ext') br'2) (lib_extends_trans (lib_extends_trans e x0) x)) as h0; simpl in *.
    eapply implies_eq_term_equals_eq_image_eq; try exact h0; apply lib_per_cond.
Qed.




Inductive equal_in_image {p} lib (A f t1 t2 : @CTerm p) : [U] :=
| eq_in_image_cl :
    forall t,
      equal_in_image lib A f t1 t
      -> equal_in_image lib A f t t2
      -> equal_in_image lib A f t1 t2
| eq_in_image_eq :
    forall a1 a2,
      equality lib a1 a2 A
      -> ccequivc_ext lib t1 (mkc_apply f a1)
      -> ccequivc_ext lib t2 (mkc_apply f a2)
      -> equal_in_image lib A f t1 t2.


Lemma per_image_eq_implies_equal_in_image {o} :
  forall lib (eq : per(o)) T f t1 t2,
    nuprl lib T T eq
    -> per_image_eq lib eq f t1 t2
    -> equal_in_image lib T f t1 t2.
Proof.
  introv n h.
  induction h.

  - eapply eq_in_image_cl; eauto.

  - eapply eq_in_image_eq; eauto.
    apply (equality_eq1 lib T T a1 a2 eq); auto.
Qed.
Hint Resolve per_image_eq_implies_equal_in_image : slow.

Lemma equal_in_image_implies_per_image_eq {o} :
  forall lib (eq : per(o)) T f t1 t2,
    nuprl lib T T eq
    -> equal_in_image lib T f t1 t2
    -> per_image_eq lib eq f t1 t2.
Proof.
  introv n h.
  induction h.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; eauto.
    apply (equality_eq1 lib T T a1 a2 eq); auto.
Qed.
Hint Resolve equal_in_image_implies_per_image_eq : slow.

Lemma equality_in_mkc_image {p} :
  forall lib (t1 t2 T f : @CTerm p),
    equality lib t1 t2 (mkc_image T f)
    <=> (type lib T # all_in_ex_bar lib (fun lib => equal_in_image lib T f t1 t2)).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_image2 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.
    dands; eauto 3 with slow;[].

    apply per_bar_eq_per_image_eq_bar_lib_per_iff in e0.
    exrepnd.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in e3.
    apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in e2.
    remember (intersect_bars bar bar0) as b.
    clear dependent bar.
    clear dependent bar0.
    exists b.
    introv br ext.
    pose proof (e3 _ br _ ext) as e3; simpl in *.
    pose proof (e2 _ br _ ext) as e2; simpl in *.

    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (e3 xt) as e3.
    pose proof (e2 xt) as e2.
    eauto 3 with slow.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.

    pose proof (nuprl_monotone_func lib T T eq e1) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_image_eq_bar lib eqa' f); dands; auto; eauto 3 with slow.

    {
      apply CL_image; unfold per_image.
      exists eqa' T T f f; dands; spcast; eauto 3 with slow.
      introv; apply tya0.
    }

    unfold all_in_ex_bar in e; exrepnd; exists bar; introv br ext; introv.
    pose proof (e0 _ br _ ext) as e0; simpl in *.
    eapply equal_in_image_implies_per_image_eq; eauto.
    apply tya0.
Qed.

Lemma equal_in_image_prop {p} :
  forall lib (A f t1 t2 : @CTerm p),
    equal_in_image lib A f t1 t2
    -> {a1, a2 : CTerm
        , ccequivc_ext lib t1 (mkc_apply f a1)
        # ccequivc_ext lib t2 (mkc_apply f a2)
        # member lib a1 A
        # member lib a2 A}.
Proof.
  introv e.
  induction e; exrepnd.

  exists a0 a2; sp.
  exists a1 a2; sp.
  { allapply @equality_refl; sp. }
  { apply @equality_refl with (t2 := a1); apply equality_sym; sp. }
Qed.

Lemma tequality_mkc_image {o} :
  forall lib (T1 T2 f1 f2 : @CTerm o),
    tequality lib (mkc_image T1 f1) (mkc_image T2 f2)
    <=> (tequality lib T1 T2 # ccequivc_bar lib f1 f2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_image2 in teq0; exrepnd.
    dands; eauto 3 with slow.
    apply ccequivc_ext_bar_iff_ccequivc_bar.
    exists bar; introv br ext.
    apply (teq0 _ br); eauto 3 with slow.

  - unfold tequality in teq0; exrepnd.
    pose proof (nuprl_monotone_func lib T1 T2 eq teq1) as tya; exrepnd.
    rename eq' into eqa'.
    apply ccequivc_ext_bar_iff_ccequivc_bar in teq.
    unfold ccequivc_ext_bar, all_in_ex_bar in teq; exrepnd.

    exists (per_bar_eq bar (per_image_eq_bar_lib_per lib eqa' f1)).
    apply CL_bar; exists bar (per_image_eq_bar_lib_per lib eqa' f1); dands; auto;[].
    introv br ext; introv; simpl; fold (@nuprl o).
    pose proof (teq0 _ br _ ext) as teq0; simpl in *.

    apply CL_image; fold (@nuprl o).
    exists (raise_lib_per eqa' x) T1 T2 f1 f2; dands; spcast; eauto 3 with slow.
    introv; simpl.
    apply tya0.
Qed.
