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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export per_props_util.
Require Export per_props_tacs.


Lemma type_extensionality_per_qtime_nuprl {o} :
  @type_extensionality o (per_qtime nuprl).
Proof.
  introv per e.
  unfold per_qtime in *; exrepnd.
  exists eqa A B; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_qtime_nuprl : slow.

Lemma type_extensionality_per_qtime_nuprli {o} :
  forall i, @type_extensionality o (per_qtime (nuprli i)).
Proof.
  introv per e.
  unfold per_qtime in *; exrepnd.
  exists eqa A B; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_qtime_nuprli : slow.

Lemma uniquely_valued_per_qtime_nuprl {o} :
  @uniquely_valued o (per_qtime nuprl).
Proof.
  introv pera perb.
  unfold per_qtime in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq.
  apply cequivc_ext_mkc_qtime_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_qtime_eq_bar.
  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprl_refl in pera3.
  apply nuprl_refl in perb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_qtime_nuprl : slow.

Lemma uniquely_valued_per_qtime_nuprli {o} :
  forall i, @uniquely_valued o (per_qtime (nuprli i)).
Proof.
  introv pera perb.
  unfold per_qtime in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq.
  apply cequivc_ext_mkc_qtime_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprli_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_qtime_eq_bar.
  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprli_refl in pera3.
  apply nuprli_refl in perb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_qtime_nuprli : slow.

Lemma local_per_bar_per_qtime_nuprl {o} :
  @local_ts o (per_bar (per_qtime nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_qtime_nuprl : slow.

Lemma local_per_bar_per_qtime_nuprli {o} :
  forall i, @local_ts o (per_bar (per_qtime (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_qtime_nuprli : slow.

Lemma dest_nuprl_per_qtime_l {o} :
  forall (ts : cts(o)) lib T A T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_qtime_l {o} :
  forall i (ts : cts(o)) lib T A T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime_nuprli; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_qtime {o} :
  forall (lib : @SL o) A B eq,
    nuprl lib (mkc_qtime A) (mkc_qtime B) eq
    -> per_bar (per_qtime nuprl) lib (mkc_qtime A) (mkc_qtime B) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_qtime_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_qtime {o} :
  forall i (lib : @SL o) A B eq,
    nuprli i lib (mkc_qtime A) (mkc_qtime B) eq
    -> per_bar (per_qtime (nuprli i)) lib (mkc_qtime A) (mkc_qtime B) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_qtime_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_qtime2 {o} :
  forall lib (eq : per(o)) A B,
    nuprl lib (mkc_qtime A) (mkc_qtime B) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_qtime_eq_bar_lib_per lib eqa)))
        # all_in_bar_ext bar (fun lib' x => nuprl lib' A B (eqa lib' x)).
Proof.
  introv u.
  apply dest_nuprl_qtime in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A B (eqa0 lib'' y))
               # (eqa lib' x) <=2=> (per_qtime_eq_bar lib' eqa0) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_qtime in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.
  }
  clear u0.

  apply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.
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
    apply implies_eq_term_equals_per_qtime_eq_bar.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
      exrepnd; spcast.
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
Qed.

Lemma dest_nuprli_qtime2 {o} :
  forall i lib (eq : per(o)) A B,
    nuprli i lib (mkc_qtime A) (mkc_qtime B) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_qtime_eq_bar_lib_per lib eqa)))
        # all_in_bar_ext bar (fun lib' x => nuprli i lib' A B (eqa lib' x)).
Proof.
  introv u.
  apply dest_nuprli_qtime in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A B (eqa0 lib'' y))
               # (eqa lib' x) <=2=> (per_qtime_eq_bar lib' eqa0) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_qtime in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].

    exists eqa0; dands; auto.
  }
  clear u0.

  apply all_in_bar_ext_exists_lib_per_implies_exists in e; exrepnd.
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
    apply implies_eq_term_equals_per_qtime_eq_bar.
    introv; simpl; unfold raise_ext_per.

    split; intro h.

    - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
      pose proof (u0 _ e) as u0; simpl in *.

      pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
      exrepnd; spcast.
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
Qed.




Lemma tequality_mkc_qtime {p} :
  forall lib (A B : @CTerm p),
    tequality lib (mkc_qtime A) (mkc_qtime B)
    <=> tequality lib A B.
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_qtime2 in teq0; exrepnd.
    dands; eauto 3 with slow.

  - unfold tequality in teq; exrepnd.
    rename eq into eqa.

    pose proof (nuprl_monotone_func lib A B eqa teq0) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_qtime_eq_bar lib eqa'); apply CL_qtime; unfold per_qtime.
    exists eqa' A B; sp; spcast; eauto 3 with slow.
    introv; apply tya0.
Qed.

Lemma per_bar_eq_per_qtime_eq_bar_lib_per_iff {o} :
  forall {lib : SL} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) p1 p2,
    (per_bar_eq bar (per_qtime_eq_bar_lib_per lib eqa) p1 p2)
      <=>
      exists bar,
        all_in_bar_ext
          bar
          (fun lib' x => per_qtime_eq lib' (eqa lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_qtime_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    unfold per_bar_eq in *; simpl in *.
    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.

    apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_qtime_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.
    unfold per_qtime_eq_bar in h0; exrepnd.
    exists bar0; simpl in *.
    unfold raise_ext_per in *.

    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
    eapply implies_eq_term_equals_per_qtime_eq; try exact h1;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).

  - unfold per_bar_eq; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x).
    introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h0 _ br'1 lib'3 (lib_extends_trans (lib_extends_trans e ext') br'2) (lib_extends_trans (lib_extends_trans e x0) x)) as h0; simpl in *.

    eapply implies_eq_term_equals_per_qtime_eq; try exact h0;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).
Qed.

Lemma equality_mkc_qtime {p} :
  forall lib (t1 t2 A : @CTerm p),
    equality lib t1 t2 (mkc_qtime A)
    <=> (type lib A
         # all_in_ex_bar lib (fun lib => {a1, a2 : CTerm
             , ccequivc lib t1 a1
             # ccequivc lib t2 a2
             # ccequivc_ext lib t1 t2
             # equality lib a1 a2 A})).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_qtime2 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.
    dands; eauto 3 with slow;[].

    apply per_bar_eq_per_qtime_eq_bar_lib_per_iff in e0; exrepnd.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar) in e2.
    apply (implies_all_in_bar_ext_intersect_bars_right _ bar0) in e1.
    remember (intersect_bars bar0 bar) as b.
    clear dependent bar.
    clear dependent bar0.
    exists b.
    introv br ext.
    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (e2 _ br _ ext xt) as e2; simpl in *.
    pose proof (e1 _ br _ ext xt) as e1; simpl in *.

    unfold per_qtime_eq in *; exrepnd.
    eexists; eexists; dands; eauto.
    apply (equality_eq1 lib'0 A A x y (eqa lib'0 xt)); auto.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.
    pose proof (nuprl_monotone_func lib A A eqa e1) as tya; exrepnd.
    rename eq' into eqa'.

    exists (per_qtime_eq_bar lib eqa'); dands.

    {
      apply CL_qtime; unfold per_qtime.
      exists eqa' A A; dands; spcast; eauto 3 with slow.
      introv; apply tya0.
    }

    unfold all_in_ex_bar in e; exrepnd; exists bar; introv br ext; introv.
    pose proof (e0 _ br _ ext) as e0; simpl in *; exrepnd.
    unfold per_qtime_eq.
    exists a1 a2; dands; auto.
    apply (equality_eq1 lib'0 A A a1 a2 (eqa' lib'0 x)); eauto 3 with slow.
    apply tya0.
Qed.
