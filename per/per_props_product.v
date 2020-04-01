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
           Abhishek Anand

*)


Require Export per_props_tacs.
Require Export per_props_fam2.
Require Export per_props_util.
Require Export csubst6.


Lemma type_extensionality_per_product_bar_nuprl {o} :
  @type_extensionality o (per_product_bar nuprl).
Proof.
  introv per e.
  unfold per_product_bar in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_product_bar_nuprl : slow.

Lemma uniquely_valued_per_product_bar_nuprl {o} :
  @uniquely_valued o (per_product_bar nuprl).
Proof.
  introv pera perb.
  unfold per_product_bar in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp pera3.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_product_implies in ceq.
  apply ccequivc_ext_mkc_product_implies in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera5;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera5;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_left  in pera0;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_right in pera0;[|apply bcequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_product_eq_bar.

  {
    introv.
    pose proof (pera5 _ e) as pera5.
    pose proof (perb5 _ e) as perb5.
    simpl in *.
    apply nuprl_refl in pera5.
    apply nuprl_refl in perb5.
    eapply nuprl_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v1) as perb0.
    simpl in *.
    apply nuprl_refl in pera0.
    apply nuprl_refl in perb0.
    eapply nuprl_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_product_bar_nuprl : slow.

Lemma local_per_bar_per_product_bar_nuprl {o} :
  @local_ts o (per_bar (per_product_bar nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_product_bar_nuprl : slow.

Lemma dest_nuprl_per_product_l {o} :
  forall (ts : cts(o)) uk lib T A v B T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> close ts uk lib T T' eq
    -> per_bar (per_product_bar (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_product {o} :
  forall uk (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprl uk lib (mkc_product A v B) (mkc_product C w D) eq
    -> per_bar (per_product_bar nuprl) uk lib (mkc_product A v B) (mkc_product C w D) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_product_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma type_family_ext_nuprl_product_uniquely_valued_eqas {o} :
  forall uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_product nuprl uk lib (mkc_product A v B) (mkc_product C w D) eqa1 eqb1
    -> type_family_ext mkc_product nuprl uk lib (mkc_product A v B) (mkc_product C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  repeat ccomputes_to_valc_ext_val.

  eapply in_ext_ext_nuprl_value_respecting_left  in tfa4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in tfa4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_left  in tfb4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in tfb4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_left  in tfa1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_right in tfa1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_left  in tfb1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprl_value_respecting_right in tfb1;[|apply bcequivc_ext_sym;eauto].

  introv.
  pose proof (tfa4 _ e) as tfa4.
  pose proof (tfb4 _ e) as tfb4.
  simpl in *.
  apply nuprl_refl in tfa4.
  apply nuprl_refl in tfb4.
  eapply nuprl_uniquely_valued; eauto.
Qed.

Lemma dest_nuprl_product2 {o} :
  forall uk lib (eq : per(o)) A v B C w D,
    nuprl uk lib (mkc_product A v B) (mkc_product C w D) eq
    ->
    exists (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq lib (per_product_eq_bar_lib_per lib eqa eqb))
      # in_open_bar_ext lib (fun lib' x => nuprl uk lib' A C (eqa lib' x))
      # in_open_bar_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprl uk lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e))
      # is_swap_invariant_cond uk eqa v B w D.
Proof.
  introv u.
  apply dest_nuprl_product in u.
  unfold per_bar in u; exrepnd.

  unfold per_product_bar in u1.
  apply in_open_bar_ext_choice in u1; exrepnd.
  apply in_open_bar_eqa_choice in u2; exrepnd.
  apply in_open_bar_eqa_fam_choice in u1; exrepnd.

  assert (FunDeqEqa_cond Feqa) as cond.
  { eapply nuprl_type_family_ext_implies_FunDeqEq_cond; try exact u2; eauto 3 with slow. }

  exists (fun_lib_dep_eqa Feqa).
  exists (fun_lib_dep_eqb cond Feqb).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_product_eq_bar; simpl.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as u; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ z0) in u0.
        eapply @type_family_ext_nuprl_uniquely_valued_eqas in u0; try exact q0; auto; simpl in *; eauto 3 with slow;[].
        pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
        unfold raise_ext_per in u0; simpl in *.
        eapply lib_per_cond; apply u0; eapply lib_per_cond; eauto.
    }

    {
      repeat introv; simpl; unfold raise_ext_per_fam; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.
        eapply lib_per_fam_cond; eauto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as xx; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ z0) in xx0.
        dup xx0 as eqas.
        dup xx0 as eqbs.
        eapply @type_family_ext_nuprl_uniquely_valued_eqas in eqas; try exact q0; auto; simpl in *; eauto 3 with slow;[].
        eapply @type_family_ext_nuprl_uniquely_valued_eqbs in eqbs; try exact q0; auto; simpl in *; eauto 3 with slow;[].

        pose proof (eqas _ (lib_extends_refl _)) as eqas; simpl in *.

        assert (raise_ext_per (Feqa lib' ext lib'0 xtb z) e lib'1 (lib_extends_refl lib'1) a a') as eqa1.
        { unfold raise_ext_per; simpl.
          eapply lib_per_cond; eauto. }
        assert (raise_ext_per (Feqa lib1 ext1 lib2 ext2 extz) z0 lib'1 (lib_extends_refl lib'1) a a') as eqa2.
        { unfold raise_ext_per; simpl.
          apply eqas.
          eapply lib_per_cond; eauto. }

        pose proof (eqbs _ (lib_extends_refl _) a a' eqa1 eqa2) as eqbs; simpl in *.

        unfold raise_ext_per_fam in eqbs; simpl in *.
        eapply lib_per_fam_cond; apply eqbs; eapply lib_per_fam_cond; eauto.
    }
  }

  {
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    unfold type_family_ext in q0; exrepnd.
    repeat ccomputes_to_valc_ext_val.

    pose proof (q4 _ (lib_extends_refl lib'0)) as q4; simpl in *.
    eapply nuprl_value_respecting_left in q4;[|apply ccequivc_ext_sym;eauto].
    eapply nuprl_value_respecting_right in q4;[|apply ccequivc_ext_sym;eauto].
    eapply type_extensionality_nuprl;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      pose proof (u6 _ z0) as u6; simpl in *.
      apply nuprl_refl in u6.
      apply nuprl_refl in q4.
      eapply nuprl_value_respecting_left in u6;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprl_value_respecting_right in u6;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprl_uniquely_valued in u6; try exact q4.
      apply u6; auto.
  }

  {
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    unfold type_family_ext in q0; exrepnd.
    repeat ccomputes_to_valc_ext_val.

    assert ((Feqa lib' ext lib'0 xtb z) lib'0 (lib_extends_refl lib'0) a a') as e1.
    { simpl in *; exrepnd; eapply cond; eauto. }

    pose proof (q0 _ (lib_extends_refl lib'0) a a' e1) as q0; simpl in *.
    eapply nuprl_value_respecting_left in q0;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto].
    eapply nuprl_value_respecting_right in q0;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto].

    eapply type_extensionality_nuprl;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0).
      eapply lib_per_fam_cond; eauto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      assert ((Feqa lib1 ext1 lib2 ext2 extz) lib'0 z0 a a') as eb.
      { simpl in *; exrepnd; eapply cond; eauto. }

      pose proof (u1 _ z0 a a' eb) as u1; simpl in *.
      eapply nuprl_value_respecting_left in u1;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto] ]; auto;[].
      eapply nuprl_value_respecting_right in u1;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto] ]; auto;[].
      apply nuprl_refl in u1.
      apply nuprl_refl in q0.
      eapply nuprl_uniquely_valued in u1; try exact q0.
      apply u1; auto; eapply lib_per_fam_cond; eauto.
  }

  {
    destruct uk; simpl; auto;[].
    dands; introv ext; simpl in *; exrepnd;
      pose proof (u2 _ ext1 _ ext2 extz) as u2; simpl in u2; repnd;
        unfold type_family_ext in *; simpl in *; exrepnd;
          repeat ccomputes_to_valc_ext_val; eauto 3 with slow.
  }
Qed.

Lemma type_extensionality_per_product_bar_nuprli {o} :
  forall i, @type_extensionality o (per_product_bar (nuprli i)).
Proof.
  introv per e.
  unfold per_product_bar in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_product_bar_nuprli : slow.

Lemma uniquely_valued_per_product_bar_nuprli {o} :
  forall i, @uniquely_valued o (per_product_bar (nuprli i)).
Proof.
  introv pera perb.
  unfold per_product_bar in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp perb3.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_product_implies in ceq.
  apply ccequivc_ext_mkc_product_implies in ceq0.
  repnd.
  eapply in_ext_ext_nuprli_value_respecting_left  in pera5;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera5;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_left  in pera0;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_right in pera0;[|apply bcequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_product_eq_bar.

  {
    introv.
    pose proof (pera5 _ e) as pera5.
    pose proof (perb5 _ e) as perb5.
    simpl in *.
    apply nuprli_refl in pera5.
    apply nuprli_refl in perb5.
    eapply nuprli_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v1) as perb0.
    simpl in *.
    apply nuprli_refl in pera0.
    apply nuprli_refl in perb0.
    eapply nuprli_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_product_bar_nuprli : slow.

Lemma local_per_bar_per_product_bar_nuprli {o} :
  forall i, @local_ts o (per_bar (per_product_bar (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_product_bar_nuprli : slow.

Lemma dest_nuprli_per_product_l {o} :
  forall i uk (ts : cts(o)) lib T A v B T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> close ts uk lib T T' eq
    -> per_bar (per_product_bar (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_product {o} :
  forall i uk (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprli i uk lib (mkc_product A v B) (mkc_product C w D) eq
    -> per_bar (per_product_bar (nuprli i)) uk lib (mkc_product A v B) (mkc_product C w D) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_product_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma type_family_ext_nuprli_product_uniquely_valued_eqas {o} :
  forall i uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_product (nuprli i) uk lib (mkc_product A v B) (mkc_product C w D) eqa1 eqb1
    -> type_family_ext mkc_product (nuprli i) uk lib (mkc_product A v B) (mkc_product C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.

  repeat ccomputes_to_valc_ext_val.
  eapply in_ext_ext_nuprli_value_respecting_left  in tfa4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in tfa4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_left  in tfa1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_right in tfa1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_left  in tfb4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in tfb4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_left  in tfb1;[|apply bcequivc_ext_sym;eauto].
  eapply in_ext_ext_fam_nuprli_value_respecting_right in tfb1;[|apply bcequivc_ext_sym;eauto].

  introv.
  pose proof (tfa4 _ e) as tfa4.
  pose proof (tfb4 _ e) as tfb4.
  simpl in *.
  apply nuprli_refl in tfa4.
  apply nuprli_refl in tfb4.
  eapply nuprli_uniquely_valued; eauto.
Qed.

(*Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa_i {o} :
  forall {lib lib'} {bar : @BarLib o lib} {feqa : bar-and-fam-per(lib,bar,o)}
         {A v B C w D i}
         (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product (nuprli i) lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
         {x : lib_extends lib' lib}
         {a a'}
         (lib1 : library)
         (br : bar_lib_bar bar lib1)
         (ext : lib_extends lib' lib1)
         (y : lib_extends lib' lib),
    (bar_and_fam_per2lib_per feqa) lib' x a a'
    -> (lpaf_eqa (feqa lib1 br lib' ext y)) lib' (lib_extends_refl lib') a a'.
Proof.
  introv F h; simpl in *; exrepnd.
  pose proof (F _ br0 _ ext0 x0) as q1.
  pose proof (F _ br _ ext y) as q2.
  eapply type_family_ext_nuprli_product_uniquely_valued_eqas in q1; try exact q2.
  simpl in *.
  pose proof (q1 _ (lib_extends_refl lib')) as q1; simpl in *.
  apply q1; auto.
Qed.*)

(*Definition bar_and_fam_per2lib_per_fam_i {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o))
           {A v B C w D i}
           (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product (nuprli i) lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
  : lib-per-fam(lib,bar_and_fam_per2lib_per(feqa),o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) a a' (e : bar_and_fam_per2lib_per(feqa) lib' x a a') t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {y : lib_extends lib' lib
            , lpaf_eqb
                (feqa lib1 br lib' ext y)
                lib'
                (lib_extends_refl lib')
                a a'
                (bar_and_fam_per2lib_per_implies_lpaf_eqa_i F lib1 br ext y e)
                t1 t2}}}}).

  repeat introv.
  split; introv h; exrepnd.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
Defined.*)

Lemma dest_nuprli_product2 {o} :
  forall i uk lib (eq : per(o)) A v B C w D,
    nuprli i uk lib (mkc_product A v B) (mkc_product C w D) eq
    ->
    exists (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq lib (per_product_eq_bar_lib_per lib eqa eqb))
      # in_open_bar_ext lib (fun lib' x => nuprli i uk lib' A C (eqa lib' x))
      # in_open_bar_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprli i uk lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e))
      # is_swap_invariant_cond uk eqa v B w D.
Proof.
  introv u.
  apply dest_nuprli_product in u.
  unfold per_bar in u; exrepnd.

  unfold per_product_bar in u1.
  apply in_open_bar_ext_choice in u1; exrepnd.
  apply in_open_bar_eqa_choice in u2; exrepnd.
  apply in_open_bar_eqa_fam_choice in u1; exrepnd.

  assert (FunDeqEqa_cond Feqa) as cond.
  { eapply nuprli_type_family_ext_implies_FunDeqEq_cond; try exact u2; eauto 3 with slow. }

  exists (fun_lib_dep_eqa Feqa).
  exists (fun_lib_dep_eqb cond Feqb).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_product_eq_bar; simpl.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as u; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ z0) in u0.
        eapply @type_family_ext_nuprli_uniquely_valued_eqas in u0; try exact q0; auto; simpl in *; eauto 3 with slow;[].
        pose proof (u0 _ (lib_extends_refl _)) as u0; simpl in *.
        unfold raise_ext_per in u0; simpl in *.
        eapply lib_per_cond; apply u0; eapply lib_per_cond; eauto.
    }

    {
      repeat introv; simpl; unfold raise_ext_per_fam; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.
        eapply lib_per_fam_cond; eauto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as xx; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ _ z0) in xx0.
        dup xx0 as eqas.
        dup xx0 as eqbs.
        eapply @type_family_ext_nuprli_uniquely_valued_eqas in eqas; try exact q0; auto; simpl in *; eauto 3 with slow;[].
        eapply @type_family_ext_nuprli_uniquely_valued_eqbs in eqbs; try exact q0; auto; simpl in *; eauto 3 with slow;[].

        pose proof (eqas _ (lib_extends_refl _)) as eqas; simpl in *.

        assert (raise_ext_per (Feqa lib' ext lib'0 xtb z) e lib'1 (lib_extends_refl lib'1) a a') as eqa1.
        { unfold raise_ext_per; simpl.
          eapply lib_per_cond; eauto. }
        assert (raise_ext_per (Feqa lib1 ext1 lib2 ext2 extz) z0 lib'1 (lib_extends_refl lib'1) a a') as eqa2.
        { unfold raise_ext_per; simpl.
          apply eqas.
          eapply lib_per_cond; eauto. }

        pose proof (eqbs _ (lib_extends_refl _) a a' eqa1 eqa2) as eqbs; simpl in *.

        unfold raise_ext_per_fam in eqbs; simpl in *.
        eapply lib_per_fam_cond; apply eqbs; eapply lib_per_fam_cond; eauto.
    }
  }

  {
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    unfold type_family_ext in q0; exrepnd.
    repeat ccomputes_to_valc_ext_val.

    pose proof (q4 _ (lib_extends_refl lib'0)) as q4; simpl in *.
    eapply nuprli_value_respecting_left in q4;[|apply ccequivc_ext_sym;eauto].
    eapply nuprli_value_respecting_right in q4;[|apply ccequivc_ext_sym;eauto].
    eapply nuprli_type_extensionality;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      pose proof (u6 _ z0) as u6; simpl in *.
      apply nuprli_refl in u6.
      apply nuprli_refl in q4.
      eapply nuprli_value_respecting_left in u6;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprli_value_respecting_right in u6;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprli_uniquely_valued in u6; try exact q4.
      apply u6; auto.
  }

  {
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv; simpl.
    pose proof (u2 _ ext _ xtb z) as q; simpl in q; repnd.
    unfold type_family_ext in q0; exrepnd.
    repeat ccomputes_to_valc_ext_val.

    assert ((Feqa lib' ext lib'0 xtb z) lib'0 (lib_extends_refl lib'0) a a') as e1.
    { simpl in *; exrepnd; eapply cond; eauto. }

    pose proof (q0 _ (lib_extends_refl lib'0) a a' e1) as q0; simpl in *.
    eapply nuprli_value_respecting_left in q0;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto].
    eapply nuprli_value_respecting_right in q0;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto].

    eapply nuprli_type_extensionality;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0).
      eapply lib_per_fam_cond; eauto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      assert ((Feqa lib1 ext1 lib2 ext2 extz) lib'0 z0 a a') as eb.
      { simpl in *; exrepnd; eapply cond; eauto. }

      pose proof (u1 _ z0 a a' eb) as u1; simpl in *.
      eapply nuprli_value_respecting_left in u1;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto] ]; auto;[].
      eapply nuprli_value_respecting_right in u1;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;apply bcequivc_ext_implies_ccequivc_ext;eauto] ]; auto;[].
      apply nuprli_refl in u1.
      apply nuprli_refl in q0.
      eapply nuprli_uniquely_valued in u1; try exact q0.
      apply u1; auto; eapply lib_per_fam_cond; eauto.
  }

  {
    destruct uk; simpl; auto;[].
    dands; introv ext; simpl in *; exrepnd;
      pose proof (u2 _ ext1 _ ext2 extz) as u2; simpl in u2; repnd;
        unfold type_family_ext in *; simpl in *; exrepnd;
          repeat ccomputes_to_valc_ext_val; eauto 3 with slow.
  }
Qed.



Lemma per_bar_eq_per_product_eq_bar_lib_per_iff {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) p1 p2,
    (per_bar_eq lib (per_product_eq_bar_lib_per lib eqa eqb) p1 p2)
      <=>
      in_open_bar_ext
          lib
          (fun lib' x => per_product_eq lib' (eqa lib' x) (eqb lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; simpl in *.
    unfold per_product_eq_bar in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; simpl in *.
    introv.
    eapply implies_eq_term_equals_per_product_eq; try exact h; introv;
      try (apply lib_per_cond);
      try (apply lib_per_fam_cond).

  - eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; simpl in *.
    unfold per_product_eq_bar.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; simpl in *.
    introv.
    eapply implies_eq_term_equals_per_product_eq; try exact h; introv;
      try (apply lib_per_cond);
      try (apply lib_per_fam_cond).
Qed.

Lemma equality_in_product {o} :
  forall uk lib (p1 p2 : @CTerm o) A v B,
    equality uk lib p1 p2 (mkc_product A v B)
    <=>
    (type uk lib A
     # equality_swap_invariant_cond uk lib A v B v B
     # in_ext
         lib
         (fun lib' => forall a a',
              equality uk lib' a a' A
              -> tequality uk lib' (substc a v B) (substc a' v B))
     # in_open_bar
         lib
         (fun lib =>
            {a1, a2, b1, b2 : CTerm
            , p1 ===>(lib) (mkc_pair a1 b1)
            # p2 ===>(lib) (mkc_pair a2 b2)
            # equality uk lib a1 a2 A
            # equality uk lib b1 b2 (substc a1 v B)})).
Proof.
  introv; split; intro e; exrepnd.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_product2 in e1; exrepnd.
    apply e2 in e0.
    clear dependent eq.
    dands; eauto 3 with slow.

    {
      introv x ea.

      exists (per_bar_eq lib' (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
      apply CL_bar.
      exists (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].

      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e0.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e4.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e3.

      apply in_open_bar_ext_twice in e3.
      apply in_open_bar_ext_twice in e4.
      apply in_open_bar_ext_dup.
      eapply in_open_bar_ext_comb; try exact e0; clear e0.
      eapply in_open_bar_ext_comb; try exact e3; clear e3.
      eapply in_open_bar_ext_pres; try exact e4; clear e4; introv m4 m3 m0; simpl in *.
      unfold raise_ext_per_fam.
      unfold per_product_eq_bar in m0; simpl in m0.

      eapply in_open_bar_ext_comb; try exact m0; clear m0.
      eapply in_open_bar_ext_comb; try exact m3; clear m3.
      eapply in_open_bar_ext_pres; try exact m4; clear m4; introv m4 m3 m0; simpl in *.
      unfold per_product_eq, raise_ext_per, raise_ext_per_fam in *; exrepnd.
      introv.

      assert (eqa lib'1 (lib_extends_trans (lib_extends_trans e0 e) x) a a') as eea.
      {
        pose proof (equality_eq1 uk lib'1 A A a a' (eqa lib'1 (lib_extends_trans (lib_extends_trans e0 e) x))) as w.
        apply w; auto; eauto 4 with slow.
      }

      assert (eqa lib'1 (lib_extends_trans e0 (lib_extends_trans e x)) a a') as eeb.
      { eapply lib_per_cond; eauto. }

      assert (eqa lib'1 (lib_extends_trans z x) a a') as eec.
      { eapply lib_per_cond; eauto. }

      pose proof (m4 _ _ eea) as m4.
      fold (@nuprl o).

      eapply type_extensionality_nuprl;[eauto|].
      introv; split; intro w; eauto;[|exrepnd; eapply lib_per_fam_cond; eauto].
      exists eec; eapply lib_per_fam_cond; eauto.
    }

    {
      apply per_bar_eq_per_product_eq_bar_lib_per_iff in e0; exrepnd.
      unfold per_product_eq in e0.
      eapply in_open_bar_comb2; try exact e3; clear e3.
      eapply in_open_bar_ext_comb; try exact e4; clear e4.
      eapply in_open_bar_ext_pres; try exact e0; clear e0; introv e0 e4 e3.
      exrepnd.
      exists a a' b b'; dands; auto.

      - eapply (equality_eq1 uk lib' A A a a' (eqa lib' e)); auto.

      - pose proof (e4 _ _ e2) as e4; simpl in *.
        apply (equality_eq1 uk lib' (substc a v B) (substc a' v B) b b' (eqb lib' e a a' e2)); auto.
    }

  - unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    pose proof (nuprl_monotone_func uk lib A A eqa e3) as tya; exrepnd.
    rename eq' into eqa'.

    eapply choice_ext_lib_teq_fam in e2;[|apply tya0].
    exrepnd.

    exists (per_product_eq_bar lib eqa' eqb).
    dands;[|].

    {
      apply CL_product.
      exists eqa' eqb.
      dands; auto;[].
      exists A A v v B B; dands; spcast; eauto 3 with slow;
        try (complete (fold (@nuprl o) in *; introv; apply tya0));
        try (complete (eapply equality_swap_invariant_cond_nuprl_imp; eauto; introv; apply tya0)).
    }

    unfold per_product_eq_bar.
    eapply in_open_bar_ext_comb2; eauto; clear e.
    apply in_ext_ext_implies_in_open_bar_ext; introv h; exrepnd.

    pose proof (tya0 _ e) as tya0; repnd.
    dup h3 as ea.
    apply (equality_eq1 uk lib' A A a1 a2 (eqa' lib' e)) in ea; auto.
    pose proof (e0 _ e _ _ ea) as e0.
    exists a1 a2 b1 b2 ea; dands; auto.
    eapply equality_eq1; eauto.
Qed.

Lemma equality_in_prod {p} :
  forall uk lib (p1 p2 A B : @CTerm p),
    equality uk lib p1 p2 (mkc_prod A B)
    <=>
    (type uk lib A
     # in_ext lib (fun lib => inhabited_type uk lib A -> type uk lib B)
     # in_open_bar
         lib
         (fun lib =>
            {a1, a2, b1, b2 : CTerm
            , p1 ===>(lib) (mkc_pair a1 b1)
            # p2 ===>(lib) (mkc_pair a2 b2)
            # equality uk lib a1 a2 A
            # equality uk lib b1 b2 B})).
Proof.
  introv.
  rw <- @fold_mkc_prod.
  rw @equality_in_product.
  split; intro k; exrepnd; dands; auto; eauto 3 with slow;[| | |].

  {
    introv e i.
    unfold inhabited_type in i; exrepnd.
    pose proof (k2 _ e _ _ i0) as q.
    repeat (rw @csubst_mk_cv in q); sp.
  }

  {
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
    introv e k; exrepnd.
    exists a1 a2 b1 b2; dands; auto.
    allrw @csubst_mk_cv; sp.
  }

  {
    introv e ea.
    repeat (rw @csubst_mk_cv).
    apply k1; eauto 3 with slow.
  }

  {
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
    introv e k; exrepnd.
    exists a1 a2 b1 b2; dands; auto.
    repeat (rw @csubst_mk_cv); sp.
  }
Qed.

Lemma tequality_product {o} :
  forall uk lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    tequality uk lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2)
    <=>
    (tequality uk lib A1 A2
     # equality_swap_invariant_cond uk lib A1 v1 B1 v2 B2
     # in_ext lib (fun lib => forall a a', equality uk lib a a' A1 -> tequality uk lib (substc a v1 B1) (substc a' v2 B2))).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality in teq; exrepnd.
    apply dest_nuprl_product2 in teq0; exrepnd.
    dands; eauto 3 with slow;[].

    introv x ea.

    exists (per_bar_eq lib' (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    apply CL_bar.
    exists (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].

    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq2.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq3.
    eapply in_open_bar_ext_comb; try exact teq2; clear teq2.
    eapply in_open_bar_ext_pres; try exact teq3; clear teq3; introv teq3 teq2; simpl in *.
    fold (@nuprl o).

    assert (eqa lib'0 (lib_extends_trans e x) a a') as xx.
    {
      pose proof (equality_eq1 uk lib'0 A1 A2 a a' (eqa lib'0 (lib_extends_trans e x))) as w.
      apply w; auto; eauto 3 with slow.
    }

    pose proof (teq3 _ _ xx) as teq3; simpl in *.

    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[].
    exrepnd.
    unfold raise_ext_per, raise_ext_per_fam in *.
    eapply lib_per_fam_cond; eauto.

  - Case "<-".
    introv e; exrepnd.

    assert (forall lib', lib_extends lib' lib -> tequality uk lib' A1 A2) as teqa by eauto 3 with slow.
    clear e0.

    rename e into teqb.

    unfold tequality in *.

    apply choice_ext_lib_teq in teqa; exrepnd.
    eapply choice_ext_lib_teq_fam in teqb;[|eauto]; exrepnd.

    exists (per_product_eq_bar lib eqa eqb).
    apply CL_product.
    exists eqa eqb.
    dands; eauto 3 with slow.
    exists A1 A2 v1 v2 B1 B2.
    dands; spcast; eauto 3 with slow;
      try (complete (eapply equality_swap_invariant_cond_nuprl_imp; eauto;
                     introv; apply teqa0)).
Qed.

Lemma equality_product {o} :
  forall uk lib (A1 A2 : @CTerm o) v1 v2 B1 B2 i,
    equality uk lib (mkc_product A1 v1 B1)
             (mkc_product A2 v2 B2)
             (mkc_uni uk i)
    <=>
    (equality uk lib A1 A2 (mkc_uni uk i)
     # equality_swap_invariant_cond uk lib A1 v1 B1 v2 B2
     # in_ext lib (fun lib => forall a a', equality uk lib a a' A1 -> equality uk lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni uk i))).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    dands; eauto 3 with slow.

    {
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq2 in teq0.

      exists eq.
      dands; auto.
      apply teq2.

      clear dependent eq.
      eapply in_open_bar_ext_pres; try exact teq0; clear teq0; introv teq0; simpl in *.
      unfold univi_eq in *; exrepnd.

      unfold univi_eq in *.
      exrepnd.
      apply dest_nuprli_product2 in teq1; exrepnd.
      exists (per_bar_eq lib' eqa0).
      apply CL_bar; exists eqa0; dands; auto.
    }

    {
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq2 in teq0.
      unfold per_bar_eq in teq0; simpl in teq0.
      apply if_in_open_bar_equality_swap_invariant_cond.
      eapply in_open_bar_comb2; try exact teq0; clear teq0.
      apply in_ext_ext_implies_in_open_bar_ext; introv ext h.
      unfold univi_eq in *; exrepnd.
      apply dest_nuprli_product2 in h0; exrepnd; eauto 3 with slow.
    }

    {
      introv x ea.
      unfold equality in teq; exrepnd.
      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq2 in teq0.

      exists (per_bar_eq lib' (univi_eq_lib_per uk lib' i)).
      dands; auto; eauto 2 with slow.

      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq0.
      eapply in_open_bar_ext_pres; try exact teq0; clear teq0; introv teq0; simpl in *.
      unfold univi_eq in *.
      exrepnd.
      apply dest_nuprli_product2 in teq3; exrepnd.
      exists (per_bar_eq lib'0 (lib_per_fam2lib_per a a' eqb)).
      apply CL_bar; exists (lib_per_fam2lib_per a a' eqb); dands; tcsp;[]; simpl in *.
      fold (@nuprli o i) in *.

      eapply in_open_bar_ext_comb; try exact teq4; clear teq4.
      eapply in_open_bar_ext_pres; try exact teq5; clear teq5; introv teq4 teq5.

      assert (eqa0 lib'1 e0 a a') as xx.
      {
        pose proof (equality_eq1 uk lib'1 A1 A2 a a' (eqa0 lib'1 e0)) as w.
        apply w; auto; eauto 4 with slow.
      }

      pose proof (teq4 _ _ xx) as teq4; simpl in *.

      eapply nuprli_type_extensionality;[eauto|].
      introv; split; intro w; eauto;[].
      exrepnd.
      unfold raise_ext_per, raise_ext_per_fam in *.
      eapply lib_per_fam_cond; eauto.
    }

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.

    applydup @dest_nuprl_uni in eqa1.
    apply univ_implies_univi_bar3 in eqa2; exrepnd.
    apply eqa2 in eqa0.

    exists eq; dands; auto.
    apply eqa2.
    clear dependent eq.

    eapply in_open_bar_ext_pres; try exact eqa0; clear eqa0; introv eqa0; simpl in *.
    unfold univi_eq in *; exrepnd.
    fold (@nuprli o i) in *.

    pose proof (nuprli_monotone_func i uk lib' A1 A2 eqa eqa1) as tya; exrepnd.
    rename eq' into eqa'.

    assert (forall lib'',
               lib_extends lib'' lib' ->
               forall a a',
                 equality uk lib'' a a' A1 ->
                 equality uk lib'' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']] (mkc_uni uk i)) as teq.
    { introv xt ea; eapply eqb; eauto 3 with slow. }
    clear eqb.

    eapply choice_ext_teqi in teq;[|introv;eapply nuprli_implies_nuprl;eapply tya0];[].
    exrepnd.
    rename eqb into eqb'.

    exists (per_product_eq_bar lib' eqa' eqb').
    apply CL_product; fold (@nuprli o i).
    exists eqa' eqb'.
    dands; auto;[].
    exists A1 A2 v1 v2 B1 B2; dands; spcast; eauto 3 with slow;
      try (complete (introv; apply tya0));
      try (complete (eapply lib_extends_preserves_equality_swap_invariant_cond in eqb0; eauto;
                     eapply equality_swap_invariant_cond_nuprli_imp; eauto;
                     introv; apply tya0)).
Qed.

Lemma equality_product_uk0 {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2 i,
    equality uk0 lib (mkc_product A1 v1 B1)
             (mkc_product A2 v2 B2)
             (mkc_uni uk0 i)
    <=>
    (equality uk0 lib A1 A2 (mkc_uni uk0 i)
     # in_ext lib (fun lib => forall a a', equality uk0 lib a a' A1 -> equality uk0 lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni uk0 i))).
Proof.
  introv.
  rw (@equality_product o uk0).
  split; intro h; repnd; dands; eauto 2 with slow.
Qed.

Lemma tequality_mkc_prod {p} :
  forall uk lib (A1 A2 B1 B2 : @CTerm p),
    tequality uk lib (mkc_prod A1 B1) (mkc_prod A2 B2)
    <=> (tequality uk lib A1 A2
         # in_ext lib (fun lib => inhabited_type uk lib A1 -> tequality uk lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_prod.
  rw (@tequality_product p uk).
  split; intro k; repnd; dands; auto; eauto 3 with slow.

  {
    introv x i.
    unfold inhabited_type in i; exrepnd.
    generalize (k _ x t t i0); intro teq.
    allrw @csubst_mk_cv; auto.
  }

  {
    introv x e.
    allrw @csubst_mk_cv; auto.
    apply equality_refl in e.
    eapply k; eauto 3 with slow.
  }
Qed.

Lemma type_mkc_prod {p} :
  forall uk lib (A B : @CTerm p),
    type uk lib (mkc_prod A B)
    <=> (type uk lib A
         # in_ext lib (fun lib => inhabited_type uk lib A -> type uk lib B)).
Proof.
  introv.
  rw @tequality_mkc_prod; sp.
Qed.

Lemma inhabited_product {p} :
  forall uk lib (A : @CTerm p) v B,
    inhabited_type uk lib (mkc_product A v B)
    <=>
    (type uk lib A
     # equality_swap_invariant_cond uk lib A v B v B
     # in_ext lib (fun lib => forall a a', equality uk lib a a' A -> tequality uk lib (substc a v B) (substc a' v B))
     # {t : CTerm
       , in_open_bar
           lib
           (fun lib =>
              {a , b : CTerm
              , t ===>(lib) (mkc_pair a b)
              # member uk lib a A
              # member uk lib b (substc a v B)})}).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_product in k0; exrepnd; dands; tcsp.
    exists t.
    eapply all_in_ex_bar_modus_ponens1;[|exact k0]; clear k0.
    introv e k; exrepnd.
    exists a1 b1; dands; auto; eauto 3 with slow; eapply equality_refl; eauto.

  - exrepnd.
    allunfold @inhabited_type; exrepnd.
    exists t.
    rw @equality_in_product; dands; tcsp.
    eapply all_in_ex_bar_modus_ponens1;[|exact k3]; clear k3.
    introv e k; exrepnd.
    exists a a b b; dands; auto; eauto 3 with slow.
Qed.

Lemma inhabited_exists {p} :
  forall uk lib (A : @CTerm p) v B,
    inhabited_type uk lib (mkc_exists A v B)
    <=>
    (type uk lib A
     # equality_swap_invariant_cond uk lib A v B v B
     # in_ext lib (fun lib => forall a a', equality uk lib a a' A -> tequality uk lib (substc a v B) (substc a' v B))
     # {t : CTerm
       , in_open_bar
           lib
           (fun lib =>
              {a , b : CTerm
              , t ===>(lib) (mkc_pair a b)
              # member uk lib a A
              # member uk lib b (substc a v B)})}).
Proof.
  introv.
  unfold mkc_exists.
  rw @inhabited_product; tcsp.
Qed.

Lemma alphaeqc_mkc_product1 {o} :
  forall (a b : @CTerm o) v t,
    alphaeqc a b
    -> alphaeqc (mkc_product a v t) (mkc_product b v t).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  unfold mk_product.
  repeat prove_alpha_eq4.
Qed.

Lemma member_product2 {o} :
  forall uk lib (p : @CTerm o) A v B,
    member uk lib p (mkc_product A v B)
    <=>
    (type uk lib (mkc_product A v B)
     # equality_swap_invariant_cond uk lib A v B v B
     # in_open_bar
         lib
         (fun lib =>
            {a , b : CTerm
            , p ===>(lib) (mkc_pair a b)
            # member uk lib a A
            # member uk lib b (substc a v B)})).
Proof.
  introv.
  rw @equality_in_product; split; intro k; exrepnd.

  - dands; eauto 3 with slow.

    + apply tequality_product; auto.

    + eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
      introv e k; exrepnd.
      exists a1 b1; dands; auto; eauto 3 with slow; eapply equality_refl; eauto.

  - apply @tequality_product in k0; repnd.
    dands; eauto 3 with slow.
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
    introv e k; exrepnd.
    exists a a b b; dands; auto.
Qed.

Lemma inhabited_prod {p} :
  forall uk lib (A B : @CTerm p),
    inhabited_type_bar uk lib (mkc_prod A B)
    <=>
    (type uk lib A
     # type uk lib B
     # inhabited_type_bar uk lib A
     # inhabited_type_bar uk lib B).
Proof.
  introv.
  split; intro k; exrepnd.

  - unfold inhabited_type_bar, inhabited_type in k.
    dands; eauto 3 with slow.

    {
      apply all_in_ex_bar_type_implies_type.
      eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
      introv e k; exrepnd.
      apply equality_in_prod in k0; repnd; auto.
    }

    {
      apply all_in_ex_bar_type_implies_type.
      eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
      introv e k; exrepnd.
      apply equality_in_prod in k0; repnd; auto.
      apply all_in_ex_bar_type_implies_type.
      eapply all_in_ex_bar_modus_ponens1;[|exact k0]; clear k0.
      introv x k; exrepnd.
      apply k2; eauto 3 with slow.
    }

    {
      apply collapse_all_in_ex_bar.
      eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
      introv e k; exrepnd.
      apply equality_in_prod in k0; repnd; auto.
      eapply all_in_ex_bar_modus_ponens1;[|exact k0]; clear k0.
      introv x k; exrepnd.
      exists a1; eapply equality_refl; eauto.
    }

    {
      apply collapse_all_in_ex_bar.
      eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k.
      introv e k; exrepnd.
      apply equality_in_prod in k0; repnd; auto.
      eapply all_in_ex_bar_modus_ponens1;[|exact k0]; clear k0.
      introv x k; exrepnd.
      exists b1; eapply equality_refl; eauto.
    }

  - unfold inhabited_type_bar in *; exrepnd.
    eapply in_open_bar_comb; try exact k; clear k.
    eapply in_open_bar_pres; try exact k2; clear k2; introv ext k2 k.

    unfold inhabited_type in *; exrepnd.
    exists (mkc_pair t0 t).
    apply equality_in_prod; dands; eauto 3 with slow.

    { introv e inh; eapply inhabited_implies_tequality; eauto 3 with slow. }

    { apply in_ext_implies_in_open_bar; introv xt.
      exists t0 t0 t t; dands; spcast; eauto 3 with slow. }
Qed.

Lemma inhabited_prod2 {p} :
  forall uk lib (A B : @CTerm p),
    inhabited_type_bar uk lib (mkc_prod A B)
    <=>
    (type uk lib A
     # inhabited_type_bar uk lib A
     # type uk lib B
     # inhabited_type_bar uk lib B).
Proof.
  introv.
  rw @inhabited_prod; split; sp.
Qed.
