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


Require Export per_props_fam.
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

  unfold type_family_ext in *; exrepnd; spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_product_eq_bar.

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprl_refl in pera4.
    apply nuprl_refl in perb4.
    eapply nuprl_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v) as perb0.
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
  forall (ts : cts(o)) lib T A v B T' eq,
    ts = univ
    -> computes_to_valc lib T (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_bar (per_product_bar (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_product {o} :
  forall (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprl lib (mkc_product A v B) (mkc_product C w D) eq
    -> per_bar (per_product_bar nuprl) lib (mkc_product A v B) (mkc_product C w D) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_product_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma type_family_ext_nuprl_product_uniquely_valued_eqas {o} :
  forall lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_product nuprl lib (mkc_product A v B) (mkc_product C w D) eqa1 eqb1
    -> type_family_ext mkc_product nuprl lib (mkc_product A v B) (mkc_product C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  repeat computes_to_eqval.
  introv.
  pose proof (tfa3 _ e) as tfa3.
  pose proof (tfb3 _ e) as tfb3.
  simpl in *.
  apply nuprl_refl in tfa3.
  apply nuprl_refl in tfb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.

Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa {o} :
  forall {lib lib'} {bar : @BarLib o lib} {feqa : bar-and-fam-per(lib,bar,o)}
         {A v B C w D}
         (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product nuprl lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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
  eapply type_family_ext_nuprl_product_uniquely_valued_eqas in q1; try exact q2.
  simpl in *.
  pose proof (q1 _ (lib_extends_refl lib')) as q1; simpl in *.
  apply q1; auto.
Qed.

Definition bar_and_fam_per2lib_per_fam {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o))
           {A v B C w D}
           (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product nuprl lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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
                (bar_and_fam_per2lib_per_implies_lpaf_eqa F lib1 br ext y e)
                t1 t2}}}}).

  repeat introv.
  split; introv h; exrepnd.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
  - exists lib1 br ext y0; auto.
    eapply (lib_per_fam_cond _  (lpaf_eqb (feqa lib1 br lib' ext y0))); eauto.
Defined.

Lemma dest_nuprl_product2 {o} :
  forall lib (eq : per(o)) A v B C w D,
    nuprl lib (mkc_product A v B) (mkc_product C w D) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq bar (per_product_eq_bar_lib_per lib eqa eqb))
      # all_in_bar_ext bar (fun lib' x => nuprl lib' A C (eqa lib' x))
      # all_in_bar_ext bar (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprl lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e)).
Proof.
  introv u.
  apply dest_nuprl_product in u.
  unfold per_bar in u; exrepnd.

  apply all_in_bar_ext_exists_per_and_fam_implies_exists in u0; exrepnd.

  assert (forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product nuprl lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x))) as F by eapply u2.

  exists bar.
  exists (bar_and_fam_per2lib_per feqa).
  exists (bar_and_fam_per2lib_per_fam feqa F).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (u2 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eqa.

    introv; simpl.
    apply implies_eq_term_equals_per_product_eq_bar.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u3 _ e) as u3; simpl in *.

        pose proof (F lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q3 _ (lib_extends_refl lib'1)) as q3; simpl in *.
        apply nuprl_refl in q3.
        apply nuprl_refl in u3.
        eapply nuprl_uniquely_valued in q3; try exact u3.
        apply q3; auto.

      - exrepnd.
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u3 _ e) as u3; simpl in *.

        pose proof (F lib1 br0 _ ext0 x0) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q3 _ (lib_extends_refl lib'1)) as q3; simpl in *.
        apply nuprl_refl in q3.
        apply nuprl_refl in u3.
        eapply nuprl_uniquely_valued in q3; try exact u3.
        apply q3; auto.
    }

    {
      repeat introv; simpl; unfold raise_ext_per_fam; simpl.
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u0 _ e a a' u) as u0; simpl in *.

        pose proof (F lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q1 _ (lib_extends_refl lib'1) a a') as q1; simpl in *.
        remember (bar_and_fam_per2lib_per_implies_lpaf_eqa F lib' br  (lib_extends_trans e ext) (lib_extends_trans e x) v0) as xxx.
        pose proof (q1 xxx) as q1; simpl in *.
        subst.

        apply nuprl_refl in q1.
        apply nuprl_refl in u0.
        eapply nuprl_uniquely_valued in q1; try exact u0.
        apply q1; auto.

      - exrepnd.
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u0 _ e a a' u) as u0; simpl in *.

        pose proof (F lib1 br0 _ ext0 y) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q1 _ (lib_extends_refl lib'1) a a') as q1; simpl in *.
        remember (bar_and_fam_per2lib_per_implies_lpaf_eqa F lib1 br0 ext0 y v0) as xxx.
        pose proof (q1 xxx) as q1; simpl in *.
        subst.

        apply nuprl_refl in q1.
        apply nuprl_refl in u0.
        eapply nuprl_uniquely_valued in q1; try exact u0.
        apply q1; auto.
    }
  }

  {
    clear F.
    introv br ext; introv.
    pose proof (u2 _ br _ ext x) as h; simpl in *; repnd.
    clear h.
    unfold type_family_ext in h0; exrepnd.
    computes_to_value_isvalue.
    pose proof (h3 _ (lib_extends_refl lib'0)) as h3; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (u2 _ br0 _ ext0 x0) as u2; repnd.
      clear u2.
      unfold type_family_ext in u0; exrepnd.
      computes_to_value_isvalue.
      pose proof (u4 _ (lib_extends_refl lib'0)) as u4; simpl in *.
      apply nuprl_refl in u4.
      apply nuprl_refl in h3.
      eapply nuprl_uniquely_valued in u4; try exact h3.
      apply u4; auto.
  }

  {
    introv br ext; introv.
    simpl in *; exrepnd.
    pose proof (u2 _ br0 _ ext0 x0) as h; simpl in *; repnd.
    clear h.
    unfold type_family_ext in h0; exrepnd.
    computes_to_value_isvalue.
    pose proof (h0 _ (lib_extends_refl lib'0) a a' e1) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].

    split; intro h.

    - exists lib1 br0 ext0 x0; simpl.
      eapply (lib_per_fam_cond _ (lpaf_eqb (feqa lib1 br0 lib'0 ext0 x0))); eauto.

    - exrepnd.
      pose proof (u2 _ br1 _ ext1 y) as u2; repnd.
      clear u2.
      unfold type_family_ext in u0; exrepnd.
      computes_to_value_isvalue.
      remember (bar_and_fam_per2lib_per_implies_lpaf_eqa F lib0 br1 ext1 y (ex_intro _ lib1 (ex_intro _ br0 (ex_intro _ ext0 (ex_intro _ x0 e1))))) as xxx.
      pose proof (u0 _ (lib_extends_refl lib'0) a a' xxx) as u0; simpl in *.
      subst.
      apply nuprl_refl in u0.
      apply nuprl_refl in h0.
      eapply nuprl_uniquely_valued in u0; try exact h0.
      apply u0; auto.
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

  unfold type_family_ext in *; exrepnd; spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_product_eq_bar.

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprli_refl in pera4.
    apply nuprli_refl in perb4.
    eapply nuprli_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v) as perb0.
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
  forall i (ts : cts(o)) lib T A v B T' eq,
    ts = univi_bar i
    -> computes_to_valc lib T (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_bar (per_product_bar (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar_nuprli; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_product {o} :
  forall i (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprli i lib (mkc_product A v B) (mkc_product C w D) eq
    -> per_bar (per_product_bar (nuprli i)) lib (mkc_product A v B) (mkc_product C w D) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_product_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma type_family_ext_nuprli_product_uniquely_valued_eqas {o} :
  forall i lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_product (nuprli i) lib (mkc_product A v B) (mkc_product C w D) eqa1 eqb1
    -> type_family_ext mkc_product (nuprli i) lib (mkc_product A v B) (mkc_product C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  repeat computes_to_eqval.
  introv.
  pose proof (tfa3 _ e) as tfa3.
  pose proof (tfb3 _ e) as tfb3.
  simpl in *.
  apply nuprli_refl in tfa3.
  apply nuprli_refl in tfb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.

Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa_i {o} :
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
Qed.

Definition bar_and_fam_per2lib_per_fam_i {o}
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
Defined.

Lemma dest_nuprli_product2 {o} :
  forall i lib (eq : per(o)) A v B C w D,
    nuprli i lib (mkc_product A v B) (mkc_product C w D) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq bar (per_product_eq_bar_lib_per lib eqa eqb))
      # all_in_bar_ext bar (fun lib' x => nuprli i lib' A C (eqa lib' x))
      # all_in_bar_ext bar (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprli i lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e)).
Proof.
  introv u.
  apply dest_nuprli_product in u.
  unfold per_bar in u; exrepnd.

  apply all_in_bar_ext_exists_per_and_fam_implies_exists in u0; exrepnd.

  assert (forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_product (nuprli i) lib2 (mkc_product A v B) (mkc_product C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x))) as F by eapply u2.

  exists bar.
  exists (bar_and_fam_per2lib_per feqa).
  exists (bar_and_fam_per2lib_per_fam_i feqa F).

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq.
    apply all_in_bar_ext_intersect_bars_same.
    introv br ext; introv.
    pose proof (u2 _ br _ ext x) as u2; repnd.
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eqa.

    introv; simpl.
    apply implies_eq_term_equals_per_product_eq_bar.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u3 _ e) as u3; simpl in *.

        pose proof (F lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q3 _ (lib_extends_refl lib'1)) as q3; simpl in *.
        apply nuprli_refl in q3.
        apply nuprli_refl in u3.
        eapply nuprli_uniquely_valued in q3; try exact u3.
        apply q3; auto.

      - exrepnd.
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u3 _ e) as u3; simpl in *.

        pose proof (F lib1 br0 _ ext0 x0) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q3 _ (lib_extends_refl lib'1)) as q3; simpl in *.
        apply nuprli_refl in q3.
        apply nuprli_refl in u3.
        eapply nuprli_uniquely_valued in q3; try exact u3.
        apply q3; auto.
    }

    {
      repeat introv; simpl; unfold raise_ext_per_fam; simpl.
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u0 _ e a a' u) as u0; simpl in *.

        pose proof (F lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q1 _ (lib_extends_refl lib'1) a a') as q1; simpl in *.
        remember (bar_and_fam_per2lib_per_implies_lpaf_eqa_i F lib' br  (lib_extends_trans e ext) (lib_extends_trans e x) v0) as xxx.
        pose proof (q1 xxx) as q1; simpl in *.
        subst.

        apply nuprli_refl in q1.
        apply nuprli_refl in u0.
        eapply nuprli_uniquely_valued in q1; try exact u0.
        apply q1; auto.

      - exrepnd.
        unfold type_family_ext in u0; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (u0 _ e a a' u) as u0; simpl in *.

        pose proof (F lib1 br0 _ ext0 y) as q.
        unfold type_family_ext in q; exrepnd; spcast.
        computes_to_value_isvalue.
        pose proof (q1 _ (lib_extends_refl lib'1) a a') as q1; simpl in *.
        remember (bar_and_fam_per2lib_per_implies_lpaf_eqa_i F lib1 br0 ext0 y v0) as xxx.
        pose proof (q1 xxx) as q1; simpl in *.
        subst.

        apply nuprli_refl in q1.
        apply nuprli_refl in u0.
        eapply nuprli_uniquely_valued in q1; try exact u0.
        apply q1; auto.
    }
  }

  {
    clear F.
    introv br ext; introv.
    pose proof (u2 _ br _ ext x) as h; simpl in *; repnd.
    clear h.
    unfold type_family_ext in h0; exrepnd.
    computes_to_value_isvalue.
    pose proof (h3 _ (lib_extends_refl lib'0)) as h3; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (u2 _ br0 _ ext0 x0) as u2; repnd.
      clear u2.
      unfold type_family_ext in u0; exrepnd.
      computes_to_value_isvalue.
      pose proof (u4 _ (lib_extends_refl lib'0)) as u4; simpl in *.
      apply nuprli_refl in u4.
      apply nuprli_refl in h3.
      eapply nuprli_uniquely_valued in u4; try exact h3.
      apply u4; auto.
  }

  {
    introv br ext; introv.
    simpl in *; exrepnd.
    pose proof (u2 _ br0 _ ext0 x0) as h; simpl in *; repnd.
    clear h.
    unfold type_family_ext in h0; exrepnd.
    computes_to_value_isvalue.
    pose proof (h0 _ (lib_extends_refl lib'0) a a' e1) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].

    split; intro h.

    - exists lib1 br0 ext0 x0; simpl.
      eapply (lib_per_fam_cond _ (lpaf_eqb (feqa lib1 br0 lib'0 ext0 x0))); eauto.

    - exrepnd.
      pose proof (u2 _ br1 _ ext1 y) as u2; repnd.
      clear u2.
      unfold type_family_ext in u0; exrepnd.
      computes_to_value_isvalue.
      remember (bar_and_fam_per2lib_per_implies_lpaf_eqa_i F lib0 br1 ext1 y (ex_intro _ lib1 (ex_intro _ br0 (ex_intro _ ext0 (ex_intro _ x0 e1))))) as xxx.
      pose proof (u0 _ (lib_extends_refl lib'0) a a' xxx) as u0; simpl in *.
      subst.
      apply nuprli_refl in u0.
      apply nuprli_refl in h0.
      eapply nuprli_uniquely_valued in u0; try exact h0.
      apply u0; auto.
  }
Qed.



Lemma per_bar_eq_per_product_eq_bar_lib_per_iff {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) p1 p2,
    (per_bar_eq bar (per_product_eq_bar_lib_per lib eqa eqb) p1 p2)
      <=>
      exists bar,
        all_in_bar_ext
          bar
          (fun lib' x => per_product_eq lib' (eqa lib' x) (eqb lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_product_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    unfold per_bar_eq in *; simpl in *.
    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.

    apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_product_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.
    unfold per_product_eq_bar in h0; exrepnd.
    exists bar0; simpl in *.
    unfold raise_ext_per_fam in *; simpl in *.
    unfold raise_ext_per in *.

    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
    eapply implies_eq_term_equals_per_product_eq; try exact h1;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).

  - unfold per_bar_eq; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x).
    introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h0 _ br'1 lib'3 (lib_extends_trans (lib_extends_trans e ext') br'2) (lib_extends_trans (lib_extends_trans e x0) x)) as h0; simpl in *.

    eapply implies_eq_term_equals_per_product_eq; try exact h0;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).
Qed.

Lemma equality_in_product {o} :
  forall lib (p1 p2 : @CTerm o) A v B,
    equality lib p1 p2 (mkc_product A v B)
    <=>
    (type lib A
     # in_ext
         lib
         (fun lib' => forall a a',
              equality lib' a a' A
              -> tequality lib' (substc a v B) (substc a' v B))
     # all_in_ex_bar
         lib
         (fun lib =>
            {a1, a2, b1, b2 : CTerm
            , p1 ===>(lib) (mkc_pair a1 b1)
            # p2 ===>(lib) (mkc_pair a2 b2)
            # equality lib a1 a2 A
            # equality lib b1 b2 (substc a1 v B)})).
Proof.
  introv; split; intro e; exrepnd.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_product2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.
    dands; eauto 3 with slow.

    {
      introv x ea.

      exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
      apply CL_bar.
      exists (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
      introv br ext; introv; simpl in *; exrepnd.
      fold (@nuprl o).
      pose proof (e3 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as e3; simpl in *.

      assert (eqa lib'1 (lib_extends_trans x0 x) a a') as xx.
      {
        pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans x0 x))) as w.
        apply w; auto; eauto 3 with slow.
      }

      pose proof (e2 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x) a a' xx) as e2; simpl in *.

      eapply type_extensionality_nuprl;[eauto|].
      introv; split; intro w; eauto;[].
      exrepnd.
      unfold raise_ext_per, raise_ext_per_fam in *.
      eapply lib_per_fam_cond; eauto.
    }

    {
      apply per_bar_eq_per_product_eq_bar_lib_per_iff in e0; exrepnd.
      unfold per_product_eq in e1.
      exists (intersect_bars bar bar0).
      introv br ext; simpl in *; exrepnd.
      assert (lib_extends lib'0 lib) as xt by eauto 4 with slow.
      pose proof (e1 _ br2 _ (lib_extends_trans ext br1) xt) as e1; simpl in *; exrepnd.
      eexists; eexists; eexists; eexists; dands; eauto.

      - pose proof (e3 _ br0 _ (lib_extends_trans ext br3) xt) as e3; simpl in *.
        apply (equality_eq1 lib'0 A A a a' (eqa lib'0 xt)) in e5; auto.

      - pose proof (e2 _ br0 _ (lib_extends_trans ext br3) xt a a' e5) as e2; simpl in *.
        apply (equality_eq1 lib'0 (substc a v B) (substc a' v B) b b' (eqb lib'0 xt a a' e)) in e0; auto.
        eapply type_extensionality_nuprl;[eauto|].
        apply lib_per_fam_cond.
    }

  - unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    pose proof (nuprl_monotone_func lib A A eqa e2) as tya; exrepnd.
    rename eq' into eqa'.

    eapply choice_ext_lib_teq_fam in e1;[|apply tya0].
    exrepnd.

    exists (per_product_eq_bar lib eqa' eqb).
    dands;[|].

    {
      apply CL_product.
      exists eqa' eqb.
      dands; auto;[].
      exists A A v v B B; dands; spcast; eauto 3 with slow;[].

      fold (@nuprl o) in *.
      introv; apply tya0.
    }

    unfold all_in_ex_bar in *; exrepnd.
    exists bar.
    introv br ext; introv.

    pose proof (e1 _ br _ ext) as e1; simpl in *; exrepnd.
    pose proof (tya0 _ x) as tya0; repnd.

    dup e5 as ea.
    apply (equality_eq1 lib'0 A A a1 a2 (eqa' lib'0 x)) in ea; auto.
    pose proof (e0 _ x _ _ ea) as e0.
    exists a1 a2 b1 b2 ea; dands; auto.
    eapply equality_eq1; eauto.
Qed.

Lemma equality_in_prod {p} :
  forall lib (p1 p2 A B : @CTerm p),
    equality lib p1 p2 (mkc_prod A B)
    <=>
    (type lib A
     # in_ext lib (fun lib => inhabited_type lib A -> type lib B)
     # all_in_ex_bar
         lib
         (fun lib =>
            {a1, a2, b1, b2 : CTerm
            , p1 ===>(lib) (mkc_pair a1 b1)
            # p2 ===>(lib) (mkc_pair a2 b2)
            # equality lib a1 a2 A
            # equality lib b1 b2 B})).
Proof.
  introv.
  rw <- @fold_mkc_prod.
  rw @equality_in_product.
  split; intro k; exrepnd; dands; auto;[| | |].

  {
    introv e i.
    unfold inhabited_type in i; exrepnd.
    pose proof (k1 _ e _ _ i0) as q.
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
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    tequality lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # in_ext lib (fun lib => forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2))).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality in teq; exrepnd.
    apply dest_nuprl_product2 in teq0; exrepnd.
    dands; eauto 3 with slow;[].

    introv x ea.

    exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    apply CL_bar.
    exists (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
    introv br ext; introv; simpl in *; exrepnd.
    fold (@nuprl o).
    pose proof (teq2 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as teq2; simpl in *.

    assert (lib_extends lib'1 lib') as xt by eauto 3 with slow.
    eapply equality_monotone in ea;[|exact xt].
    apply (equality_eq1 lib'1 A1 A2 a a' (eqa lib'1 (lib_extends_trans x0 x))) in ea; auto;[].

    pose proof (teq1 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x) a a' ea) as teq1; simpl in *.

    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[].
    exrepnd.
    unfold raise_ext_per, raise_ext_per_fam in *.
    eapply lib_per_fam_cond; eauto.

  - Case "<-".
    introv e; exrepnd.

    assert (forall lib', lib_extends lib' lib -> tequality lib' A1 A2) as teqa by eauto 3 with slow.
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
    dands; spcast; eauto 3 with slow.
Qed.

Lemma equality_product {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2 i,
    equality lib (mkc_product A1 v1 B1)
             (mkc_product A2 v2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # in_ext lib (fun lib => forall a a', equality lib a a' A1 -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i))).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    dands.

    {
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq3 in teq0.

      exists eq.
      dands; auto.
      apply teq3.

      clear dependent eq.

      introv br ext; introv.
      pose proof (teq0 _ br _ ext x) as teq0; simpl in *.
      unfold univi_eq in *.
      exrepnd.
      exists bar'.
      introv br' ext' x'.
      pose proof (teq1 _ br' _ ext' x') as teq1; simpl in *; exrepnd.
      fold (@nuprli o i) in *.

      apply dest_nuprli_product2 in teq0; exrepnd.
      exists (per_bar_eq bar0 eqa0).
      apply CL_bar; exists bar0 eqa0; dands; auto.
    }

    {
      introv x ea.
      unfold equality in teq; exrepnd.
      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq3 in teq0.

      exists (per_bar_eq (raise_bar bar x) (univi_eq_lib_per lib' i)).
      dands; auto; eauto 2 with slow.

      introv br ext; introv; simpl in *; exrepnd.
      pose proof (teq0 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as teq0; simpl in *.
      unfold univi_eq in *.
      exrepnd.
      exists bar'.
      introv br' ext' x'.
      pose proof (teq2 _ br' _ ext' x') as teq2; simpl in *; exrepnd.
      fold (@nuprli o i) in *.

      apply dest_nuprli_product2 in teq0; exrepnd.

      assert (lib_extends lib'3 lib) as xt by eauto 3 with slow.

      exists (per_bar_eq bar0 (lib_per_fam2lib_per a a' eqb)).
      apply CL_bar; exists bar0 (lib_per_fam2lib_per a a' eqb); dands; tcsp;[].
      introv br'' ext''; introv; simpl.
      fold (@nuprli o i) in *.
      pose proof (teq4 _ br'' _ ext'' x1) as teq4; simpl in *.

      assert (eqa0 lib'5 x1 a a') as xx.
      {
        pose proof (equality_eq1 lib'5 A1 A2 a a' (eqa0 lib'5 x1)) as w.
        apply w; auto; eauto 4 with slow.
      }

      pose proof (teq2 _ br'' _ ext'' x1 a a' xx) as teq2; simpl in *.

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
    apply eqa3 in eqa0.

    exists eq; dands; auto.
    apply eqa3.
    clear dependent eq.

    introv br ext; introv.
    pose proof (eqa0 _ br _ ext x) as eqa0; simpl in *; exrepnd.
    exists bar'.

    introv br' ext' x'.
    pose proof (eqa1 _ br' _ ext' x') as eqa1; simpl in *.
    unfold univi_eq in *; exrepnd.
    fold (@nuprli o i) in *.

    pose proof (nuprli_monotone_func i lib'2 A1 A2 eqa eqa0) as tya; exrepnd.
    rename eq' into eqa'.

    assert (forall lib',
               lib_extends lib' lib'2 ->
               forall a a',
                 equality lib' a a' A1 ->
                 equality lib' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']] (mkc_uni i)) as teq.
    { introv xt ea; eapply eqb; eauto 3 with slow. }
    clear eqb.

    eapply choice_ext_teqi in teq;[|introv;eapply nuprli_implies_nuprl;eapply tya0];[].
    exrepnd.
    rename eqb into eqb'.

    exists (per_product_eq_bar lib'2 eqa' eqb').
    apply CL_product; fold (@nuprli o i).
    exists eqa' eqb'.
    dands; auto;[].
    exists A1 A2 v1 v2 B1 B2; dands; spcast; eauto 3 with slow;[].

    introv; apply tya0.
Qed.

Lemma tequality_mkc_prod {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_prod A1 B1) (mkc_prod A2 B2)
    <=> (tequality lib A1 A2 # in_ext lib (fun lib => inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_prod.
  rw @tequality_product.
  split; intro k; repnd; dands; auto.

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
  forall lib (A B : @CTerm p),
    type lib (mkc_prod A B) <=> (type lib A # in_ext lib (fun lib => inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkc_prod; sp.
Qed.

Lemma inhabited_product {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_product A v B)
    <=>
    (type lib A
     # in_ext lib (fun lib => forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {t : CTerm
       , all_in_ex_bar
           lib
           (fun lib =>
              {a , b : CTerm
              , t ===>(lib) (mkc_pair a b)
              # member lib a A
              # member lib b (substc a v B)})}).
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
    eapply all_in_ex_bar_modus_ponens1;[|exact k2]; clear k2.
    introv e k; exrepnd.
    exists a a b b; dands; auto; eauto 3 with slow.
Qed.

Lemma inhabited_exists {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_exists A v B)
    <=>
    (type lib A
     # in_ext lib (fun lib => forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {t : CTerm
       , all_in_ex_bar
           lib
           (fun lib =>
              {a , b : CTerm
              , t ===>(lib) (mkc_pair a b)
              # member lib a A
              # member lib b (substc a v B)})}).
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
  forall lib (p : @CTerm o) A v B,
    member lib p (mkc_product A v B)
    <=>
    (type lib (mkc_product A v B)
     # all_in_ex_bar
         lib
         (fun lib =>
            {a , b : CTerm
            , p ===>(lib) (mkc_pair a b)
            # member lib a A
            # member lib b (substc a v B)})).
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
  forall lib (A B : @CTerm p),
    inhabited_type_bar lib (mkc_prod A B)
    <=>
    (type lib A
     # type lib B
     # inhabited_type_bar lib A
     # inhabited_type_bar lib B).
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

  - unfold inhabited_type_bar, all_in_ex_bar in *; exrepnd.
    apply (implies_all_in_bar_intersect_bars_left _ bar) in k4.
    apply (implies_all_in_bar_intersect_bars_right _ bar0) in k3.
    remember (intersect_bars bar0 bar) as b.
    clear dependent bar.
    clear dependent bar0.
    exists b.
    introv br ext.
    pose proof (k4 _ br _ ext) as k4; simpl in *.
    pose proof (k3 _ br _ ext) as k3; simpl in *.

    unfold inhabited_type in *; exrepnd.
    exists (mkc_pair t0 t).
    apply equality_in_prod; dands; eauto 3 with slow.

    { introv e inh; eapply inhabited_implies_tequality; eauto 3 with slow. }

    { exists (trivial_bar lib'0).
      apply in_ext_implies_all_in_bar_trivial_bar; introv e.
      exists t0 t0 t t; dands; spcast; eauto 3 with slow. }
Qed.

Lemma inhabited_prod2 {p} :
  forall lib (A B : @CTerm p),
    inhabited_type_bar lib (mkc_prod A B)
    <=>
    (type lib A
     # inhabited_type_bar lib A
     # type lib B
     # inhabited_type_bar lib B).
Proof.
  introv.
  rw @inhabited_prod; split; sp.
Qed.
