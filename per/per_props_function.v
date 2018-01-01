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

  Authors: Vincent Rahli

 *)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.



Definition pair2lib_per {o}
           {lib A  B}
           (f : {lib' : library $ lib_extends lib' lib} -> per(o))
           (p : forall a, nuprl (projT1 a) A B (f a)): lib-per(lib,o).
Proof.
  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).

  introv.
  pose proof (p (exI(lib',e))) as a.
  pose proof (p (exI(lib',y))) as b.
  apply nuprl_refl in a.
  apply nuprl_refl in b.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

Lemma choice_ext_lib_teq {o} :
  forall lib (A B : @CTerm o),
    in_ext lib (fun lib' => tequality lib' A B)
    -> {eqa : lib-per(lib,o),
        forall lib' (e : lib_extends lib' lib), nuprl lib' A B (eqa lib' e) }.
Proof.
  introv F.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun a b => nuprl (projT1 a) A B b)) as C.
  autodimp C hyp.

  {
    unfold tequality in F.
    introv; exrepnd; simpl in *; auto.
  }

  exrepnd.
  exists (pair2lib_per f C0); simpl.
  introv.
  pose proof (C0 (existT (fun lib' => lib_extends lib' lib) lib' e)) as C.
  simpl in *; auto.
Qed.

Definition pair_dep2lib_per {o}
           {lib : library}
           {eqa : lib-per(lib,o)}
           {v1 v2 B1 B2}
           (f : {lib' : library $ {ext : lib_extends lib' lib $ {a1, a2 : CTerm $ eqa lib' ext a1 a2}}} -> per(o))
           (p : forall a, nuprl (projT1 a) (B1)[[v1\\projT1(projT2(projT2 a))]] (B2)[[v2\\projT1(projT2(projT2(projT2 a)))]] (f a))
  : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).

  introv.
  pose proof (p (exI( lib', exI( e, exI( a, exI( b, p0)))))) as w.
  pose proof (p (exI( lib', exI( y, exI( a, exI( b, q)))))) as z.
  apply nuprl_refl in w.
  apply nuprl_refl in z.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

Lemma choice_ext_lib_teq_fam {o} :
  forall lib (A1 : @CTerm o) v1 B1 A2 v2 B2 (eqa : lib-per(lib,o)),
    (forall lib' e, nuprl lib' A1 A2 (eqa lib' e))
    -> (forall lib',
           lib_extends lib' lib
           -> forall a a' : CTerm,
             equality lib' a a' A1
             -> exists eq, nuprl lib' (B1)[[v1\\a]] (B2)[[v2\\a']] eq)
    -> {eqb : lib-per-fam(lib,eqa,o),
              forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
                nuprl lib' (B1)[[v1\\a]] (B2)[[v2\\a']] (eqb lib' x a a' e) }.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             exists eq, nuprl lib' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']] eq) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A1 A2 a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprl
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v1 B1)
                              (substc (projT1 (projT2 (projT2 (projT2 a)))) v2 B2)
                              b)) as C.
  autodimp C hyp.
  {
    introv; exrepnd; simpl in *.
    eapply F; eauto.
  }

  clear F.
  exrepnd.

  exists (pair_dep2lib_per f C0); simpl.
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))) as C.
  simpl in *; auto.
Qed.

Hint Resolve computes_to_valc_refl : slow.

Lemma type_extensionality_per_func_ext_nuprl {o} :
  @type_extensionality o (per_func_ext nuprl).
Proof.
  introv per e.
  unfold per_func_ext in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_func_ext_nuprl : slow.

Lemma uniquely_valued_per_func_ext_nuprl {o} :
  @uniquely_valued o (per_func_ext nuprl).
Proof.
  introv pera perb.
  unfold per_func_ext in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd; spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_func_ext_eq.

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
Hint Resolve uniquely_valued_per_func_ext_nuprl : slow.

Lemma local_per_bar_per_func_ext_nuprl {o} :
  @local_ts o (per_bar (per_func_ext nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_func_ext_nuprl : slow.

Lemma dest_nuprl_per_func_l {o} :
  forall (ts : cts(o)) lib T A v B T' eq,
    ts = univ
    -> computes_to_valc lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_function {o} :
  forall (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprl lib (mkc_function A v B) (mkc_function C w D) eq
    -> per_bar (per_func_ext nuprl) lib (mkc_function A v B) (mkc_function C w D) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_func_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Record lib_per_and_fam {o} {lib} :=
  MkLibPerAndFam
    {
      lpaf_eqa : lib-per(lib,o);
      lpaf_eqb : lib-per-fam(lib,lpaf_eqa,o);
    }.

Notation "bar-and-fam-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib),
      @lib_per_and_fam o lib2).

Lemma all_in_bar_ext_exists_per_and_fam_implies_exists {o} :
  forall {lib} (bar : @BarLib o lib)
         (F : forall lib' (x : lib_extends lib' lib) (eqa : lib-per(lib',o)) (eqb : lib-per-fam(lib',eqa,o)), Prop),
    all_in_bar_ext bar (fun lib' x => {eqa : lib-per(lib',o) , {eqb : lib-per-fam(lib',eqa,o) , F lib' x eqa eqb }})
    ->
    exists (feqa : bar-and-fam-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 x (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => @lib_per_and_fam o (plb_lib2 _ x))
                (fun x e => F (plb_lib2 _ x)
                              (plb_x _ x)
                              (lpaf_eqa e)
                              (lpaf_eqb e))) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; simpl in *.
    pose proof (h _ plb_br _ plb_ext plb_x) as h; simpl in *; exrepnd.
    exists (MkLibPerAndFam _ _ eqa eqb); simpl; auto. }

  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

Definition bar_and_fam_per2lib_per {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {x : lib_extends lib' lib
            , lpaf_eqa (feqa lib1 br lib' ext x) lib' (lib_extends_refl lib') t1 t2}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br ext x0; auto.
  - exists lib1 br ext x0; auto.
Defined.

Lemma type_family_ext_nuprl_function_uniquely_valued_eqas {o} :
  forall lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_function nuprl lib (mkc_function A v B) (mkc_function C w D) eqa1 eqb1
    -> type_family_ext mkc_function nuprl lib (mkc_function A v B) (mkc_function C w D) eqa2 eqb2
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
         (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_function nuprl lib2 (mkc_function A v B) (mkc_function C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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
  eapply type_family_ext_nuprl_function_uniquely_valued_eqas in q1; try exact q2.
  simpl in *.
  pose proof (q1 _ (lib_extends_refl lib')) as q1; simpl in *.
  apply q1; auto.
Qed.

Definition bar_and_fam_per2lib_per_fam {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o))
           {A v B C w D}
           (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_function nuprl lib2 (mkc_function A v B) (mkc_function C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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

Lemma dest_nuprl_function2 {o} :
  forall lib (eq : per(o)) A v B C w D,
    nuprl lib (mkc_function A v B) (mkc_function C w D) eq
    ->
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq bar (per_func_ext_eq_bar_lib_per lib eqa eqb))
      # all_in_bar_ext bar (fun lib' x => nuprl lib' A C (eqa lib' x))
      # all_in_bar_ext bar (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprl lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e)).
Proof.
  introv u.
  apply dest_nuprl_function in u.
  unfold per_bar in u; exrepnd.

  apply all_in_bar_ext_exists_per_and_fam_implies_exists in u0; exrepnd.

  assert (forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_function nuprl lib2 (mkc_function A v B) (mkc_function C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x))) as F by eapply u2.

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
    apply implies_eq_term_equals_per_func_ext_eq.

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

(*Definition raise_lib_per2bar {o}
           {lib}
           (eqa : lib-per(lib,o))
           (bar : BarLib lib) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            all_in_bar
              bar
              (fun lib'' => lib_extends lib' lib'' -> eqa lib' x t1 t2)).

  repeat introv.
  split; intro h; exrepnd; introv br ext w.
  - pose proof (h _ br _ ext w) as h; simpl in h; eapply lib_per_cond; eauto.
  - pose proof (h _ br _ ext w) as h; simpl in h; eapply lib_per_cond; eauto.
Defined.

Definition raise_lib_per_fam2bar {o}
           {lib}
           {eqa : lib-per(lib,o)}
           (eqb : lib-per-fam(lib,eqa,o))
           (bar : BarLib lib) : lib-per-fam(lib,raise_lib_per2bar eqa bar,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib)
              a a' (e : raise_lib_per2bar eqa bar lib' x a a') t1 t2 =>
            all_in_bar_ext2
              bar
              (fun lib1 (br : bar_lib_bar bar lib1)
                   lib2 (y : lib_extends lib2 lib1) =>
                 forall (w : lib_extends lib' lib2),
                   eqb lib' x a a' (e _ br _ y w) t1 t2)).

  repeat introv.
  split; intro h; exrepnd; repeat introv.
  - pose proof (h _ b0 _ e0 w) as h; simpl in *.
    eapply lib_per_fam_cond; eauto.
  - pose proof (h _ b0 _ e0 w) as h; simpl in *.
    eapply lib_per_fam_cond; eauto.
Defined.

Definition lib_per_fam2lib_per {o} {lib}
           {eqa : lib-per(lib,o)}
           (a a' : CTerm)
           (F : in_ext_ext lib (fun lib' x => eqa lib' x a a'))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            eqb lib' x a a' (F lib' x)).

  repeat introv.
  eapply lib_per_fam_cond.
Defined.*)

Definition lib_per_fam2lib_per {o} {lib}
           {eqa : lib-per(lib,o)}
           (a a' : @CTerm o)
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {e : eqa lib' x a a' ,  eqb lib' x a a' e t1 t2}).

  repeat introv.
  split; intro h; exrepnd.
  - assert (eqa lib' y a a') as f by (eapply lib_per_cond; eauto).
    exists f; eapply lib_per_fam_cond; eauto.
  - assert (eqa lib' e a a') as f by (eapply lib_per_cond; eauto).
    exists f; eapply lib_per_fam_cond; eauto.
Defined.


(* This is basically 'functionEquality' *)
Lemma tequality_function {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    tequality lib
              (mkc_function A1 v1 B1)
              (mkc_function A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # in_ext lib (fun lib' => forall a a', equality lib' a a' A1 -> tequality lib' (substc a v1 B1) (substc a' v2 B2))).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    applydup @dest_nuprl_function2 in teq0; exrepnd.

    assert (nuprl lib A1 A2 (per_bar_eq bar eqa)) as ea.
    { apply CL_bar; exists bar eqa; dands; auto. }

    dands.

    { exists (per_bar_eq bar eqa); auto. }

    {
      introv x eqas.

      exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
      apply CL_bar.
      exists (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
      introv br ext; introv; simpl in *; exrepnd.
      fold (@nuprl o).
      pose proof (teq3 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as teq3; simpl in *.

      assert (eqa lib'1 (lib_extends_trans x0 x) a a') as xx.
      {
        pose proof (equality_eq1 lib'1 A1 A2 a a' (eqa lib'1 (lib_extends_trans x0 x))) as w.
        apply w; auto; eauto 3 with slow.
      }

      pose proof (teq2 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x) a a' xx) as teq2; simpl in *.

      eapply type_extensionality_nuprl;[eauto|].
      introv; split; intro w; eauto;[].
      exrepnd.
      unfold raise_ext_per, raise_ext_per_fam in *.
      eapply lib_per_fam_cond; eauto.
    }

  - Case "<-".
    introv e; exrepnd.

    assert (forall lib', lib_extends lib' lib -> tequality lib' A1 A2) as teqa by eauto 3 with slow.
    clear e0.

    rename e into teqb.

    unfold tequality in *.

    apply choice_ext_lib_teq in teqa; exrepnd.
    eapply choice_ext_lib_teq_fam in teqb;[|eauto]; exrepnd.

    exists (per_func_ext_eq lib eqa eqb).
    apply CL_func.
    exists eqa eqb.
    dands; eauto 3 with slow.
    exists A1 A2 v1 v2 B1 B2.
    dands; spcast; eauto 3 with slow.
Qed.

Lemma if_member_function {o} :
  forall lib (f : @CTerm o) A v B,
    member lib f (mkc_function A v B)
    ->
    forall lib' (x : lib_extends lib' lib) x y,
      equality lib' x y A
      -> equality lib' (mkc_apply f x) (mkc_apply f y) (substc x v B).
Proof.
  introv m x e.
  unfold member, equality, nuprl in m; exrepnd.

  applydup @dest_nuprl_function2 in m1; exrepnd.

  exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per x0 y (raise_lib_per_fam eqb x))).
  dands.

  {
    apply CL_bar.
    exists (raise_bar bar x) (lib_per_fam2lib_per x0 y (raise_lib_per_fam eqb x)); dands; tcsp;[].
    introv br ext; introv; simpl in *; exrepnd.
    fold (@nuprl o).
    pose proof (m4 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x1 x)) as m4; simpl in *.

    assert (eqa lib'1 (lib_extends_trans x1 x) x0 y) as xx.
    {
      pose proof (equality_eq1 lib'1 A A x0 y (eqa lib'1 (lib_extends_trans x1 x))) as w.
      apply w; auto; eauto 3 with slow.
    }

    pose proof (m3 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x1 x) x0 y xx) as m3; simpl in *.

    apply nuprl_refl in m3.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[].
    exrepnd.
    unfold raise_ext_per, raise_ext_per_fam in *.
    eapply lib_per_fam_cond; eauto.
  }

  {
    introv br ext; introv; simpl in *; exrepnd.
    unfold raise_ext_per_fam.
    apply m2 in m0.
    pose proof (m0 _ br1 lib'1 (lib_extends_trans ext br2) (lib_extends_trans x1 x)) as m0; simpl in *.
    unfold per_func_ext_eq in m0.
    apply collapse2bars_ext.
    { introv; split; intro h; exrepnd; simpl in *.
      - assert (raise_ext_per eqa x lib'2 (lib_extends_trans y0 x1) x0 y) as xx.
        { eapply lib_per_cond; eauto. }
        exists xx.
        eapply lib_per_fam_cond; eauto.
      - assert (raise_ext_per eqa x lib'2 (lib_extends_trans x2 x1) x0 y) as xx.
        { eapply lib_per_cond; eauto. }
        exists xx.
        eapply lib_per_fam_cond; eauto. }

    exrepnd.
    exists bar'.
    introv br' ext'; introv.
    pose proof (m5 _ br' _ ext' x2) as m5; simpl in *.
    exrepnd.
    exists bar0.
    introv br'' ext''; introv.
    pose proof (m0 _ br'' _ ext'' x3) as m0; simpl in *.

    assert (lib_extends lib'5 lib1) as xt1 by eauto 4 with slow.
    assert (lib_extends lib'5 lib) as xt2 by eauto 3 with slow.
    pose proof (m4 _ br1 lib'5 xt1 xt2) as m4; simpl in *.

    assert (eqa lib'5 (lib_extends_trans x3 (lib_extends_trans x2 (lib_extends_trans x1 x))) x0 y) as xx.
    {
      pose proof (equality_eq1 lib'5 A A x0 y (eqa lib'5 (lib_extends_trans x3 (lib_extends_trans x2 (lib_extends_trans x1 x))))) as w.
      apply w; auto; eauto 4 with slow.
      eapply type_extensionality_nuprl;[eauto|].
      apply lib_per_cond.
    }

    pose proof (m0 _ _ xx) as m0.
    unfold raise_ext_per_fam in *.

    assert (raise_ext_per eqa x lib'5 (lib_extends_trans (lib_extends_trans x3 x2) x1) x0 y) as yy by (eapply lib_per_cond; eauto).
    exists yy.
    eapply lib_per_fam_cond; eauto.
  }
Qed.

(*
(* !!MOVE to nuprl_mon *)
Definition type_monotone3 {o} (ts : cts(o)) :=
  forall lib T1 T2 eq,
    ts lib T1 T2 eq
    ->
    exists (eq' : lib-per(lib,o)),
    forall lib' (x : lib_extends lib' lib),
      ts lib' T1 T2 (eq' lib' x) # sub_per eq (eq' lib' x).

(* !!MOVE to nuprl_mon *)
Lemma type_monotone2_implies_type_monotone3 {o} :
  forall (ts : cts(o)), type_monotone2 ts -> type_monotone3 ts.
Proof.
  introv mon tsts.
  pose proof (mon lib) as mon.

  assert (forall (T1 T2 : CTerm) (eq : per(o)),
             ts lib T1 T2 eq
             ->
             forall (lib' : library),
               lib_extends lib' lib
               -> exists eq', ts lib' T1 T2 eq' # sub_per eq eq') as mon'.
  { introv h ext; eapply mon in h; eauto. }
  clear mon; rename mon' into mon.

  pose proof (mon T1 T2 eq) as mon; autodimp mon hyp.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun a b => ts (projT1 a) T1 T2 b # sub_per eq b)) as mon'.
  autodimp mon' hyp.
  { introv; exrepnd; simpl in *; auto. }

  clear mon; rename mon' into mon.
  exrepnd.

  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).
  introv.
  pose proof (mon0 (existT (fun lib' => lib_extends lib' lib) lib' x)) as mon.
  simpl in *; auto.
Qed.
*)

Definition pair_dep2lib_per2 {o}
           {lib : library}
           {eqa : lib-per(lib,o)}
           {v B F1 F2}
           (f : {lib' : library $ {ext : lib_extends lib' lib $ {a1, a2 : CTerm $ eqa lib' ext a1 a2}}} -> per(o))
           (p : forall a : {lib' : library $ {ext : lib_extends lib' lib $ {a1, a2 : CTerm $ eqa lib' ext a1 a2}}},
               (nuprl (projT1 a) (B) [[v \\ projT1 (projT2 (projT2 a))]] (B) [[v \\ projT1 (projT2 (projT2 a))]] (f a))
                 # f a (F1 (projT1 (projT2 (projT2 a)))) (F2 (projT1 (projT2 (projT2 (projT2 a))))))
  : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).

  introv.
  pose proof (p (exI( lib', exI( e, exI( a, exI( b, p0)))))) as w.
  pose proof (p (exI( lib', exI( y, exI( a, exI( b, q)))))) as z.
  repnd.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

Lemma choice_ext_lib_eq_fam {o} :
  forall lib (A A' : @CTerm o) v B (eqa : lib-per(lib,o)) F1 F2,
    (forall lib' e, nuprl lib' A A' (eqa lib' e))
    -> (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> equality lib' (F1 a) (F2 a') (B)[[v\\a]])
    -> {eqb : lib-per-fam(lib,eqa,o),
              forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
                nuprl lib' (B)[[v\\a]] (B)[[v\\a]] (eqb lib' x a a' e)
                      # eqb lib' x a a' e (F1 a) (F2 a')}.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             equality lib' (F1 a) (F2 a') (B)[[v\\a]]) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A A' a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprl
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v B)
                              (substc (projT1 (projT2 (projT2 a))) v B)
                              b
                              # b (F1 (projT1 (projT2 (projT2 a))))
                                  (F2 (projT1 (projT2 (projT2 (projT2 a))))))) as C.
  autodimp C hyp.
  {
    introv; exrepnd; simpl in *.
    eapply F; eauto.
  }

  clear F.
  exrepnd.

  exists (pair_dep2lib_per2 f C0).
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))) as C.
  simpl in *; auto.
Qed.

(* This is 'functionExtensionality' *)
Lemma implies_member_function {o} :
  forall lib (f : @CTerm o) g A v B,
    type lib A
    -> (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> tequality lib' (substc a v B) (substc a' v B))
    -> (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))
    -> equality lib f g (mkc_function A v B).
Proof.
  introv ty teq eqap.
  unfold member, equality.
  unfold type, tequality in ty; exrepnd.
  rename eq into eqa.

  pose proof (nuprl_monotone_func lib A A eqa ty0) as tya; exrepnd.
  rename eq' into eqa'.

  eapply choice_ext_lib_teq_fam in teq;[|apply tya0].
  exrepnd.

  eapply choice_ext_lib_eq_fam in eqap;[|apply tya0].
  exrepnd.
  rename eqb0 into eqb'.

  exists (per_func_ext_eq lib eqa' eqb).
  dands;[|].

  {
    apply CL_func.
    exists eqa' eqb.
    dands; auto;[].
    exists A A v v B B; dands; spcast; eauto 3 with slow;[].

    fold (@nuprl o) in *.
    introv; apply tya0.
  }

  exists (trivial_bar lib).
  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
  repeat introv.
  pose proof (eqap0 lib' e a a' e0) as q;repnd.
  pose proof (teq0 lib' e a a' e0) as h.
  apply nuprl_refl in h.
  eapply nuprl_uniquely_valued in h;[|exact q0].
  apply h; auto.
Qed.

(**

  As another example, we can prove that two terms [f] and [g] are
  equal in the function type [mkc_function A v B] if and only if [A]
  is a type, [B] is functional over [A], and forall [a] and [a'] equal
  in [A], [mkc_apply f a] and [mkc_apply g a'] are equals in [substc a
  v B].

  This is one of the lemmas where we need the [FunctionalChoice_on]
  axiom. Let us explain that issue.  Let us assume that we want to
  prove the left-hand-side of [<=>] from its right-hand-side.  To
  prove that [f] and [g] are equal in [mkc_function A v B], we have to
  provide the equality of the function type, and in particular, we
  have to provide the equality of its co-domain.  We obtain that
  equality from the third clause in the right-hand-side of the [<=>].
  However, in our current [Prop] metatheory, that clause is (roughly)
  a [forall] of a propositional [exists].  From such a formula, we
  need to build a [per-fam] function (the equality of the co-domain),
  which is exactly what [FunctionalChoice_on] gives us.  This axiom is
  necessary because in general we cannot access the witness of a
  propositional existential.

 *)

(* This is the <=> verison of 'implies_member_function' *)
Lemma equality_in_function {o} :
  forall lib (f : @CTerm o) g A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> tequality lib' (substc a v B) (substc a' v B))
     # (forall lib' (x : lib_extends lib' lib) a a',
           equality lib' a a' A
           -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; sp_iff Case; introv e; try (complete (apply implies_member_function; sp));[].

  unfold equality in e; exrepnd.

  applydup @dest_nuprl_function2 in e1; exrepnd.
  apply e2 in e0.
  clear dependent eq.
  dands.

  {
    exists (per_bar_eq bar eqa).
    apply CL_bar; exists bar eqa; dands; tcsp.
  }

  {
    introv x e.

    exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    apply CL_bar.
    exists (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
    introv br ext; introv; simpl in *; exrepnd.
    fold (@nuprl o).
    pose proof (e4 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as e4; simpl in *.

    assert (eqa lib'1 (lib_extends_trans x0 x) a a') as xx.
    {
      pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans x0 x))) as w.
      apply w; auto; eauto 3 with slow.
    }

    pose proof (e3 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x) a a' xx) as e3; simpl in *.

    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[].
    exrepnd.
    unfold raise_ext_per, raise_ext_per_fam in *.
    eapply lib_per_fam_cond; eauto.
  }

  {
    introv x e.

    exists (per_bar_eq (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    dands.

    {
      apply CL_bar.
      exists (raise_bar bar x) (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
      introv br ext; introv; simpl in *; exrepnd.
      fold (@nuprl o).
      pose proof (e4 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as e4; simpl in *.

      assert (eqa lib'1 (lib_extends_trans x0 x) a a') as xx.
      {
        pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans x0 x))) as w.
        apply w; auto; eauto 3 with slow.
      }

      pose proof (e3 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x0 x) a a' xx) as e3; simpl in *.

      apply nuprl_refl in e3.
      eapply type_extensionality_nuprl;[eauto|].
      introv; split; intro w; eauto;[].
      exrepnd.
      unfold raise_ext_per, raise_ext_per_fam in *.
      eapply lib_per_fam_cond; eauto.
    }

    {
      introv br ext; introv; simpl in *; exrepnd.
      unfold raise_ext_per_fam.
      pose proof (e0 _ br1 lib'1 (lib_extends_trans ext br2) (lib_extends_trans x0 x)) as e0.
      simpl in *.
      unfold per_func_ext_eq in e0.

      apply collapse2bars_ext.
      { introv; split; intro h; exrepnd; simpl in *.
        - assert (raise_ext_per eqa x lib'2 (lib_extends_trans y x0) a a') as xx.
          { eapply lib_per_cond; eauto. }
          exists xx.
          eapply lib_per_fam_cond; eauto.
        - assert (raise_ext_per eqa x lib'2 (lib_extends_trans x1 x0) a a') as xx.
          { eapply lib_per_cond; eauto. }
          exists xx.
          eapply lib_per_fam_cond; eauto. }

      exrepnd.
      exists bar'.
      introv br' ext'; introv.
      pose proof (e1 _ br' _ ext' x1) as e1; simpl in *.
      exrepnd.
      exists bar0.
      introv br'' ext''; introv.
      pose proof (e0 _ br'' _ ext'' x2) as e0; simpl in *.

      assert (lib_extends lib'5 lib1) as xt1 by eauto 4 with slow.
      assert (lib_extends lib'5 lib) as xt2 by eauto 3 with slow.
      pose proof (e4 _ br1 lib'5 xt1 xt2) as e4; simpl in *.

      assert (eqa lib'5 (lib_extends_trans x2 (lib_extends_trans x1 (lib_extends_trans x0 x))) a a') as xx.
      {
        pose proof (equality_eq1 lib'5 A A a a' (eqa lib'5 (lib_extends_trans x2 (lib_extends_trans x1 (lib_extends_trans x0 x))))) as w.
        apply w; auto; eauto 4 with slow.
        eapply type_extensionality_nuprl;[eauto|].
        apply lib_per_cond.
      }

      pose proof (e0 _ _ xx) as e0.
      unfold raise_ext_per_fam in *.

      assert (raise_ext_per eqa x lib'5 (lib_extends_trans (lib_extends_trans x2 x1) x0) a a') as yy by (eapply lib_per_cond; eauto).
      exists yy.
      eapply lib_per_fam_cond; eauto.
    }
  }
Qed.

Lemma equality_in_function2 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib (mkc_function A v B)
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv.
  rw @equality_in_function; split; intro k; repnd; dands; try (complete sp).

  { unfold type; rw @tequality_function; sp. }

  { rw @tequality_function in k0; sp. }

  { rw @tequality_function in k0; sp. }
Qed.

Lemma inhabited_function {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_function A v B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib) a a', equality lib' a a' A -> tequality lib' (substc a v B) (substc a' v B))
     # {f : CTerm
        , forall lib' (x : lib_extends lib' lib) a a',
            equality lib' a a' A
            -> equality lib' (mkc_apply f a) (mkc_apply f a') (substc a v B)}).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_function in k0; repnd; dands; try (complete sp).
    exists t; sp.

  - exrepnd.
    exists f.
    rw @equality_in_function; sp.
Qed.

Lemma equality_in_function3 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> tequality lib' (substc a v B) (substc a' v B)
             # equality lib' (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; rw @equality_in_function; split; introv h; repnd;
    dands; tcsp; introv x e; eapply h; eauto.
Qed.

Lemma tequality_function_fun {p} :
  forall lib (A : @CTerm p) v B,
    (type lib (mkc_function A v (mk_cv [v] B)) {+} type lib (mkc_fun A B))
    -> tequality lib (mkc_function A v (mk_cv [v] B))
                 (mkc_fun A B).
Proof.
  introv o; repdors.

  { apply tequality_respects_alphaeqc_right with (T2 := mkc_function A v (mk_cv [v] B)); sp. }

  { apply tequality_respects_alphaeqc_left with (T1 := mkc_fun A B); sp.
    apply alphaeqc_sym; sp. }
Qed.

Lemma tequality_mkc_fun_dom {p} :
  forall lib (A1 A2 B : @CTerm p),
    tequality lib A1 A2
    -> type lib (mkc_fun A1 B)
    -> tequality lib (mkc_fun A1 B) (mkc_fun A2 B).
Proof.
  introv teqa teqf.
  allrw <- @fold_mkc_fun.
  allrw @tequality_function; repnd; dands; auto.
Qed.

Lemma tequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=>
    (tequality lib A1 A2
      # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A1 -> tequality lib' B1 B2)).
Proof.
  intros.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv x e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq lib' x t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp.

  - pose proof (teq lib' x) as teq.
    autodimp teq hyp.
    exists a; allapply @equality_refl; sp.
    repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_mkc_fun_l {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    -> tequality lib A1 A2.
Proof.
  introv Hpart1.
  rw @tequality_fun in Hpart1; sp.
Qed.

Lemma equality_in_fun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_fun A B)
    <=>
    (type lib A
     # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A -> type lib' B)
     # (forall lib' (x : lib_extends lib' lib) a a',
          equality lib' a a' A
          -> equality lib' (mkc_apply f a) (mkc_apply g a') B)).
Proof.
  introv.
  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  split; intro k; repnd; dands; auto.

  {
    introv x i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 lib' x t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.
  }

  {
    introv x e.
    apply k in e; auto.
    repeat (rw @csubst_mk_cv in e); sp.
  }

  {
    introv x e.
    repeat (rw @csubst_mk_cv); sp.
    pose proof (k1 lib' x) as k1.
    autodimp k1 hyp.
    exists a; allapply @equality_refl; sp.
  }

  {
    introv x e.
    repeat (rw @csubst_mk_cv); sp.
  }
Qed.

Lemma tequality_mkc_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=> (tequality lib A1 A2
         # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A1 -> tequality lib' B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro k; repnd; dands; auto; introv x.

  {
    introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k lib' x t t i0); intro teq.
    allrw @csubst_mk_cv; auto.
  }

  {
    introv e.
    allrw @csubst_mk_cv; auto.
    apply equality_refl in e.
    pose proof (k lib' x) as k.
    autodimp k hyp.
    exists a; auto.
  }
Qed.

Lemma type_mkc_fun {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_fun A B) <=> (type lib A # (forall lib' (x : lib_extends lib' lib), inhabited_type lib' A -> type lib' B)).
Proof.
  introv.
  rw @tequality_mkc_fun; sp.
Qed.

Definition pair_dep2lib_per3 {o}
           {lib : library}
           {eqa : lib-per(lib,o)}
           {v1 v2 B1 B2 i}
           (f : {lib' : library $ {ext : lib_extends lib' lib $ {a1, a2 : CTerm $ eqa lib' ext a1 a2}}} -> per(o))
           (p : forall a, nuprli i (projT1 a) (B1)[[v1\\projT1(projT2(projT2 a))]] (B2)[[v2\\projT1(projT2(projT2(projT2 a)))]] (f a))
  : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun (lib' : library) (x : lib_extends lib' lib) a a' (e : eqa lib' x a a') =>
            f (existT _ lib' (existT _ x (existT _ a (existT _ a' e))))).

  introv.
  pose proof (p (exI( lib', exI( e, exI( a, exI( b, p0)))))) as w.
  pose proof (p (exI( lib', exI( y, exI( a, exI( b, q)))))) as z.
  apply nuprli_refl in w.
  apply nuprli_refl in z.
  simpl in *.
  eapply nuprli_uniquely_valued; eauto.
Defined.

Lemma choice_ext_teqi {o} :
  forall lib i (A A' : @CTerm o) v1 B1 v2 B2 (eqa : lib-per(lib,o)),
    (forall lib' e, nuprl lib' A A' (eqa lib' e))
    -> (forall lib' (x : lib_extends lib' lib) a1 a2,
           equality lib' a1 a2 A
           -> equality lib' (substc a1 v1 B1) (substc a2 v2 B2) (mkc_uni i))
    -> {eqb : lib-per-fam(lib,eqa,o),
         forall lib' (x : lib_extends lib' lib) a1 a2 (e : eqa lib' x a1 a2),
            nuprli i lib' (substc a1 v1 B1) (substc a2 v2 B2) (eqb lib' x a1 a2 e)}.
Proof.
  introv teqa F.

  assert (forall lib' (x : lib_extends lib' lib) a a' (e : eqa lib' x a a'),
             equality lib' (B1)[[v1\\a]] (B2)[[v2\\a']] (mkc_uni i)) as G.
  {
    introv e.
    apply (F lib' x a a').
    apply (equality_eq1 lib' A A' a a' (eqa lib' x)); auto.
  }
  clear F; rename G into F.

  pose proof (FunctionalChoice_on
                {lib' : library & {ext : lib_extends lib' lib & {a1 : CTerm & {a2 : CTerm & eqa lib' ext a1 a2}}}}
                per
                (fun a b => nuprli
                              i
                              (projT1 a)
                              (substc (projT1 (projT2 (projT2 a))) v1 B1)
                              (substc (projT1 (projT2 (projT2 (projT2 a)))) v2 B2)
                              b)) as C.
  autodimp C hyp.
  {
    introv; exrepnd; simpl in *.
    pose proof (F lib' ext a0 a1 a3) as G.
    unfold equality in G; exrepnd.

    apply dest_nuprl_uni in G1.
    apply univ_implies_univi_bar3 in G1; exrepnd.
    apply G2 in G0.
    clear dependent eq.

    assert (exists (bar : BarLib lib'), per_bar_eq bar (univi_eq_lib_per lib' i) (substc a0 v1 B1) (substc a1 v2 B2)) as h by (exists bar; auto).
    clear dependent bar.
    unfold per_bar_eq in h; simpl in *.

    pose proof (@collapse2bars_ext o lib' (fun lib'' x => univi_eq (univi_bar i) lib'' (substc a0 v1 B1) (substc a1 v2 B2))) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in h; clear q.
    exrepnd.
    unfold univi_eq in h0; fold (@nuprli o i) in *.

    apply all_in_bar_ext_exists_per_implies_exists in h0; exrepnd.
    exists (per_bar_eq bar (bar_per2lib_per feqa)).
    apply CL_bar.
    exists bar (bar_per2lib_per feqa).
    dands; tcsp;[].

    introv br xt ; introv; simpl; try (fold (@nuprli o i)).
    pose proof (h1 _ br _ xt x) as q.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro h.

    { exists lib'0 br xt x; auto. }

    exrepnd.
    pose proof (h1 _ br0 _ ext0 x0) as h1.
    eapply nuprli_uniquely_valued in h1; try exact q.
    apply h1; auto.
  }
  clear F.
  exrepnd.

  exists (pair_dep2lib_per3 f C0).
  introv; simpl in *.
  pose proof (C0 (existT _ lib' (existT _ x (existT _ a1 (existT _ a2 e))))) as C.
  simpl in *; auto.
Qed.

Lemma equality_function {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_function A1 v1 B1)
      (mkc_function A2 v2 B2)
      (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # forall lib' (x : lib_extends lib' lib) a a',
         equality lib' a a' A1
         -> equality lib' (substc a v1 B1) (substc a' v2 B2) (mkc_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.

    dands.

    {
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.


XXXXXXXXX

      inversion teq1; subst; try not_univ;[].
      duniv j h.
      allrw @univi_exists_iff; exrepd.
      computes_to_value_isvalue; GC.
      discover; exrepnd.
      rename eqa into eqi.
      ioneclose; subst; try not_univ;[].

      one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
      computes_to_value_isvalue; GC.

      exists eq; sp.
      allrw.
      exists (eqa lib (lib_extends_refl lib)); sp.
    }

    {
      introv x ea.
      eapply equality_monotone in teq;[|eauto].

      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      inversion teq1; subst; try not_univ;[].
      duniv j h.
      allrw @univi_exists_iff; exrepd.
      computes_to_value_isvalue; GC.
      discover; exrepnd.
      rename eqa into eqi.
      ioneclose; subst; try not_univ;[].

      one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
      computes_to_value_isvalue; GC.

      exists eq; sp; try (complete (apply teq1'0));[].

      allfold (@nuprli o j0).
      allrw.
      unfold equality in ea; exrepnd.

      eapply nuprl_uniquely_valued in ea1;
        [|eapply nuprli_implies_nuprl;eapply nuprli_refl;eapply (tsa lib' (lib_extends_refl lib'))];[].
      apply ea1 in ea0.
      pose proof (tsb lib' (lib_extends_refl lib') a a' ea0) as n.
      exists (feqb lib' (lib_extends_refl lib') a a' ea0); sp.
    }

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli o j0).

    exists eq; sp.
    allrw.

    pose proof (@nuprli_monotone2 o j0) as mon.
    apply type_monotone2_implies_type_monotone3 in mon.
    pose proof (mon lib A1 A2 eqa h0) as tya; exrepnd.
    rename eq' into eqa'.

    eapply choice_ext_teqi in eqb;
      [|introv;eapply nuprli_implies_nuprl;apply (tya0 lib' e)].

    exrepnd.
    rename eqb0 into eqb'.

    exists (per_func_ext_eq lib eqa' eqb').
    apply CL_func.
    exists eqa' eqb'.
    dands; auto;[].
    exists A1 A2 v1 v2 B1 B2; dands; spcast; eauto 3 with slow;
      try (complete (introv; apply tya0)).
Qed.
