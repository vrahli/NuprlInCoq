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
Require Export per_props_fam2.


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

  unfold type_family_ext in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp pera3.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_function_implies in ceq.
  apply ccequivc_ext_mkc_function_implies in ceq0.
  repnd.

  apply implies_eq_term_equals_per_func_ext_eq.

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprl_refl in pera4.
    apply nuprl_refl in perb4.
    eapply nuprl_uniquely_valued; eauto.
    eapply nuprl_value_respecting_left;[|eapply lib_extends_preserves_ccequivc_ext;[eauto|];eauto ].
    eapply nuprl_value_respecting_right;[|eapply lib_extends_preserves_ccequivc_ext;[eauto|];eauto ].
    auto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v1) as perb0.
    simpl in *.
    apply nuprl_refl in pera0.
    apply nuprl_refl in perb0.
    eapply nuprl_uniquely_valued; eauto.
    eapply nuprl_value_respecting_left;
      [|eapply lib_extends_preserves_ccequivc_ext;[eauto|];
        apply bcequivc_ext_implies_ccequivc_ext;eauto
      ].
    eapply nuprl_value_respecting_right;
      [|eapply lib_extends_preserves_ccequivc_ext;[eauto|];
        apply bcequivc_ext_implies_ccequivc_ext;eauto
      ].
    auto.
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
    -> ccomputes_to_valc_ext lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
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

Lemma type_family_ext_nuprl_function_uniquely_valued_eqas {o} :
  forall lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_function nuprl lib (mkc_function A v B) (mkc_function C w D) eqa1 eqb1
    -> type_family_ext mkc_function nuprl lib (mkc_function A v B) (mkc_function C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  eapply type_family_ext_nuprl_uniquely_valued_eqas; eauto; eauto 3 with slow.
Qed.

Lemma dest_nuprl_function2 {o} :
  forall lib (eq : per(o)) A v B C w D,
    nuprl lib (mkc_function A v B) (mkc_function C w D) eq
    ->
    exists (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq lib (per_func_ext_eq_bar_lib_per lib eqa eqb))
      # in_open_bar_ext lib (fun lib' x => nuprl lib' A C (eqa lib' x))
      # in_open_bar_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprl lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e)).
Proof.
  introv u.
  apply dest_nuprl_function in u.
  unfold per_bar in u; exrepnd.

  unfold per_func_ext in u1.
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
    apply implies_eq_term_equals_per_func_ext_eq; simpl.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as u; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ z0) in u0.
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
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ z0) in xx0.
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

    pose proof (q3 _ (lib_extends_refl lib'0)) as q3; simpl in *.
    eapply nuprl_value_respecting_left in q3;[|apply ccequivc_ext_sym;eauto].
    eapply nuprl_value_respecting_right in q3;[|apply ccequivc_ext_sym;eauto].
    eapply type_extensionality_nuprl;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      pose proof (u5 _ z0) as u5; simpl in *.
      apply nuprl_refl in u5.
      apply nuprl_refl in q3.
      eapply nuprl_value_respecting_left in u5;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprl_value_respecting_right in u5;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprl_uniquely_valued in u5; try exact q3.
      apply u5; auto.
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

    assert (nuprl lib A1 A2 (per_bar_eq lib eqa)) as ea.
    { apply CL_bar; exists eqa; dands; auto. }

    dands.

    { exists (per_bar_eq lib eqa); auto. }

    {
      introv x eqas.

      exists (per_bar_eq lib' (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
      apply CL_bar.
      exists (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq3.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq1.
      eapply in_open_bar_ext_comb; try exact teq3; clear teq3.
      eapply in_open_bar_ext_pres; try exact teq1; clear teq1; introv teq1 teq3; simpl in *.
      fold (@nuprl o).

      assert (eqa lib'0 (lib_extends_trans e x) a a') as xx.
      {
        pose proof (equality_eq1 lib'0 A1 A2 a a' (eqa lib'0 (lib_extends_trans e x))) as w.
        apply w; auto; eauto 3 with slow.
      }

      pose proof (teq1 _ _ xx) as teq1; simpl in *.

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

  exists (per_bar_eq lib' (lib_per_fam2lib_per x0 y (raise_lib_per_fam eqb x))).
  dands.

  {
    apply CL_bar.
    exists (lib_per_fam2lib_per x0 y (raise_lib_per_fam eqb x)); dands; tcsp;[].
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in m4.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in m2.
    eapply in_open_bar_ext_comb; try exact m4; clear m4.
    eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4; simpl in *.
    fold (@nuprl o).

    assert (eqa lib'0 (lib_extends_trans e0 x) x0 y) as xx.
    {
      pose proof (equality_eq1 lib'0 A A x0 y (eqa lib'0 (lib_extends_trans e0 x))) as w.
      apply w; auto; eauto 3 with slow.
    }

    pose proof (m2 _ _ xx) as m2; simpl in *.
    apply nuprl_refl in m2.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[].
    exrepnd.
    unfold raise_ext_per, raise_ext_per_fam in *.
    eapply lib_per_fam_cond; eauto.
  }

  {
    apply m3 in m0; clear m3.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in m4.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in m2.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in m0.

    apply in_open_bar_ext_twice in m4.
    apply in_open_bar_ext_twice in m2.
    apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_comb; try exact m0; clear m0.
    eapply in_open_bar_ext_comb; try exact m4; clear m4.
    eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4 m0; simpl in *.
    unfold raise_ext_per_fam.
    unfold per_func_ext_eq in m0; simpl in m0.

    eapply in_open_bar_ext_comb; try exact m0; clear m0.
    eapply in_open_bar_ext_comb; try exact m4; clear m4.
    eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4 m0; simpl in *.
    unfold per_func_eq, raise_ext_per, raise_ext_per_fam in *.
    introv.

    assert (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x) x0 y) as ea.
    {
      pose proof (equality_eq1 lib'1 A A x0 y (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x))) as w.
      apply w; auto; eauto 4 with slow.
    }

    assert (eqa lib'1 (lib_extends_trans e1 (lib_extends_trans e0 x)) x0 y) as eb.
    { eapply lib_per_cond; eauto. }

    assert (eqa lib'1 (lib_extends_trans z x) x0 y) as ec.
    { eapply lib_per_cond; eauto. }

    pose proof (m2 _ _ ea) as m2.
    pose proof (m0 _ _ eb) as m0.
    exists ec.
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

  unfold per_func_ext_eq.
  apply in_ext_ext_implies_in_open_bar_ext.
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
  apply e3 in e0.
  clear dependent eq.
  dands.

  {
    exists (per_bar_eq lib eqa).
    apply CL_bar; exists eqa; dands; tcsp.
  }

  {
    introv x e.

    exists (per_bar_eq lib' (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    apply CL_bar.
    exists (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].

    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e0.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e2.
    apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e4.

    apply in_open_bar_ext_twice in e4.
    apply in_open_bar_ext_twice in e2.
    apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_comb; try exact e0; clear e0.
    eapply in_open_bar_ext_comb; try exact e4; clear e4.
    eapply in_open_bar_ext_pres; try exact e2; clear e2; introv m2 m4 m0; simpl in *.
    unfold raise_ext_per_fam.
    unfold per_func_ext_eq in m0; simpl in m0.

    eapply in_open_bar_ext_comb; try exact m0; clear m0.
    eapply in_open_bar_ext_comb; try exact m4; clear m4.
    eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4 m0; simpl in *.
    unfold per_func_eq, raise_ext_per, raise_ext_per_fam in *.
    introv.

    assert (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x) a a') as ea.
    {
      pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x))) as w.
      apply w; auto; eauto 4 with slow.
    }

    assert (eqa lib'1 (lib_extends_trans e1 (lib_extends_trans e0 x)) a a') as eb.
    { eapply lib_per_cond; eauto. }

    assert (eqa lib'1 (lib_extends_trans z x) a a') as ec.
    { eapply lib_per_cond; eauto. }

    pose proof (m2 _ _ ea) as m2.
    pose proof (m0 _ _ eb) as m0.
    fold (@nuprl o).

    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro w; eauto;[|exrepnd; eapply lib_per_fam_cond; eauto].
    exists ec; eapply lib_per_fam_cond; eauto.
  }

  {
    introv x e.

    exists (per_bar_eq lib' (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x))).
    dands.

    {
      apply CL_bar.
      exists (lib_per_fam2lib_per a a' (raise_lib_per_fam eqb x)); dands; tcsp;[].

      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e0.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e2.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e4.

      apply in_open_bar_ext_twice in e4.
      apply in_open_bar_ext_twice in e2.
      apply in_open_bar_ext_dup.
      eapply in_open_bar_ext_comb; try exact e0; clear e0.
      eapply in_open_bar_ext_comb; try exact e4; clear e4.
      eapply in_open_bar_ext_pres; try exact e2; clear e2; introv m2 m4 m0; simpl in *.
      unfold raise_ext_per_fam.
      unfold per_func_ext_eq in m0; simpl in m0.

      eapply in_open_bar_ext_comb; try exact m0; clear m0.
      eapply in_open_bar_ext_comb; try exact m4; clear m4.
      eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4 m0; simpl in *.
      unfold per_func_eq, raise_ext_per, raise_ext_per_fam in *.
      introv.

      assert (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x) a a') as ea.
      {
        pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x))) as w.
        apply w; auto; eauto 4 with slow.
      }

      assert (eqa lib'1 (lib_extends_trans e1 (lib_extends_trans e0 x)) a a') as eb.
      { eapply lib_per_cond; eauto. }

      assert (eqa lib'1 (lib_extends_trans z x) a a') as ec.
      { eapply lib_per_cond; eauto. }

      pose proof (m2 _ _ ea) as m2.
      pose proof (m0 _ _ eb) as m0.
      fold (@nuprl o).

      apply nuprl_refl in m2.
      eapply type_extensionality_nuprl;[eauto|].
      introv; split; intro w; eauto;[exists ec; eapply lib_per_fam_cond; eauto|].
      exrepnd; eapply lib_per_fam_cond; eauto.
    }

    {

      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e0.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e2.
      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in e4.

      apply in_open_bar_ext_twice in e4.
      apply in_open_bar_ext_twice in e2.
      apply in_open_bar_ext_dup.
      eapply in_open_bar_ext_comb; try exact e0; clear e0.
      eapply in_open_bar_ext_comb; try exact e4; clear e4.
      eapply in_open_bar_ext_pres; try exact e2; clear e2; introv m2 m4 m0; simpl in *.
      unfold raise_ext_per_fam.
      unfold per_func_ext_eq in m0; simpl in m0.

      eapply in_open_bar_ext_comb; try exact m0; clear m0.
      eapply in_open_bar_ext_comb; try exact m4; clear m4.
      eapply in_open_bar_ext_pres; try exact m2; clear m2; introv m2 m4 m0; simpl in *.
      unfold per_func_eq, raise_ext_per, raise_ext_per_fam in *.
      introv.

      assert (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x) a a') as ea.
      {
        pose proof (equality_eq1 lib'1 A A a a' (eqa lib'1 (lib_extends_trans (lib_extends_trans e1 e0) x))) as w.
        apply w; auto; eauto 4 with slow.
      }

      assert (eqa lib'1 (lib_extends_trans e1 (lib_extends_trans e0 x)) a a') as eb.
      { eapply lib_per_cond; eauto. }

      assert (eqa lib'1 (lib_extends_trans z x) a a') as ec.
      { eapply lib_per_cond; eauto. }

      pose proof (m2 _ _ ea) as m2.
      pose proof (m0 _ _ eb) as m0.
      fold (@nuprl o).

      apply nuprl_refl in m2.
      exists ec; eapply lib_per_fam_cond; eauto.
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

Lemma type_extensionality_per_func_ext_nuprli {o} :
  forall i, @type_extensionality o (per_func_ext (nuprli i)).
Proof.
  introv per e.
  unfold per_func_ext in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_func_ext_nuprli : slow.

Lemma uniquely_valued_per_func_ext_nuprli {o} :
  forall i, @uniquely_valued o (per_func_ext (nuprli i)).
Proof.
  introv pera perb.
  unfold per_func_ext in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp perb3.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_function_implies in ceq.
  apply ccequivc_ext_mkc_function_implies in ceq0.
  repnd.

  apply implies_eq_term_equals_per_func_ext_eq.

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.

    eapply nuprli_value_respecting_left in pera4;[|apply ccequivc_ext_sym;eapply lib_extends_preserves_ccequivc_ext;eauto].

    apply nuprli_refl in pera4.
    apply nuprli_refl in perb4.
    eapply nuprli_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera0 _ e a a' u) as pera0.
    pose proof (perb0 _ e a a' v1) as perb0.
    simpl in *.

    eapply nuprli_value_respecting_left in pera0;[|apply ccequivc_ext_sym;eapply lib_extends_preserves_ccequivc_ext;try eapply bcequivc_ext_implies_ccequivc_ext;eauto].

    apply nuprli_refl in pera0.
    apply nuprli_refl in perb0.
    eapply nuprli_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_func_ext_nuprli : slow.

Lemma local_per_bar_per_func_ext_nuprli {o} :
  forall i, @local_ts o (per_bar (per_func_ext (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_func_ext_nuprli : slow.

Lemma dest_nuprli_per_func_l {o} :
  forall i (ts : cts(o)) lib T A v B T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_function {o} :
  forall i (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprli i lib (mkc_function A v B) (mkc_function C w D) eq
    -> per_bar (per_func_ext (nuprli i)) lib (mkc_function A v B) (mkc_function C w D) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_func_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma type_family_ext_nuprli_function_uniquely_valued_eqas {o} :
  forall i lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_function (nuprli i) lib (mkc_function A v B) (mkc_function C w D) eqa1 eqb1
    -> type_family_ext mkc_function (nuprli i) lib (mkc_function A v B) (mkc_function C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  unfold type_family_ext in *; exrepnd; spcast.
  repeat ccomputes_to_valc_ext_val.

  eapply in_ext_ext_nuprli_value_respecting_left  in tfa3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in tfa3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_left  in tfb3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in tfb3;[|apply ccequivc_ext_sym;eauto].

  introv.
  pose proof (tfa3 _ e) as tfa3.
  pose proof (tfb3 _ e) as tfb3.
  simpl in *.
  apply nuprli_refl in tfa3.
  apply nuprli_refl in tfb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.

(*Lemma bar_and_fam_per2lib_per_implies_lpaf_eqa_i {o} :
  forall {lib lib'} {bar : @BarLib o lib} {feqa : bar-and-fam-per(lib,bar,o)}
         {A v B C w D i}
         (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_function (nuprli i) lib2 (mkc_function A v B) (mkc_function C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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
  eapply type_family_ext_nuprli_function_uniquely_valued_eqas in q1; try exact q2.
  simpl in *.
  pose proof (q1 _ (lib_extends_refl lib')) as q1; simpl in *.
  apply q1; auto.
Qed.*)

(*Definition bar_and_fam_per2lib_per_fam_i {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-and-fam-per(lib,bar,o))
           {A v B C w D i}
           (F : forall lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib), type_family_ext mkc_function (nuprli i) lib2 (mkc_function A v B) (mkc_function C w D) (lpaf_eqa (feqa lib1 br lib2 ext x)) (lpaf_eqb (feqa lib1 br lib2 ext x)))
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

Lemma dest_nuprli_function2 {o} :
  forall i lib (eq : per(o)) A v B C w D,
    nuprli i lib (mkc_function A v B) (mkc_function C w D) eq
    ->
    exists (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq lib (per_func_ext_eq_bar_lib_per lib eqa eqb))
      # in_open_bar_ext lib (fun lib' x => nuprli i lib' A C (eqa lib' x))
      # in_open_bar_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprli i lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e)).
Proof.
  introv u.
  apply dest_nuprli_function in u.
  unfold per_bar in u; exrepnd.

  unfold per_func_ext in u1.
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
    apply implies_eq_term_equals_per_func_ext_eq; simpl.

    {
      repeat introv; simpl; unfold raise_ext_per; simpl.
      split; intro h.

      - exists lib' ext lib'0 xtb z e; auto.

      - exrepnd.
        pose proof (u2 _ ext1 _ ext2 extz) as u; exrepnd.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ z0) in u0.
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
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ e) in q0.
        apply (implies_type_family_ext_raise_lib_per _ _ _ _ z0) in xx0.
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

    pose proof (q3 _ (lib_extends_refl lib'0)) as q3; simpl in *.
    eapply nuprli_value_respecting_left in q3;[|apply ccequivc_ext_sym;eauto].
    eapply nuprli_value_respecting_right in q3;[|apply ccequivc_ext_sym;eauto].
    eapply nuprli_type_extensionality;[eauto|].

    split; intro h.

    - exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto.

    - exrepnd.
      pose proof (u2 _ ext1 _ ext2 extz) as u2; repnd.
      unfold type_family_ext in u1; exrepnd.
      repeat ccomputes_to_valc_ext_val.

      pose proof (u5 _ z0) as u5; simpl in *.
      apply nuprli_refl in u5.
      apply nuprli_refl in q3.
      eapply nuprli_value_respecting_left in u5;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprli_value_respecting_right in u5;[|eapply lib_extends_preserves_ccequivc_ext;[|apply ccequivc_ext_sym;eauto];auto].
      eapply nuprli_uniquely_valued in u5; try exact q3.
      apply u5; auto.
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
      apply dest_nuprli_function2 in teq1; exrepnd.
      exists (per_bar_eq lib' eqa0).
      apply CL_bar; exists eqa0; dands; auto.
    }

    {
      introv x ea.
      unfold equality, nuprl in teq; exrepnd.
      fold (@nuprl o) in *.

      applydup @dest_nuprl_uni in teq1.
      apply univ_implies_univi_bar3 in teq2; exrepnd.
      apply teq2 in teq0.

      exists (per_bar_eq lib' (univi_eq_lib_per lib' i)).
      dands; auto; eauto 2 with slow.

      {
        apply CL_init; exists (univi_eq_lib_per lib' i); dands; tcsp.
        apply in_ext_ext_implies_in_open_bar_ext; introv.
        exists (S i).
        apply univi_exists_iff; exists i; dands; spcast; tcsp; eauto 3 with slow.
      }

      apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in teq0.
      eapply in_open_bar_ext_pres; try exact teq0; clear teq0; introv teq0; simpl in *.
      unfold univi_eq in *.
      exrepnd.
      apply dest_nuprli_function2 in teq3; exrepnd.
      exists (per_bar_eq lib'0 (lib_per_fam2lib_per a a' eqb)).
      apply CL_bar; exists (lib_per_fam2lib_per a a' eqb); dands; tcsp;[]; simpl in *.
      fold (@nuprli o i) in *.

      eapply in_open_bar_ext_comb; try exact teq4; clear teq4.
      eapply in_open_bar_ext_pres; try exact teq3; clear teq3; introv teq4 teq3.

      assert (eqa0 lib'1 e0 a a') as xx.
      {
        pose proof (equality_eq1 lib'1 A1 A2 a a' (eqa0 lib'1 e0)) as w.
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

    pose proof (nuprli_monotone_func i lib' A1 A2 eqa eqa1) as tya; exrepnd.
    rename eq' into eqa'.

    assert (forall lib'',
               lib_extends lib'' lib' ->
               forall a a',
                 equality lib'' a a' A1 ->
                 equality lib'' (B1) [[v1 \\ a]] (B2) [[v2 \\ a']] (mkc_uni i)) as teq.
    { introv xt ea; eapply eqb; eauto 3 with slow. }
    clear eqb.

    eapply choice_ext_teqi in teq;[|introv;eapply nuprli_implies_nuprl;eapply tya0];[].
    exrepnd.
    rename eqb into eqb'.

    exists (per_func_ext_eq lib' eqa' eqb').
    apply CL_func; fold (@nuprli o i).
    exists eqa' eqb'.
    dands; auto;[].
    exists A1 A2 v1 v2 B1 B2; dands; spcast; eauto 3 with slow;[].

    introv; apply tya0.
Qed.
