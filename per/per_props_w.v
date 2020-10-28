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


Require Export per_props_util.
Require Export per_props_function.
Require Export list. (* WTF?? *)



Lemma type_extensionality_per_w_bar_nuprl {o} :
  @type_extensionality o (per_w_bar nuprl).
Proof.
  introv per e.
  unfold per_w_bar in *; exrepnd.
  exists eqa eqb; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_w_bar_nuprl : slow.

Lemma uniquely_valued_per_w_bar_nuprl {o} :
  @uniquely_valued o (per_w_bar nuprl).
Proof.
  introv pera perb.
  unfold per_w_bar in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold type_family_ext in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp pera3.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_w_implies in ceq.
  apply ccequivc_ext_mkc_w_implies in ceq0.
  repnd.

  apply implies_eq_term_equals_weq_bar.

  {
    introv.
    pose proof (pera5 _ e) as pera5.
    pose proof (perb5 _ e) as perb5.
    simpl in *.
    apply nuprl_refl in pera5.
    apply nuprl_refl in perb5.
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
Hint Resolve uniquely_valued_per_w_bar_nuprl : slow.

Lemma local_per_bar_per_w_bar_nuprl {o} :
  @local_ts o (per_bar (per_w_bar nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_w_bar_nuprl : slow.

Lemma dest_nuprl_per_w_l {o} :
  forall (ts : cts(o)) uk lib T A v B T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> close ts uk lib T T' eq
    -> per_bar (per_w_bar (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_w_bar_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_w {o} :
  forall uk (lib : @library o) (A : @CTerm o) v B C w D eq,
    nuprl uk lib (mkc_w A v B) (mkc_w C w D) eq
    -> per_bar (per_w_bar nuprl) uk lib (mkc_w A v B) (mkc_w C w D) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_w_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.




Lemma type_family_ext_nuprl_w_uniquely_valued_eqas {o} :
  forall uk lib A v B C w D (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    type_family_ext mkc_w nuprl uk lib (mkc_w A v B) (mkc_w C w D) eqa1 eqb1
    -> type_family_ext mkc_w nuprl uk lib (mkc_w A v B) (mkc_w C w D) eqa2 eqb2
    -> in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x)).
Proof.
  introv tfa tfb.
  eapply type_family_ext_nuprl_uniquely_valued_eqas; eauto; eauto 3 with slow.
Qed.



Lemma dest_nuprl_w2 {o} :
  forall uk lib (eq : per(o)) A v B C w D,
    nuprl uk lib (mkc_w A v B) (mkc_w C w D) eq
    ->
    exists (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
      eq <=2=> (per_bar_eq lib (weq_bar_lib_per lib eqa eqb))
      # in_open_bar_ext lib (fun lib' x => nuprl uk lib' A C (eqa lib' x))
      # in_open_bar_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), nuprl uk lib' (substc a v B) (substc a' w D) (eqb lib' x a a' e))
      # is_swap_invariant_cond uk eqa v B w D.
Proof.
  introv u.
  apply dest_nuprl_w in u.
  unfold per_bar in u; exrepnd.

  unfold per_w_bar in u1.
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
    apply implies_eq_term_equals_weq_bar; simpl.

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

Lemma implies_in_open_bar_ext_in_ext_ext {o} :
  forall (lib : @library o) (F : forall lib', lib_extends lib' lib -> Prop),
    in_open_bar_ext lib F
    -> in_open_bar_ext lib (fun lib' e => in_ext_ext lib' (fun lib'' e' => F lib'' (lib_extends_trans e' e))).
Proof.
  introv h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' y; introv xt; repeat introv.
  pose proof (h1 lib'1 (lib_extends_trans e xt)) as h1; simpl in h1; auto.
Qed.

Lemma equality_in_w {o} :
  forall u lib (s1 s2 : @CTerm o) A v B,
    equality u lib s1 s2 (mkc_w A v B)
    <=>
    {eqa : lib-per(lib,o)
     , {eqb :  lib-per-fam(lib,eqa,o)
        , in_open_bar_ext lib (fun lib e => nuprl u lib A A (eqa lib e))
        # in_open_bar_ext lib
             (fun lib x =>
                forall a a' (e : eqa lib x a a'),
                  nuprl u lib (substc a v B) (substc a' v B) (eqb lib x a a' e))
        # is_swap_invariant_cond u eqa v B v B
        # weq_bar lib eqa eqb s1 s2}}.
Proof.
  introv; sp_iff Case; introv e.

  - unfold equality in e; exrepnd.
    applydup @dest_nuprl_w2 in e1; exrepnd.
    apply e3 in e0.
    exists eqa eqb; dands; auto.

    { unfold per_bar_eq in *; simpl in *.
      apply in_open_bar_ext_dup; simpl in *.
      eapply in_open_bar_ext_pres; try exact e0; introv h.
      eapply in_open_bar_ext_pres; try exact h; introv q; introv.
      eapply implies_eq_term_equals_weq; try exact q.
      { unfold raise_lib_per, raise_ext_per; simpl; apply lib_per_cond. }
      { introv; unfold raise_lib_per_fam, raise_ext_per_fam; simpl; apply lib_per_fam_cond. } }

  - exrepnd.
    unfold equality.
    exists (per_bar_eq lib (weq_bar_lib_per lib eqa eqb)); dands; tcsp.

    { apply CL_bar.
      exists (weq_bar_lib_per lib eqa eqb); dands; tcsp.
      apply implies_in_open_bar_ext_in_ext_ext in e0.
      apply implies_in_open_bar_ext_in_ext_ext in e2.
      eapply in_open_bar_ext_comb; try exact e0; clear e0.
      eapply in_open_bar_ext_pres; try exact e2; clear e2.
      introv e2 e0.
      apply CL_w; simpl.
      exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e).
      dands; tcsp; eauto 3 with slow.
      exists A A v v B B; sp; spcast; eauto 2 with slow. }

    apply per_bar_eq_weq_bar_lib_per; auto.
Qed.

Lemma weq_implies {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> forall t1 t2,
         weq lib eqa1 eqb1 t1 t2
         -> weq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqia eqib weq1.
  induction weq1.

  assert (eqa2 a a') as ea2 by (allrw <-; sp).

  apply @weq_cons
        with
        (a  := a)
        (f  := f)
        (a' := a')
        (f' := f')
        (e  := ea2);
    try (complete sp).

  introv eia.

  apply_hyp.
  generalize (eqib a a' e ea2); intro eqt; allrw; sp.
Qed.


Lemma eq_term_equals_weq {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> eq_term_equals (weq lib eqa1 eqb1)
                      (weq lib eqa2 eqb2).
Proof.
  introv eqia eqib.
  eapply implies_eq_term_equals_weq; eauto.
Qed.

Lemma tequality_mkc_w {p} :
  forall u lib (A1 : @CTerm p) v1 B1
         A2 v2 B2,
    tequality u lib
      (mkc_w A1 v1 B1)
      (mkc_w A2 v2 B2)
    <=>
    (tequality u lib A1 A2
     # equality_swap_invariant_cond u lib A1 v1 B1 v2 B2
     # in_ext lib (fun lib => forall a1 a2,
        equality u lib a1 a2 A1
        -> tequality u lib (substc a1 v1 B1) (substc a2 v2 B2))).
Proof.
  introv; split; intro e; repnd.

  - unfold tequality in e; exrepnd.
    apply dest_nuprl_w2 in e0; exrepnd.

    dands; eauto 3 with slow.
    introv ext equ.

    eapply (lib_extends_preserves_in_open_bar_ext _ _ _ ext) in e2.
    eapply (lib_extends_preserves_in_open_bar_ext _ _ _ ext) in e3.

    eapply all_in_ex_bar_tequality_implies_tequality.
    eapply in_open_bar_comb2; try exact e3; clear e3.
    eapply in_open_bar_ext_pres; try exact e2; clear e2.
    introv e2 e3.
    eapply equality_monotone in equ; eauto.
    eapply equality_eq1 in e2; apply e2 in equ; clear e2.
    pose proof (e3 _ _ equ) as e3.
    eexists; eauto.

  - assert (forall lib', lib_extends lib' lib -> tequality u lib' A1 A2) as teqa by eauto 3 with slow.
    clear e0.

    rename e into teqb.

    unfold tequality in *.

    apply choice_ext_lib_teq in teqa; exrepnd.
    eapply choice_ext_lib_teq_fam in teqb;[|eauto]; exrepnd.

    exists (weq_bar lib eqa eqb).
    apply CL_w.
    exists eqa eqb.
    dands; eauto 3 with slow.
    exists A1 A2 v1 v2 B1 B2.
    dands; spcast; eauto 3 with slow;
      try (complete (eapply equality_swap_invariant_cond_nuprl_imp; eauto;
                     introv; apply teqa0)).
Qed.

Lemma equality_in_w_v1 {p} :
  forall u lib A v B (t1 t2 : @CTerm p),
    equality u lib t1 t2 (mkc_w A v B)
    <=> in_open_bar
          lib
          (fun lib =>
             {a1, a2, f1, f2 : CTerm
             , t1 ===>(lib) (mkc_sup a1 f1)
             # t2 ===>(lib) (mkc_sup a2 f2)
             # equality u lib a1 a2 A
             # equality u lib f1 f2 (mkc_fun (substc a1 v B) (mkc_w A v B))})
         # type u lib A
         # equality_swap_invariant_cond u lib A v B v B
         # in_ext_ext lib (fun lib e => forall a a', equality u lib a a' A -> tequality u lib (substc a v B) (substc a' v B)).
Proof.
  introv; split; intro e.

  - applydup @inhabited_implies_tequality in e as teq.
    apply equality_in_w in e; exrepnd.
    dands; auto.

    { eapply in_open_bar_comb; try exact e1; clear e1.
      eapply in_open_bar_comb; try exact e0; clear e0.
      eapply in_open_bar_pres; try exact e2; clear e2.
      introv xt e2 e0 e1.

      pose proof (e0 xt) as e0'.
      pose proof (e2 xt) as e2'.
      pose proof (e1 xt) as e1'.

      inversion e1'.
      eexists; eexists; eexists; eexists; dands; eauto.

      { exists (eqa lib' xt); dands; auto. }

      pose proof (e2' _ _ e) as e2'.
      apply equality_in_fun; dands; eauto 3 with slow.

      { apply nuprl_refl in e2'.
        eexists; eauto. }

      introv xt' equ.


XXXXXXXXXXXXX

        apply tequality_mkc_w; dands; eauto 3 with slow.

        { eapply nuprl_monotone_func in e0; exrepnd.
          pose proof (e4 _ xt') as e4; repnd.
          eexists; eauto. }

        { SearchAbout equality_swap_invariant_cond is_swap_invariant_cond.

SearchAbout equality mkc_fun.
      exists (eqb lib' xt a a' e); dands; auto.
      

 unfold equality in e; exrepnd.
    apply dest_nuprl_w2 in e1; exrepnd.


    inversion e1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    destruct h.
    exists a a' f f'; sp.
    exists eqa; sp.
    rw <- @fold_mkc_fun.
    rw @equality_in_function; dands.

    exists (eqb a a' e).
    apply @nuprl_refl with (t2 := substc a' v0 B0); sp.

    intros b1 b2 eib.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover.
    allrw @substc_cnewvar.
    exists eq; sp.

    intros b1 b2 eib.
    allrw @substc_cnewvar.
    exists eq; sp.
    allrw.
    apply_hyp.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover; sp.

    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib A0 eq0 eqa); introv k; repeat (dest_imp k hyp).
    assert (eqa a0 a'0) as ea by (allrw <-; sp).
    exists (eqb a0 a'0 ea); sp.

  - exrepnd.
    unfold equality in e3; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A v B v B e1); intro n; exrepnd.

    exists (weq lib eqa (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3))); dands.

    apply CL_w; unfold per_w.
    exists eqa.
    exists (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3)); sp.
    unfold type_family.
    fold (@nuprl p lib).
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).

    apply @weq_cons with (a := a1) (f := f1) (a' := a2) (f' := f2) (e := e5); sp.
    generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); intro n.
    rw <- @fold_mkc_fun in e4.
    rw @equality_in_function in e4; repnd.
    generalize (e4 b b'); intro k.
    dest_imp k hyp.
    exists (f a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); sp.
    allapply @nuprl_refl; sp.
    allrw @substc_cnewvar.
    unfold equality in k; exrepnd.
    inversion k1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd; allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.

    assert (eq_term_equals eqa0 eqa)
           as eqta by (eapply nuprl_uniquely_valued; eauto).

    assert (forall (a a' : CTerm) (ea : eqa a a') (ea' : eqa0 a a'),
              eq_term_equals (f a a' (eq_equality1 lib a a' A0 eqa ea e3)) (eqb a a' ea'))
           as eqtb.
    introv.
    generalize (n0 a a' (eq_equality1 lib a a' A0 eqa ea e3)); intro n1.
    assert (nuprl lib (substc a v0 B0) (substc a' v0 B0) (eqb a a' ea')) as n2 by sp.
    apply (nuprl_uniquely_valued lib) with (t := substc a v0 B0); sp; allapply @nuprl_refl; sp.
    apply weq_implies with (eqa1 := eqa0) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.
Qed.


(**

  Using the Coq induction principle we obtain for [weq], we can prove
  the following induction principle for our W types.  The then use
  this principle to prove the [rule_w_induction] rule below.

*)

Lemma w_ind_eq {p} :
  forall u (lib : library) (A : @CTerm p) va B (Q : CTerm -> CTerm -> [U]),
    (forall t1 t2 t3 t4, cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q t1 t2 -> Q t3 t4)
    -> (forall a1 a2 f1 f2,
          equality u lib a1 a2 A
          -> equality u lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality u lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1) (mkc_apply f2 b2))
          -> Q (mkc_sup a1 f1) (mkc_sup a2 f2))
    -> (forall w1 w2, equality u lib w1 w2 (mkc_w A va B) -> Q w1 w2).
Proof.
  introv ceq ind e.
  rw @equality_in_w in e; exrepnd.
  induction e1; spcast.
  apply ceq with (t1 := mkc_sup a f) (t2 := mkc_sup a' f');
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa a' a')
         as e'
         by (eapply equality_eq_refl; eauto;
             eapply equality_eq_sym; eauto).

  apply ind; try (complete (exists eqa; sp)).

  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb a a' e); sp.
  generalize (e2 a a' e); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  introv eq.
  allrw @substc_cnewvar.
  exists (weq lib eqa eqb); sp.
  apply CL_w; unfold per_w; unfold type_family.
  exists eqa eqb; sp.
  exists A A va va B B; sp; spcast; apply computes_to_valc_refl; apply iscvalue_mkc_w.

  (* 3 *)
  introv eq.
  allrw @substc_cnewvar.
  rw @equality_in_w.
  exists eqa eqb; sp.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).

  (* 4 *)
  introv eq.
  apply_hyp; sp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).
Qed.

(* begin hide *)

Lemma w_ind_eq2 {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> [U]),
    (forall t1 t2, cequivc lib t1 t2 -> Q t1 -> Q t2)
    -> (forall a1 a2 f1 f2,
          equality lib a1 a2 A
          -> equality lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1))
          -> Q (mkc_sup a1 f1))
    -> (forall w1 w2, equality lib w1 w2 (mkc_w A va B) -> Q w1).
Proof.
  introv ceq ind e.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)).
  intro h.
  dest_imp h hyp.
  introv c1 c2 q1.
  apply ceq with (t1 := t1); sp.
  apply h with (w2 := w2); sp.
Qed.

Lemma w_ind {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> Prop),
    (forall t t', cequivc lib t t' -> Q t -> Q t')
    -> (forall a f,
          member lib a A
          -> member lib f (mkc_fun (substc a va B) (mkc_w A va B))
          -> Q (mkc_sup a f))
    -> (forall w, member lib w (mkc_w A va B) -> Q w).
Proof.
  introv ceq ind m.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)); intro i.
  apply i with (w2 := w); sp.
  apply ceq with (t := t1); sp.
  apply ind; allapply @equality_refl; sp.
Qed.

