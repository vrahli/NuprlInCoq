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


Require Export natk2.
Require Export terms_union.
Require Export cequiv_props.
Require Export per_props_cequiv.
Require Export per_props_uni.



Lemma type_extensionality_per_union_nuprl {o} :
  @type_extensionality o (per_union nuprl).
Proof.
  introv per e.
  unfold per_union in *; exrepnd.
  exists eqa eqb A1 A2 B1 B2; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_union_nuprl : slow.

Lemma type_extensionality_per_union_nuprli {o} :
  forall i, @type_extensionality o (per_union (nuprli i)).
Proof.
  introv per e.
  unfold per_union in *; exrepnd.
  exists eqa eqb A1 A2 B1 B2; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_union_nuprli : slow.

Lemma uniquely_valued_per_union_nuprl {o} :
  @uniquely_valued o (per_union nuprl).
Proof.
  introv pera perb.
  unfold per_union in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  spcast; repeat computes_to_eqval.

  apply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib));
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
    introv.

  {
    introv.
    pose proof (pera3 _ e) as pera3.
    pose proof (perb3 _ e) as perb3.
    simpl in *.
    apply nuprl_refl in pera3.
    apply nuprl_refl in perb3.
    eapply nuprl_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprl_refl in pera4.
    apply nuprl_refl in perb4.
    eapply nuprl_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_union_nuprl : slow.

Lemma uniquely_valued_per_union_nuprli {o} :
  forall i, @uniquely_valued o (per_union (nuprli i)).
Proof.
  introv pera perb.
  unfold per_union in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  spcast; repeat computes_to_eqval.

  apply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib));
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
    introv.

  {
    introv.
    pose proof (pera3 _ e) as pera3.
    pose proof (perb3 _ e) as perb3.
    simpl in *.
    apply nuprli_refl in pera3.
    apply nuprli_refl in perb3.
    eapply nuprli_uniquely_valued; eauto.
  }

  {
    introv.
    pose proof (pera4 _ e) as pera4.
    pose proof (perb4 _ e) as perb4.
    simpl in *.
    apply nuprli_refl in pera4.
    apply nuprli_refl in perb4.
    eapply nuprli_uniquely_valued; eauto.
  }
Qed.
Hint Resolve uniquely_valued_per_union_nuprli : slow.

Lemma local_per_bar_per_union_nuprl {o} :
  @local_ts o (per_bar (per_union nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_union_nuprl : slow.

Lemma local_per_bar_per_union_nuprli {o} :
  forall i, @local_ts o (per_bar (per_union (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_union_nuprli : slow.

Lemma dest_nuprl_per_union_l {o} :
  forall (ts : cts(o)) lib T A B T' eq,
    ts = univ
    -> computes_to_valc lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union_nuprl; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_union_l {o} :
  forall i (ts : cts(o)) lib T A B T' eq,
    ts = univi_bar i
    -> computes_to_valc lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union_nuprli; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_union {o} :
  forall (lib : @library o) A1 A2 B1 B2 eq,
    nuprl lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    -> per_bar (per_union nuprl) lib (mkc_union A1 B1) (mkc_union A2 B2) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_union_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_union {o} :
  forall i (lib : @library o) A1 A2 B1 B2 eq,
    nuprli i lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    -> per_bar (per_union (nuprli i)) lib (mkc_union A1 B1) (mkc_union A2 B2) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_union_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Record two_lib_per {o} {lib} :=
  MkTwoLibPer
    {
      tlp_eqa : lib-per(lib,o);
      tlp_eqb : lib-per(lib,o);
    }.

Notation "bar-two-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib),
      @two_lib_per o lib2).

Lemma all_in_bar_ext_exists2_lib_per_implies_exists2 {o} :
  forall {lib} (bar : @BarLib o lib)
         (F : forall lib' (x : lib_extends lib' lib) (eqa eqb : lib-per(lib',o)), Prop),
    all_in_bar_ext bar (fun lib' x => {eqa , eqb : lib-per(lib',o) , F lib' x eqa eqb})
    ->
    exists (feqa : bar-two-lib-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 x (tlp_eqa (feqa lib1 br lib2 ext x)) (tlp_eqb (feqa lib1 br lib2 ext x)).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => @two_lib_per o (plb_lib2 _ x))
                (fun x e => F (plb_lib2 _ x)
                              (plb_x _ x)
                              (tlp_eqa e)
                              (tlp_eqb e))) as C.
  simpl in C.
  repeat (autodimp C hyp).

  { introv; destruct x; simpl in *.
    pose proof (h _ plb_br _ plb_ext plb_x) as h; simpl in *; exrepnd.
    exists (MkTwoLibPer _ _ eqa eqb); simpl; auto. }

  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

Definition bar_two_lib_per2lib_pera {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-two-lib-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {x : lib_extends lib' lib
            , tlp_eqa (feqa lib1 br lib' ext x) lib' (lib_extends_refl lib') t1 t2}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br ext x0; auto.
  - exists lib1 br ext x0; auto.
Defined.

Definition bar_two_lib_per2lib_perb {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-two-lib-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {x : lib_extends lib' lib
            , tlp_eqb (feqa lib1 br lib' ext x) lib' (lib_extends_refl lib') t1 t2}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br ext x0; auto.
  - exists lib1 br ext x0; auto.
Defined.

Lemma dest_nuprl_union2 {o} :
  forall lib (eq : per(o)) A1 A2 B1 B2,
    nuprl lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    ->
    exists (bar : BarLib lib) (eqa eqb : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_union_eq_bar_lib_per lib eqa eqb)))
        # all_in_bar_ext bar (fun lib' x => nuprl lib' A1 A2 (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => nuprl lib' B1 B2 (eqb lib' x)).
Proof.
  introv u.
  apply dest_nuprl_union in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 , eqb : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A1 A2 (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => nuprl lib'' B1 B2 (eqb lib'' y))
               # (eqa lib' x) <=2=> (per_union_eq_bar lib' eqa0 eqb) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_union in *; exrepnd.
    spcast; computes_to_value_isvalue.
    exists eqa0 eqb; dands; auto.
  }
  clear u0.

  apply all_in_bar_ext_exists2_lib_per_implies_exists2 in e; exrepnd.
  exists bar (bar_two_lib_per2lib_pera feqa) (bar_two_lib_per2lib_perb feqa).

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
    apply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'0));
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
      introv; simpl; unfold raise_ext_per.

    {
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
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        pose proof (u1 _ e) as u1; simpl in *.

        pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        exrepnd; spcast.
        pose proof (q1 _ (lib_extends_refl lib'1)) as q1; simpl in *.
        apply nuprl_refl in q1.
        apply nuprl_refl in u1.
        eapply nuprl_uniquely_valued in q1; try exact u1.
        apply q1; auto.

      - exrepnd.
        pose proof (u1 _ e) as u1; simpl in *.

        pose proof (e0 lib1 br0 _ ext0 x0) as q; repnd.
        pose proof (q1 _ (lib_extends_refl lib'1)) as q1; simpl in *.
        apply nuprl_refl in q1.
        apply nuprl_refl in u1.
        eapply nuprl_uniquely_valued in q1; try exact u1.
        apply q1; auto.
    }
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
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h1 _ (lib_extends_refl lib'0)) as h1; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e2 _ (lib_extends_refl lib'0)) as e2; simpl in *.
      apply nuprl_refl in e2.
      apply nuprl_refl in h1.
      eapply nuprl_uniquely_valued in e2; try exact h1.
      apply e2; auto.
  }
Qed.

Lemma dest_nuprli_union2 {o} :
  forall i lib (eq : per(o)) A1 A2 B1 B2,
    nuprli i lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    ->
    exists (bar : BarLib lib) (eqa eqb : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar (per_union_eq_bar_lib_per lib eqa eqb)))
        # all_in_bar_ext bar (fun lib' x => nuprli i lib' A1 A2 (eqa lib' x))
        # all_in_bar_ext bar (fun lib' x => nuprli i lib' B1 B2 (eqb lib' x)).
Proof.
  introv u.
  apply dest_nuprli_union in u.
  unfold per_bar in u; exrepnd.

  assert (all_in_bar_ext
            bar
            (fun lib' x =>
               {eqa0 , eqb : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A1 A2 (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => nuprli i lib'' B1 B2 (eqb lib'' y))
               # (eqa lib' x) <=2=> (per_union_eq_bar lib' eqa0 eqb) })) as e.
  {
    introv br ext; introv.
    pose proof (u0 _ br _ ext x) as u0; simpl in *.
    unfold per_union in *; exrepnd.
    spcast; computes_to_value_isvalue.
    exists eqa0 eqb; dands; auto.
  }
  clear u0.

  apply all_in_bar_ext_exists2_lib_per_implies_exists2 in e; exrepnd.
  exists bar (bar_two_lib_per2lib_pera feqa) (bar_two_lib_per2lib_perb feqa).

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
    apply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'0));
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
      introv; simpl; unfold raise_ext_per.

    {
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
      split; intro h.

      - exists lib' br (lib_extends_trans e ext) (lib_extends_trans e x).
        pose proof (u1 _ e) as u1; simpl in *.

        pose proof (e0 lib' br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as q.
        exrepnd; spcast.
        pose proof (q1 _ (lib_extends_refl lib'1)) as q1; simpl in *.
        apply nuprli_refl in q1.
        apply nuprli_refl in u1.
        eapply nuprli_uniquely_valued in q1; try exact u1.
        apply q1; auto.

      - exrepnd.
        pose proof (u1 _ e) as u1; simpl in *.

        pose proof (e0 lib1 br0 _ ext0 x0) as q; repnd.
        pose proof (q1 _ (lib_extends_refl lib'1)) as q1; simpl in *.
        apply nuprli_refl in q1.
        apply nuprli_refl in u1.
        eapply nuprli_uniquely_valued in q1; try exact u1.
        apply q1; auto.
    }
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
    introv br ext; introv.
    pose proof (e0 _ br _ ext x) as h; simpl in *; repnd.
    pose proof (h1 _ (lib_extends_refl lib'0)) as h1; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    clear h.

    split; intro h.

    - exists lib' br ext x; auto.

    - exrepnd.
      pose proof (e0 _ br0 _ ext0 x0) as e0; repnd.
      pose proof (e2 _ (lib_extends_refl lib'0)) as e2; simpl in *.
      apply nuprli_refl in e2.
      apply nuprli_refl in h1.
      eapply nuprli_uniquely_valued in e2; try exact h1.
      apply e2; auto.
  }
Qed.




Lemma tequality_mkc_union {p} :
  forall lib (A1 B1 A2 B2 : @CTerm p),
    tequality lib (mkc_union A1 B1) (mkc_union A2 B2)
    <=> (tequality lib A1 A2 # tequality lib B1 B2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    apply dest_nuprl_union2 in teq0; exrepnd.
    dands; eauto 3 with slow.

  - unfold tequality in teq0; exrepnd.
    rename eq into eqa.
    unfold tequality in teq; exrepnd.
    rename eq into eqb.

    pose proof (nuprl_monotone_func lib A1 A2 eqa teq1) as tya; exrepnd.
    rename eq' into eqa'.
    pose proof (nuprl_monotone_func lib B1 B2 eqb teq0) as tyb; exrepnd.
    rename eq' into eqb'.

    exists (per_union_eq_bar lib eqa' eqb'); apply CL_union; unfold per_union.
    exists eqa' eqb' A1 A2 B1 B2; sp; spcast;
      try (apply computes_to_valc_refl; apply iscvalue_mkc_union); eauto 3 with slow.
    { introv; apply tya0. }
    { introv; apply tyb0. }
Qed.

Lemma tequality_mkc_or {p} :
  forall lib (A1 B1 A2 B2 : @CTerm p),
    tequality lib (mkc_or A1 B1) (mkc_or A2 B2)
    <=> (tequality lib A1 A2 # tequality lib B1 B2).
Proof.
  introv; rw @tequality_mkc_union; sp.
Qed.

Lemma per_bar_eq_per_union_eq_bar_lib_per_iff {o} :
  forall {lib} (bar : @BarLib o lib) (eqa eqb : lib-per(lib,o)) p1 p2,
    (per_bar_eq bar (per_union_eq_bar_lib_per lib eqa eqb) p1 p2)
      <=>
      exists bar,
        all_in_bar_ext
          bar
          (fun lib' x => per_union_eq lib' (eqa lib' x) (eqb lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_union_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    unfold per_bar_eq in *; simpl in *.
    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.

    apply collapse2bars_ext; simpl.
    { introv; apply implies_eq_term_equals_per_union_eq;
        try (apply lib_per_cond);
        try (introv; apply lib_per_fam_cond). }
    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.
    unfold per_union_eq_bar in h0; exrepnd.
    exists bar0; simpl in *.
    unfold raise_ext_per in *.

    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.
    eapply implies_eq_term_equals_per_union_eq; try exact h1;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).

  - unfold per_bar_eq; exrepnd.
    introv br ext; introv.
    exists (raise_bar bar0 x).
    introv br' ext'; introv; simpl in *; exrepnd.
    exists (trivial_bar lib'2).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h0 _ br'1 lib'3 (lib_extends_trans (lib_extends_trans e ext') br'2) (lib_extends_trans (lib_extends_trans e x0) x)) as h0; simpl in *.

    eapply implies_eq_term_equals_per_union_eq; try exact h0;
      try (apply lib_per_cond);
      try (introv; apply lib_per_fam_cond).
Qed.

Lemma equality_mkc_union {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_union A B)
    <=> (type lib A
         # type lib B
         # all_in_ex_bar lib (fun lib => {a1, a2 : CTerm
             , t1 ===>(lib) (mkc_inl a1)
             # t2 ===>(lib) (mkc_inl a2)
             # equality lib a1 a2 A}
            {+}
            {b1, b2 : CTerm
             , t1 ===>(lib) (mkc_inr b1)
             # t2 ===>(lib) (mkc_inr b2)
             # equality lib b1 b2 B})).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_union2 in e1; exrepnd.
    apply e1 in e0.
    clear dependent eq.
    dands; eauto 3 with slow;[].

    apply per_bar_eq_per_union_eq_bar_lib_per_iff in e0; exrepnd.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in e3.
    apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in e2.
    apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in e1.
    remember (intersect_bars bar bar0) as b.
    clear dependent bar.
    clear dependent bar0.
    exists b.
    introv br ext.
    assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
    pose proof (e3 _ br _ ext xt) as e3; simpl in *.
    pose proof (e2 _ br _ ext xt) as e2; simpl in *.
    pose proof (e1 _ br _ ext xt) as e1; simpl in *.

    unfold per_union_eq in *.
    repndors; [left|right].

    + unfold per_union_eq_L in *; exrepnd; eexists; eexists; dands; eauto.
      apply (equality_eq1 lib'0 A A x y (eqa lib'0 xt)); auto.

    + unfold per_union_eq_R in *; exrepnd; eexists; eexists; dands; eauto.
      apply (equality_eq1 lib'0 B B x y (eqb lib'0 xt)); auto.

  - exrepnd.
    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; spcast.

    eapply meta_type_monotone in e0;[|exact x].
    eapply meta_type_monotone in e1;[|exact x].
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.
    unfold type, tequality in e1; exrepnd.
    rename eq into eqb.

    pose proof (nuprl_monotone_func lib' A A eqa e2) as tya; exrepnd.
    rename eq' into eqa'.
    pose proof (nuprl_monotone_func lib' B B eqb e0) as tyb; exrepnd.
    rename eq' into eqb'.

    exists (per_union_eq_bar lib' eqa' eqb'); dands.

    {
      apply CL_union; unfold per_union.
      exists eqa' eqb' A A B B; dands; spcast;
        try (apply computes_to_valc_refl; apply iscvalue_mkc_union); eauto 3 with slow.
      { introv; apply tya0. }
      { introv; apply tyb0. }
    }

    exists (trivial_bar lib').
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.

    repndors;[left|right]; exrepnd; spcast.

    + eapply lib_extends_preserves_computes_to_valc in e3;[|exact e1].
      eapply lib_extends_preserves_computes_to_valc in e5;[|exact e1].
      eexists; eexists; dands; spcast; eauto.
      apply (equality_eq1 lib'0 A A a1 a2 (eqa' lib'0 e1)); eauto 3 with slow.
      eapply tya0.

    + eapply lib_extends_preserves_computes_to_valc in e3;[|exact e1].
      eapply lib_extends_preserves_computes_to_valc in e5;[|exact e1].
      eexists; eexists; dands; spcast; eauto.
      apply (equality_eq1 lib'0 B B b1 b2 (eqb' lib'0 e1)); eauto 3 with slow.
      eapply tyb0.
Qed.

Lemma equality_mkc_or {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_or A B)
    <=> (type lib A
         # type lib B
         # all_in_ex_bar lib (fun lib => {a1, a2 : CTerm
             , t1 ===>(lib) (mkc_inl a1)
             # t2 ===>(lib) (mkc_inl a2)
             # equality lib a1 a2 A}
            {+}
            {b1, b2 : CTerm
             , t1 ===>(lib) (mkc_inr b1)
             # t2 ===>(lib) (mkc_inr b2)
             # equality lib b1 b2 B})).
Proof.
  introv; rw @equality_mkc_union; sp.
Qed.

Lemma tequality_bool {o} :
  forall lib, @tequality o lib mkc_bool mkc_bool.
Proof.
  introv.
  allrw <- @fold_mkc_bool.
  rw @tequality_mkc_union; dands; eauto 3 with slow.
Qed.

Lemma implies_equality_in_unit {o} :
  forall lib (a b : @CTerm o),
    a ===>(lib) mkc_axiom
    -> b ===>(lib) mkc_axiom
    -> equality lib a b mkc_unit.
Proof.
  introv ca cb.
  apply equality_in_unit.
  apply in_ext_implies_all_in_ex_bar; introv x; dands; spcast; eauto 3 with slow.
Qed.

Lemma equality_in_bool {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_bool
    <=>
    all_in_ex_bar lib (fun lib =>
      (a ~=~(lib) tt # b ~=~(lib) tt)
      {+}
      (a ~=~(lib) ff # b ~=~(lib) ff)
    ).
Proof.
  introv.
  allrw <- @fold_mkc_bool.
  rw @equality_mkc_union; split; intro k; repnd; dands; eauto 3 with slow;[|].

  - apply collapse_all_in_ex_bar.
    eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast.
    exrepnd; repndors; exrepnd; spcast.

    + allrw @equality_in_unit; repnd.
      eapply all_in_ex_bar_modus_ponens1;try exact k3; clear k3; introv y k3; exrepnd; spcast.
      eapply lib_extends_preserves_computes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_computes_to_valc in k4;[|exact y].
      left; dands; spcast.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib'0 a (mkc_inl a1) tt); auto.
        apply cequivc_mkc_inl_if; auto.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib'0 b (mkc_inl a2) tt); auto.
        apply cequivc_mkc_inl_if; auto.

    + allrw @equality_in_unit; repnd.
      eapply all_in_ex_bar_modus_ponens1;try exact k3; clear k3; introv y k3; exrepnd; spcast.
      eapply lib_extends_preserves_computes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_computes_to_valc in k4;[|exact y].
      right; dands; spcast.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib'0 a (mkc_inr b1) ff); auto.
        apply cequivc_mkc_inr_if; auto.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib'0 b (mkc_inr b2) ff); auto.
        apply cequivc_mkc_inr_if; auto.

  - eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast.
    repndors; repnd; spcast;[left|right].

    + apply cequivc_sym in k0.
      apply cequivc_sym in k.
      apply cequivc_mkc_inl_implies in k0.
      apply cequivc_mkc_inl_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply implies_equality_in_unit; spcast; apply cequivc_axiom_implies; sp.

    + apply cequivc_sym in k0.
      apply cequivc_sym in k.
      apply cequivc_mkc_inr_implies in k0.
      apply cequivc_mkc_inr_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply implies_equality_in_unit; spcast; apply cequivc_axiom_implies; sp.
Qed.


Lemma substc_mkcv_ite {o} :
  forall v (t a b : @CTerm o),
    substc t v (mkcv_ite [v] (mkc_var v) (mk_cv [v] a) (mk_cv [v] b))
    = mkc_ite t a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold mk_ite, subst.
  change_to_lsubst_aux4; simpl.

  {
    pose proof (newvar_prog x1 i1) as e1.
    pose proof (newvar_prog x0 i0) as e2.
    pose proof (newvar_prog x i) as e3.
    rw e2; rw e3.
    boolvar; allrw @lsubst_aux_nil; sp.
    allrw @lsubst_aux_trivial; auto.

    {
      introv k; simpl in k; dorn k; cpx.
      dands; auto.
      apply isprogram_eq; sp.
      intro k.
      rw @isprog_eq in i.
      destruct i as [c w]; rw c in k; allsimpl; sp.
    }

    {
      introv k; simpl in k; dorn k; cpx.
      dands; auto.
      apply isprogram_eq; sp.
      intro k.
      rw @isprog_eq in i0.
      destruct i0 as [c w]; rw c in k; allsimpl; sp.
    }
  }

  {
    allrw app_nil_r.
    rw @isprog_eq in i1.
    destruct i1 as [c w]; rw c; sp.
  }
Qed.

Lemma mkc_ite_ceq_tt {o} :
  forall lib (a A B : @CTerm o),
    cequivc lib a tt
    -> cequivc lib (mkc_ite a A B) A.
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_trans with (b := mk_decide (mk_inl mk_axiom) nvarx x0 nvarx x).

  {
    allunfold @mk_decide.
    applydup @cequiv_isprogram in ceq; repnd.
    repeat(prove_cequiv); auto.

    {
      unfold blift; exists [nvarx] x0 x0; dands; auto.
      apply olift_approx_cequiv; sp;apply approx_open_refl;
        rw @isprog_eq in i0; destruct i0 as [c w]; sp.
    }

    {
      unfold blift; exists [nvarx] x x; dands; auto.
      apply olift_approx_cequiv; sp;apply approx_open_refl;
        rw @isprog_eq in i; destruct i as [c w]; sp.
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor.
        rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor.
        rw @isprog_eq in i; destruct i as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor.
        rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor.
        rw @isprog_eq in i; destruct i as [c w]; sp. }
    }
  }

  {
    apply reduces_to_implies_cequiv.

    {
      apply isprogram_decide; sp.
      { apply isprogram_inl; sp. }
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp. }
      { rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
      { rw @isprog_eq in i; destruct i as [c w]; rw c; sp. }
      { rw @isprog_eq in i; destruct i as [c w]; sp. }
    }

    {
      apply reduces_to_if_step; simpl.
      csunf; simpl.
      unfold apply_bterm; simpl.
      rw @lsubst_trivial; auto.
      introv k; simpl in k; dorn k; cpx.
      rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp.
    }
  }
Qed.

Lemma mkc_ite_ceq_ff {o} :
  forall lib (a A B : @CTerm o),
    cequivc lib a ff
    -> cequivc lib (mkc_ite a A B) B.
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_trans with (b := mk_decide (mk_inr mk_axiom) nvarx x0 nvarx x).

  {
    allunfold @mk_decide.
    applydup @cequiv_isprogram in ceq; repnd.
    repeat(prove_cequiv); auto.

    {
      unfold blift; exists [nvarx] x0 x0; dands; auto.
      apply olift_approx_cequiv; sp;apply approx_open_refl;
        rw @isprog_eq in i0; destruct i0 as [c w]; sp.
    }

    {
      unfold blift; exists [nvarx] x x; dands; auto.
      apply olift_approx_cequiv; sp;apply approx_open_refl;
        rw @isprog_eq in i; destruct i as [c w]; sp.
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor; rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor; rw @isprog_eq in i; destruct i as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor; rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
    }

    {
      constructor; unfold closed_bt; simpl.
      { rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp. }
      { constructor; rw @isprog_eq in i; destruct i as [c w]; sp. }
    }
  }

  {
    apply reduces_to_implies_cequiv.

    {
      apply isprogram_decide; sp.
      { apply isprogram_inr; sp. }
      { rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp. }
      { rw @isprog_eq in i0; destruct i0 as [c w]; sp. }
      { rw @isprog_eq in i; destruct i as [c w]; rw c; sp. }
      { rw @isprog_eq in i; destruct i as [c w]; sp. }
    }

    {
      apply reduces_to_if_step; simpl.
      csunf; simpl.
      unfold apply_bterm; simpl.
      rw @lsubst_trivial; auto.
      introv k; simpl in k; dorn k; cpx.
      rw @isprog_eq in i; destruct i as [c w]; rw c; sp.
    }
  }
Qed.

Lemma mkc_ite_tt {o} :
  forall lib (A B : @CTerm o),
    cequivc lib (mkc_ite tt A B) A.
Proof.
  introv.
  apply mkc_ite_ceq_tt; sp.
Qed.

Lemma mkc_ite_ff {o} :
  forall lib (A B : @CTerm o),
    cequivc lib (mkc_ite ff A B) B.
Proof.
  introv.
  apply mkc_ite_ceq_ff; sp.
Qed.

Lemma member_in_bool {o} :
  forall lib (a : @CTerm o),
    member lib a mkc_bool
    <=>
    all_in_ex_bar lib (fun lib => a ~=~(lib) tt {+} a ~=~(lib) ff).
Proof.
  introv.
  rw @equality_in_bool; split; intro k;
    eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast; tcsp.
Qed.

Lemma equality_union_in_uni {o} :
  forall lib (A1 A2 B1 B2 : @CTerm o) i,
    equality lib (mkc_union A1 B1)
             (mkc_union A2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # equality lib B1 B2 (mkc_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality in teq; exrepnd.

    applydup @dest_nuprl_uni in teq1.
    apply univ_implies_univi_bar3 in teq2; exrepnd.
    apply teq3 in teq0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in teq0; exrepnd.
    apply dest_nuprli_union2 in teq2; exrepnd.

    dands; exists eq; dands; auto; apply teq3; clear dependent eq;
      introv br ext; introv; exists (raise_bar bar0 x);
        introv br' ext'; introv; simpl in *; exrepnd.

    + pose proof (teq4 _ br'1 _ (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as teq4; simpl in *.
      exists (eqa lib'2 (lib_extends_trans x0 x)); auto.

    + pose proof (teq0 _ br'1 _ (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as teq0; simpl in *.
      exists (eqb lib'2 (lib_extends_trans x0 x)); auto.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqas eqbs].
    unfold equality in eqas; exrepnd.
    unfold equality in eqbs; exrepnd.

    applydup @dest_nuprl_uni in eqas1.
    applydup @dest_nuprl_uni in eqbs1.

    eapply univ_uniquely_valued in eqbs2; autodimp eqbs2 hyp;[exact eqas2|].
    apply eqbs2 in eqbs0.
    eapply type_extensionality_nuprl in eqbs1.
    apply eqbs1 in eqbs2; clear eqbs1.
    clear eq0.
    apply univ_implies_univi_bar3 in eqas2; exrepnd.
    apply eqas3 in eqas0.
    apply eqas3 in eqbs0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in eqas0; exrepnd.
    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in eqbs0; exrepnd.

    exists eq; dands; auto; apply eqas3; clear dependent eq.
    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.

    pose proof (nuprli_monotone_func i lib A1 A2 eq' eqas2) as tya; exrepnd.
    rename eq'1 into eqa.
    pose proof (nuprli_monotone_func i lib B1 B2 eq'0 eqbs1) as tyb; exrepnd.
    rename eq'1 into eqb.

    exists (per_union_eq_bar lib'1 (raise_lib_per eqa (lib_extends_trans e x)) (raise_lib_per eqb (lib_extends_trans e x))).
    apply CL_union; fold (@nuprli o i).
    exists (raise_lib_per eqa (lib_extends_trans e x)) (raise_lib_per eqb (lib_extends_trans e x)).
    exists A1 A2 B1 B2; dands; spcast; eauto 3 with slow; introv; simpl;
      try eapply tya0; try eapply tyb0.
Qed.
