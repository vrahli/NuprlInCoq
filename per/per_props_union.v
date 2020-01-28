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
Require Export natk2.
Require Export terms_union.
Require Export cequiv_props.
Require Export per_props_cequiv.
Require Export per_props_uni.
Require Export per_props_util2.
Require Export per_props_fam2.


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

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq.
  apply cequivc_ext_mkc_union_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_left  in pera4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera4;[|apply ccequivc_ext_sym;eauto].

  spcast; repeat computes_to_eqval.

  apply implies_eq_term_equals_per_union_bar;
    apply in_ext_ext_implies_in_open_bar_ext;
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

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq.
  apply cequivc_ext_mkc_union_right in ceq0.
  repnd.

  eapply in_ext_ext_nuprli_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_left  in pera4;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera4;[|apply ccequivc_ext_sym;eauto].

  apply implies_eq_term_equals_per_union_bar;
    apply in_ext_ext_implies_in_open_bar_ext;
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
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca; apply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_union_l {o} :
  forall i (ts : cts(o)) lib T A B T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca; apply reca; eauto 3 with slow.
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

(*Notation "bar-two-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib),
      @two_lib_per o lib2).*)

(*Lemma all_in_bar_ext_exists2_lib_per_implies_exists2 {o} :
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
Qed.*)

(*Definition bar_two_lib_per2lib_pera {o}
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
Defined.*)

(*Definition bar_two_lib_per2lib_perb {o}
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
Defined.*)

Lemma dest_nuprl_union2 {o} :
  forall lib (eq : per(o)) A1 A2 B1 B2,
    nuprl lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    ->
    exists (eqa eqb : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_union_eq_bar_lib_per lib eqa eqb)))
        # in_open_bar_ext lib (fun lib' x => nuprl lib' A1 A2 (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => nuprl lib' B1 B2 (eqb lib' x)).
Proof.
  introv u.
  apply dest_nuprl_union in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 , eqb : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A1 A2 (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => nuprl lib'' B1 B2 (eqb lib'' y))
               # (eqa lib' x) <=2=> (per_union_eq_bar lib' eqa0 eqb) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_union in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_left  in u5;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u5;[|apply ccequivc_ext_sym;eauto].

    exists eqa0 eqb; dands; auto.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.
  apply in_open_bar_eqa_choice in e1; exrepnd.
  rename Feqa0 into Feqb.

  exists (fun_lib_dep_eqa Feqa) (fun_lib_dep_eqa Feqb).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq; simpl.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply implies_eq_term_equals_per_union_bar;
      apply in_ext_ext_implies_in_open_bar_ext;
      introv; simpl; unfold raise_ext_per.

    {
      split; intro q.

      { exists lib' e lib'0 e1 z e2; auto. }

      exrepnd.
      pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
      pose proof (e3 _ z0) as e3; simpl in *.
      pose proof (h0 _ e2) as h0; simpl in *.
      apply nuprl_refl in h0; apply nuprl_refl in e3.
      eapply nuprl_uniquely_valued in h0; try exact e3; apply h0; auto.
    }

    {
      split; intro q.

      { exists lib' e lib'0 e1 z e2; auto. }

      exrepnd.
      pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
      pose proof (e4 _ z0) as e4; simpl in *.
      pose proof (h1 _ e2) as h1; simpl in *.
      apply nuprl_refl in h1; apply nuprl_refl in e4.
      eapply nuprl_uniquely_valued in h1; try exact e4; apply h1; auto.
    }
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e1 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e2.
    eapply nuprl_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd; simpl.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e1 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    apply nuprl_refl in h1; apply nuprl_refl in e3.
    eapply nuprl_uniquely_valued in h1; try exact e3; apply h1; auto.
  }
Qed.

Lemma dest_nuprli_union2 {o} :
  forall i lib (eq : per(o)) A1 A2 B1 B2,
    nuprli i lib (mkc_union A1 B1) (mkc_union A2 B2) eq
    ->
    exists (eqa eqb : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (per_union_eq_bar_lib_per lib eqa eqb)))
        # in_open_bar_ext lib (fun lib' x => nuprli i lib' A1 A2 (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => nuprli i lib' B1 B2 (eqb lib' x)).
Proof.
  introv u.
  apply dest_nuprli_union in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 , eqb : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A1 A2 (eqa0 lib'' y))
               # in_ext_ext lib' (fun lib'' y => nuprli i lib'' B1 B2 (eqb lib'' y))
               # (eqa lib' x) <=2=> (per_union_eq_bar lib' eqa0 eqb) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_union in *; exrepnd.

    repeat ccomputes_to_valc_ext_val.

    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_left  in u5;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u5;[|apply ccequivc_ext_sym;eauto].

    exists eqa0 eqb; dands; auto.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.
  apply in_open_bar_eqa_choice in e1; exrepnd.
  rename Feqa0 into Feqb.

  exists (fun_lib_dep_eqa Feqa) (fun_lib_dep_eqa Feqb).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq; simpl.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply implies_eq_term_equals_per_union_bar;
      apply in_ext_ext_implies_in_open_bar_ext;
      introv; simpl; unfold raise_ext_per.

    {
      split; intro q.

      { exists lib' e lib'0 e1 z e2; auto. }

      exrepnd.
      pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
      pose proof (e3 _ z0) as e3; simpl in *.
      pose proof (h0 _ e2) as h0; simpl in *.
      apply nuprli_refl in h0; apply nuprli_refl in e3.
      eapply nuprli_uniquely_valued in h0; try exact e3; apply h0; auto.
    }

    {
      split; intro q.

      { exists lib' e lib'0 e1 z e2; auto. }

      exrepnd.
      pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
      pose proof (e4 _ z0) as e4; simpl in *.
      pose proof (h1 _ e2) as h1; simpl in *.
      apply nuprli_refl in h1; apply nuprli_refl in e4.
      eapply nuprli_uniquely_valued in h1; try exact e4; apply h1; auto.
    }
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e1 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e2.
    eapply nuprli_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e0.
    introv h; repnd; simpl.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e1 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e0 _ ext1 _ ext2 extz) as e0; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    apply nuprli_refl in h1; apply nuprli_refl in e3.
    eapply nuprli_uniquely_valued in h1; try exact e3; apply h1; auto.
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
  forall (lib : @library o) (eqa eqb : lib-per(lib,o)) p1 p2,
    (per_bar_eq lib (per_union_eq_bar_lib_per lib eqa eqb) p1 p2)
      <=>
      in_open_bar_ext
          lib
          (fun lib' x => per_union_eq lib' (eqa lib' x) (eqb lib' x) p1 p2).
Proof.
  introv; split; intro h.

  - apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    introv.
    eapply implies_eq_term_equals_per_union_eq; try exact h;
      try (apply lib_per_cond).

  - apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    unfold per_union_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear; introv h; simpl in *.
    eapply implies_eq_term_equals_per_union_eq; try exact h;
      try (apply lib_per_cond).
Qed.

Lemma equality_mkc_union {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_union A B)
    <=> (type lib A
         # type lib B
         # in_open_bar lib (fun lib => {a1, a2 : CTerm
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
    apply e2 in e0.
    clear dependent eq.
    dands; eauto 3 with slow;[].

    apply per_bar_eq_per_union_eq_bar_lib_per_iff in e0; exrepnd.
    eapply in_open_bar_comb2; try exact e3; clear e3.
    eapply in_open_bar_ext_comb; try exact e1; clear e1.
    eapply in_open_bar_ext_pres; try exact e0; clear e0; introv e0 e1 e3.

    unfold per_union_eq in *.
    repndors; [left|right].

    + unfold per_union_eq_L in *; exrepnd; eexists; eexists; dands; eauto.
      apply (equality_eq1 lib' A A x y (eqa lib' e)); auto.

    + unfold per_union_eq_R in *; exrepnd; eexists; eexists; dands; eauto.
      apply (equality_eq1 lib' B B x y (eqb lib' e)); auto.

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

    apply in_ext_ext_implies_in_open_bar_ext; introv.
    repndors;[left|right]; exrepnd; spcast.

    + eexists; eexists; dands; spcast; eauto 3 with slow.
      apply (equality_eq1 lib'0 A A a1 a2 (eqa' lib'0 e1)); eauto 3 with slow.
      eapply tya0.

    + eexists; eexists; dands; spcast; eauto 3 with slow.
      apply (equality_eq1 lib'0 B B b1 b2 (eqb' lib'0 e1)); eauto 3 with slow.
      eapply tyb0.
Qed.

Lemma equality_mkc_or {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_or A B)
    <=> (type lib A
         # type lib B
         # in_open_bar lib (fun lib => {a1, a2 : CTerm
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

(* MOVE *)
Lemma ccomputes_to_valc_ext_implies_cequivc {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> cequivc lib a b.
Proof.
  introv comp.
  pose proof (comp _ (lib_extends_refl _)) as comp; simpl in *.
  apply cequiv_stable; exrepnd; spcast.
  eapply cequivc_trans;[|apply cequivc_sym;exact comp0].
  apply computes_to_valc_implies_cequivc; auto.
Qed.
Hint Resolve ccomputes_to_valc_ext_implies_cequivc : slow.

Lemma ccequivc_ext_mkc_inl_if {p} :
  forall lib (a b : @CTerm p),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_inl a) (mkc_inl b).
Proof.
  introv ceq ext; apply ceq in ext; spcast.
  apply cequivc_mkc_inl_if; auto.
Qed.

Lemma ccequivc_ext_mkc_inr_if {p} :
  forall lib (a b : @CTerm p),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_inr a) (mkc_inr b).
Proof.
  introv ceq ext; apply ceq in ext; spcast.
  apply cequivc_mkc_inr_if; auto.
Qed.

Lemma ccequivc_ext_mkc_inl_implies {o} :
  forall lib (t a : @CTerm o),
    ccequivc_ext lib (mkc_inl a) t
    -> ccomputes_to_valc_ext lib t (mkc_inl a).
Proof.
  introv ceq ext; apply ceq in ext; spcast.
  apply cequivc_mkc_inl_implies in ext; exrepnd.
  exists (mkc_inl b); dands; spcast; auto; eauto 3 with slow.
  apply cequivc_mkc_inl_if; auto.
Qed.

Lemma ccequivc_ext_mkc_inr_implies {o} :
  forall lib (t a : @CTerm o),
    ccequivc_ext lib (mkc_inr a) t
    -> ccomputes_to_valc_ext lib t (mkc_inr a).
Proof.
  introv ceq ext; apply ceq in ext; spcast.
  apply cequivc_mkc_inr_implies in ext; exrepnd.
  exists (mkc_inr b); dands; spcast; auto; eauto 3 with slow.
  apply cequivc_mkc_inr_if; auto.
Qed.

Lemma equality_in_bool {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_bool
    <=>
    in_open_bar lib (fun lib =>
      (ccequivc_ext lib a tt # ccequivc_ext lib b tt)
      {+}
      (ccequivc_ext lib a ff # ccequivc_ext lib b ff)
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
      eapply lib_extends_preserves_ccomputes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_ccomputes_to_valc in k4;[|exact y].
      left; dands; spcast.

      * allapply @ccomputes_to_valc_ext_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 a (mkc_inl a1) tt); auto.
        apply ccequivc_ext_mkc_inl_if; auto.

      * allapply @ccomputes_to_valc_ext_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 b (mkc_inl a2) tt); auto.
        apply ccequivc_ext_mkc_inl_if; auto.

    + allrw @equality_in_unit; repnd.
      eapply all_in_ex_bar_modus_ponens1;try exact k3; clear k3; introv y k3; exrepnd; spcast.
      eapply lib_extends_preserves_ccomputes_to_valc in k2;[|exact y].
      eapply lib_extends_preserves_ccomputes_to_valc in k4;[|exact y].
      right; dands; spcast.

      * allapply @ccomputes_to_valc_ext_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 a (mkc_inr b1) ff); auto.
        apply ccequivc_ext_mkc_inr_if; auto.

      * allapply @ccomputes_to_valc_ext_implies_ccequivc_ext.
        apply (ccequivc_ext_trans lib'0 b (mkc_inr b2) ff); auto.
        apply ccequivc_ext_mkc_inr_if; auto.

  - eapply all_in_ex_bar_modus_ponens1;try exact k; clear k; introv x k; exrepnd; spcast.
    repndors; repnd; spcast;[left|right].

    + apply ccequivc_ext_sym in k0.
      apply ccequivc_ext_sym in k.
      apply ccequivc_ext_mkc_inl_implies in k0.
      apply ccequivc_ext_mkc_inl_implies in k.
      eexists; eexists; dands; eauto.
      apply implies_equality_in_unit; eauto 3 with slow.

    + apply ccequivc_ext_sym in k0.
      apply ccequivc_ext_sym in k.
      apply ccequivc_ext_mkc_inr_implies in k0.
      apply ccequivc_ext_mkc_inr_implies in k.
      eexists; eexists; dands; eauto.
      apply implies_equality_in_unit; eauto 3 with slow.
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
    in_open_bar lib (fun lib => ccequivc_ext lib a tt {+} ccequivc_ext lib a ff).
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
    apply teq2 in teq0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in teq0; exrepnd.
    apply dest_nuprli_union2 in teq3; exrepnd.

    dands; exists eq; dands; auto; apply teq2; clear dependent eq;
      eapply in_open_bar_ext_comb; try exact teq4; clear teq4;
        eapply in_open_bar_ext_pres; try exact teq3; clear teq3; introv teq3 teq4;
          simpl; eexists; eauto.

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
    apply eqas2 in eqas0.
    apply eqas2 in eqbs0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in eqas0; exrepnd.
    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in eqbs0; exrepnd.

    exists eq; dands; auto; apply eqas2; clear dependent eq.
    apply in_ext_ext_implies_in_open_bar_ext; introv; simpl.

    pose proof (nuprli_monotone_func i lib A1 A2 eq' eqas3) as tya; exrepnd.
    rename eq'1 into eqa.
    pose proof (nuprli_monotone_func i lib B1 B2 eq'0 eqbs1) as tyb; exrepnd.
    rename eq'1 into eqb.

    exists (per_union_eq_bar lib' (raise_lib_per eqa e) (raise_lib_per eqb e)).
    apply CL_union; fold (@nuprli o i).
    exists (raise_lib_per eqa e) (raise_lib_per eqb e).
    exists A1 A2 B1 B2; dands; spcast; eauto 3 with slow; introv; simpl;
      try eapply tya0; try eapply tyb0.
Qed.
