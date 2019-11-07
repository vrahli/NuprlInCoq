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


Require Export nuprl.
Require Export axiom_func_choice_on.
Require Export computation_lib_extends2.


(* MOVE *)
Lemma in_open_bar_ext_comb_per {o} :
  forall (lib : @library o) (F G : forall lib' (x : lib_extends lib' lib), per(o)) a b,
    in_open_bar_ext lib (fun lib' x => (F lib' x) <=2=> (G lib' x))
    -> in_open_bar_ext lib (fun lib' x => G lib' x a b)
    -> in_open_bar_ext lib (fun lib' x => F lib' x a b).
Proof.
  introv h q.
  eapply in_open_bar_ext_pres2;[|exact h|exact q]; clear h q; introv h q; apply h; auto.
Qed.
Hint Resolve in_open_bar_ext_comb_per : slow.

(*Definition bar_fam {o} {lib} (bar : @BarLib o lib) :=
  forall lib1 (b : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib), BarLib lib2.*)

(*Definition bar_of_bar_fam {o} {lib} {bar : @BarLib o lib} (h : bar_fam bar) : BarLib lib.
Proof.
  exists (fun lib' =>
            exists lib1,
              exists (br : bar_lib_bar bar lib1),
                exists lib2,
                  exists (ext : lib_extends lib2 lib1),
                    exists (x : lib_extends lib2 lib),
                      bar_lib_bar (h lib1 br lib2 ext x) lib').

  - introv ext.

    destruct bar as [bar1 bars1 ext1]; simpl in *.
    pose proof (bars1 infLib) as q; autodimp q hyp; exrepnd.
    remember (h lib' q1 lib' (lib_extends_refl lib') q2) as b; symmetry in Heqb.

    destruct b as [bar2 bars2 ext2]; simpl in *.
    pose proof (bars2 infLib) as w; autodimp w hyp; exrepnd.

    exists lib'0; dands; eauto 3 with slow.
    exists lib' q1 lib' (lib_extends_refl lib') q2.
    rewrite Heqb; simpl; auto.

  - introv w; exrepnd.
    remember (h lib1 br lib2 ext x) as b; symmetry in Heqb.
    destruct bar as [bar1 bars1 ext1]; simpl in *.
    destruct b as [bar2 bars2 ext2]; simpl in *.
    eauto 3 with slow.
Defined.*)

(*Lemma all_in_bar_ext_and_implies {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> (all_in_bar_ext bar p1 # all_in_bar_ext bar p2).
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.*)

(*Lemma all_in_bar_ext_and_implies1 {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> all_in_bar_ext bar p1.
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.*)

(*Lemma all_in_bar_ext_and_implies2 {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> all_in_bar_ext bar p2.
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.*)

(*Record pack_lib_bar {o} {lib} (bar : @BarLib o lib) :=
  MkPackLibBar
    {
      plb_lib1 : library;
      plb_br   : bar_lib_bar bar plb_lib1;
      plb_lib2 : library;
      plb_ext  : lib_extends plb_lib2 plb_lib1;
      plb_x    : lib_extends plb_lib2 lib
    }.
Arguments MkPackLibBar {o} {lib} [bar] _ _ _ _ _.*)

(*Lemma ccomputes_to_valc_implies_all_in_bar {o} :
  forall lib (bar : @BarLib o lib) a b,
    a ===>(lib) b
    -> all_in_bar bar (fun lib' => a ===>(lib') b).
Proof.
  introv comp br ext; spcast; eauto 4 with slow.
Qed.
Hint Resolve ccomputes_to_valc_implies_all_in_bar : slow.*)

(*Lemma all_in_bar_ext_eq_term_equals_preserves_per_bar_eq {o} :
  forall lib (bar : @BarLib o lib) (eqa eqb : lib-per(lib,o)) t1 t2,
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> per_bar_eq bar eqa t1 t2
    -> per_bar_eq bar eqb t1 t2.
Proof.
  introv alla allb br; introv.
  unfold per_bar_eq in *.
  pose proof (allb _ br _ e) as allb; simpl in *; exrepnd.

  eapply ex_finite_ext_ext_pres; eauto.
  introv ext h; repeat introv.
  pose proof (h x) as h.

  eapply e_all_in_ex_bar_ext_pres; eauto.
  introv br' xt' q.

  assert (lib_extends lib'' lib') as xt by eauto 3 with slow.
  apply (alla _ br _ xt (lib_extends_trans y x)); auto.
Qed.*)

(*Lemma per_bar_eq_preserves_all_in_bar_ext_eq_term_equals {o} :
  forall {lib} (bar : @BarLib o lib) eqa eqb t1 t2,
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> per_bar_eq bar eqa t1 t2
    -> per_bar_eq bar eqb t1 t2).
Proof.
  introv alla per br ext; introv.
  apply (alla lib' br lib'0 ext x).
  eapply per; eauto.
Qed.*)

(*Lemma all_in_bar_ext_exists_bar_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar_ext bar (fun lib' x => {bar' : BarLib lib' , F lib' x bar'})
    ->
    exists (fbar : bar_fam bar),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 x (fbar lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => BarLib (plb_lib2 bar x))
                (fun x b => F (plb_lib2 bar x)
                              (plb_x bar x)
                              b)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; simpl in *; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.*)

(*Definition bar_fam_fam {o} {lib} (bar : @BarLib o lib) (fbar : bar_fam bar) :=
  forall lib1 (b : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib),
  forall lib1' (b' : bar_lib_bar (fbar lib1 b lib2 ext x) lib1')
         lib2' (ext' : lib_extends lib2' lib1')
         (x' : lib_extends lib2' lib2),
    BarLib lib2'.*)

(*Record pack_lib_bar_fam {o} {lib} (bar : @BarLib o lib) (fbar : bar_fam bar) :=
  MkPackLibBarFam
    {
      plbf_lib1  : library;
      plbf_br    : bar_lib_bar bar plbf_lib1;
      plbf_lib2  : library;
      plbf_ext   : lib_extends plbf_lib2 plbf_lib1;
      plbf_x     : lib_extends plbf_lib2 lib;
      plbf_lib1' : library;
      plbf_br'   : bar_lib_bar (fbar plbf_lib1 plbf_br plbf_lib2 plbf_ext plbf_x) plbf_lib1';
      plbf_lib2' : library;
      plbf_ext'  : lib_extends plbf_lib2' plbf_lib1';
      plbf_x'    : lib_extends plbf_lib2' plbf_lib2;
    }.
Arguments MkPackLibBarFam {o} {lib} [bar] [fbar] _ _ _ _ _ _ _ _ _ _.*)

(*Lemma all_in_bar_ext_exists_fbar_implies {o} :
  forall {lib} (bar : @BarLib o lib) (fbar : bar_fam bar) (F : forall lib2 lib' (x : lib_extends lib' lib2) (b : BarLib lib'), Prop),
  (forall lib1 (br : bar_lib_bar bar lib1)
          lib2 (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib),
      all_in_bar_ext
        (fbar lib1 br lib2 ext x)
        (fun lib' (x' : lib_extends lib' lib2) => {bar' : BarLib lib' , F lib2 lib' x' bar'}))
  ->
  exists (ffbar : bar_fam_fam bar fbar),
  forall lib1 (br : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib),
  forall lib1' (br' : bar_lib_bar (fbar lib1 br lib2 ext x) lib1')
         lib2' (ext' : lib_extends lib2' lib1')
         (x' : lib_extends lib2' lib2),
    F lib2 lib2' x' (ffbar lib1 br lib2 ext x lib1' br' lib2' ext' x').
Proof.
  introv h.

  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar_fam bar fbar)
                (fun x => BarLib (plbf_lib2' bar fbar x))
                (fun x b => F (plbf_lib2 bar fbar x)
                              (plbf_lib2' bar fbar x)
                              (plbf_x' bar fbar x)
                              b)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; exrepnd; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1)
              lib2 (ext : lib_extends lib2 lib1)
              (x : lib_extends lib2 lib)
              lib1' (br' : bar_lib_bar (fbar lib1 br lib2 ext x) lib1')
              lib2' (ext' : lib_extends lib2' lib1')
              (x' : lib_extends lib2' lib2)=>
            (f (MkPackLibBarFam lib1 br lib2 ext x lib1' br' lib2' ext' x'))).
  introv; simpl in *.
  pose proof (C0 (MkPackLibBarFam lib1 br lib2 ext x lib1' br' lib2' ext' x')) as w; auto.
Qed.*)

(*Definition bar_of_bar_fam_fam {o} {lib}
           {bar : @BarLib o lib} {f : bar_fam bar}
           (h : bar_fam_fam bar f) : BarLib lib.
Proof.
  exists (fun lib' =>
            exists lib1,
              exists (br : bar_lib_bar bar lib1),
                exists lib2,
                  exists (ext : lib_extends lib2 lib1),
                    exists (x : lib_extends lib2 lib),
                      exists lib1',
                        exists (br' : bar_lib_bar (f lib1 br lib2 ext x) lib1'),
                          exists lib2',
                            exists (ext' : lib_extends lib2' lib1'),
                              exists (x' : lib_extends lib2' lib2),
                                bar_lib_bar (h lib1 br lib2 ext x lib1' br' lib2' ext' x') lib').

  - introv ext.

    destruct bar as [bar1 bars1 ext1]; simpl in *.
    pose proof (bars1 infLib) as q; autodimp q hyp; exrepnd.
    remember (f lib' q1 lib' (lib_extends_refl lib') q2) as b.

    destruct b as [bar2 bars2 ext2]; simpl in *.
    pose proof (bars2 infLib) as w; autodimp w hyp; exrepnd.

    assert (bar_lib_bar (f lib' q1 lib' (lib_extends_refl lib') q2) lib'0) as z by (rewrite <- Heqb; simpl; auto).

    remember (h lib' q1 lib' (lib_extends_refl lib') q2 lib'0 z lib'0 (lib_extends_refl lib'0) w2) as q; simpl in *.

    destruct q as [bar3 bars3 ext3]; simpl in *.
    pose proof (bars3 infLib) as u; autodimp u hyp; exrepnd.

    exists lib'1; dands; eauto 3 with slow.
    exists lib' q1 lib' (lib_extends_refl lib') q2.
    exists lib'0 z lib'0 (lib_extends_refl lib'0) w2.
    rewrite <- Heqq; simpl; auto.

  - introv w; exrepnd.
    remember (h lib1 br lib2 ext x lib1' br' lib2' ext' x') as b; symmetry in Heqb.
    destruct bar as [bar1 bars1 ext1]; simpl in *.
    destruct b as [bar2 bars2 ext2]; simpl in *.
    eauto 4 with slow.
Defined.*)

Lemma in_open_bar_ext_eq_term_equals_preserves_per_bar_eq {o} :
  forall (lib : @library o) (eqa eqb : lib-per(lib,o)) t1 t2,
    in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> per_bar_eq lib eqa t1 t2
    -> per_bar_eq lib eqb t1 t2.
Proof.
  introv alla allb.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb;[|exact allb]; clear allb.
  eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
  apply in_ext_ext_implies_in_open_bar_ext; simpl.
  introv h q; apply h; auto.
Qed.
