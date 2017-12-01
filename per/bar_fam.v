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


Require Export raise_bar.
Require Export axiom_func_choice_on.


Definition bar_fam {o} {lib} (bar : @BarLib o lib) :=
  forall lib1 (b : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib), BarLib lib2.

Definition bar_of_bar_fam {o} {lib} {bar : @BarLib o lib} (h : bar_fam bar) : BarLib lib.
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
Defined.

Lemma all_in_bar_ext_and_implies {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> (all_in_bar_ext bar p1 # all_in_bar_ext bar p2).
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.

Lemma all_in_bar_ext_and_implies1 {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> all_in_bar_ext bar p1.
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.

Lemma all_in_bar_ext_and_implies2 {o} :
  forall {lib} (bar : @BarLib o lib) (p1 p2 : forall lib' (x : lib_extends lib' lib), [U]),
    all_in_bar_ext bar (fun lib' x => p1 lib' x # p2 lib' x)
    -> all_in_bar_ext bar p2.
Proof.
  introv h; dands; introv br ext; introv; eapply h; eauto.
Qed.

Definition pack_lib_bar {o} {lib} (bar : @BarLib o lib) :=
  {lib1 : library &
  {br   : bar_lib_bar bar lib1 &
  {lib2 : library &
  {ext  : lib_extends lib2 lib1 & lib_extends lib2 lib }}}}.

Definition mk_pack_lib_bar {o} {lib} {bar : BarLib lib}
           (lib1 : @library o)
           (br   : bar_lib_bar bar lib1)
           (lib2 : library)
           (ext  : lib_extends lib2 lib1)
           (x    : lib_extends lib2 lib) : pack_lib_bar bar :=
  existT _ lib1 (existT _ br (existT _ lib2 (existT _ ext x))).

(*Lemma per_bar_eq_preserves_all_in_bar_ext_eq_term_equals {o} :
  forall {lib} (bar : @BarLib o lib) eqa t1 t2 F,
    per_bar_eq bar eqa t1 t2
    -> all_in_bar_ext
         bar
         (fun lib' x => (eqa lib' x) <=2=> (F lib' x))
    -> all_in_bar_ext bar (fun lib' x => F lib' x t1 t2).
Proof.
  introv per alla br ext; introv.
  apply (alla lib' br lib'0 ext x).
  eapply per; eauto.
Qed.*)

Lemma all_in_bar_ext_exists_bar_implies {o} :
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
                (fun x => BarLib (projT1 (projT2 (projT2 x))))
                (fun x b => F (projT1 (projT2 (projT2 x)))
                              (projT2 (projT2 (projT2 (projT2 x))))
                              b)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { unfold pack_lib_bar; introv; exrepnd; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (mk_pack_lib_bar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (mk_pack_lib_bar lib1 br lib2 ext x)) as w; auto.
Qed.
