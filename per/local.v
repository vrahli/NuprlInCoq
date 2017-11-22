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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export bar_fam.


Notation "bar-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib), lib-per(lib2,o)).

Lemma all_in_bar_ext2_exists_eqa_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    (forall lib1 (br : bar_lib_bar bar lib1)
            lib2 (ext : lib_extends lib2 lib1)
            (x : lib_extends lib2 lib),
        {eqa : lib-per(lib2,o) , F lib1 br lib2 ext x eqa})
    ->
    exists (feqa : bar-lib-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib1 br lib2 ext x (feqa lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => lib-per(projT1 (projT2 (projT2 x)),o))
                (fun x e => F (projT1 x)
                              (projT1 (projT2 x))
                              (projT1 (projT2 (projT2 x)))
                              (projT1 (projT2 (projT2 (projT2 x))))
                              (projT2 (projT2 (projT2 (projT2 x))))
                              e)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (mk_pack_lib_bar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (mk_pack_lib_bar lib1 br lib2 ext x)) as w; auto.
Qed.

Lemma local_univi_bar {o} :
  forall {lib} (bar : @BarLib o lib) i T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => univi_bar i lib' T T' (eqa lib' x))
    -> univi_bar i lib T T' eq.
Proof.
  introv eqiff alla.
  unfold univi_bar in *.
  destruct i.

  {
    unfold univi_bar, per_bar in *; simpl in *.
    pose proof (bar_non_empty bar) as q; exrepnd.
    pose proof (alla lib' q0 lib' (lib_extends_refl lib') (bar_lib_ext bar lib' q0)) as h; simpl in *.
    exrepnd.
    pose proof (bar_non_empty bar0) as w; exrepnd.
    pose proof (h0 lib'0 w0 lib'0 (lib_extends_refl lib'0)) as h0; simpl in *.
    autodimp h0 hyp; tcsp; eauto 3 with slow.
  }

  remember (S i) as k.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.

  exists (bar_of_bar_fam fbar).

  exists (fun lib' (x : lib_extends lib' lib) => univi_eq (univi i) lib').
  dands.

  {
    introv br ext x; simpl in *; exrepnd.

    pose proof (alla0 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.
    pose proof (alla0
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext b lib' br0)))
      as alla0; simpl in *.

    allrw @univi_exists_iff; exrepnd.
    exists j; dands; auto; tcsp.

    SearchAbout univi.
  }


XXXXXXX

Lemma local_per_bar {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => per_bar ts lib' T T' (eqa lib' x))
    -> per_bar ts lib T T' eq.
Proof.
  introv eqiff alla.
  unfold per_bar in *.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.

  exists (bar_of_bar_fam fbar).

  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {lib2 : library
            , {ext : lib_extends lib2 lib1
            , {x : lib_extends lib2 lib
            , {w : lib_extends lib' lib2
            , feqa lib1 br lib2 ext x lib' w t1 t2}}}}}}).
  dands.

  {
    introv br ext; introv x.
    simpl in *; exrepnd.

(*    pose proof (alla0 lib1 br lib'0
                      (lib_extends_trans (lib_extends_trans ext (bar_lib_ext _ lib' br0)) ext0)
                      x) as w; exrepnd.
    clear w1.*)

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext b lib' br0)))
      as alla2; simpl in *.


  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    unfold per_bar_eq; split; introv h br ext; introv.

    - simpl in *; exrepnd.
      eapply h; eauto 4 with slow.

    - pose proof (h lib') as h.
      simpl in h.

      (fun lib' (x : lib_extends lib' lib) t1 t2 =>
           all_in_bar_ext (bar_of_bar_fam fbar) (fun lib' x => eqa lib' x t1 t2)).

      apply (h lib'0); simpl in *.
      { exists lib' br lib'0 ext x; eauto 3 with slow.
        remember (fbar lib' br lib'0 ext x) as b; eauto 3 with slow.
        }

  }
Qed.

XXXXXXXX
  induction i; introv eqiff alla; simpl in *.

  {
    unfold univi_bar, per_bar in *; simpl in *.
    pose proof (bar_non_empty bar) as q; exrepnd.
    apply (alla lib' q0 lib' (lib_extends_refl lib')); eauto 3 with slow.
  }


Qed.
