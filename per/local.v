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


Require Export bar_fam.
Require Export type_sys.


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

Definition local_ts {o} (ts : cts(o)) :=
  forall {lib} (bar : @BarLib o lib) T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

Definition lib_per_per_bar {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (fbar : bar_fam bar)
           (feqa : bar-lib-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {lib2 : library
            , {ext : lib_extends lib2 lib1
            , {x : lib_extends lib2 lib
            , {lib0 : library
            , {w : lib_extends lib' lib0
            , {fb : bar_lib_bar (fbar lib1 br lib2 ext x) lib0
            , feqa lib1 br lib2 ext x lib' (lib_extends_trans w (bar_lib_ext (fbar lib1 br lib2 ext x) lib0 fb)) t1 t2}}}}}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br lib2 ext x0 lib0 w fb; auto.
  - exists lib1 br lib2 ext x0 lib0 w fb; auto.
Defined.

(*Lemma local_per_bar {o} :
  forall (ts : cts(o)),
    type_extensionality ts
    -> uniquely_valued ts
    -> local_ts (per_bar ts).
Proof.
  introv text uv eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.

  exists (bar_of_bar_fam fbar).

  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext b lib' br0)))
      as alla2; simpl in *.

    eapply text;[eauto|].

    introv; split; introv w.

    { subst.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    eapply uv in z0; autodimp z0 hyp;[exact alla2|].
    apply z0; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    unfold per_bar_eq; split; introv h; exrepnd.

    - exists bar'.
      introv br ext; introv; simpl in *; exrepnd.
      pose proof (alla1 lib0 br lib3 ext0 x0) as q; repnd.

      pose proof (h0 lib') as h0.
      autodimp h0 hyp; simpl in *.
      { simpl; eexists; eexists; dands; eauto 4 with slow. }
      pose proof (h0 lib'0 ext x) as h0; simpl in *.
      apply q0 in h0.

      clear q q0.

      exists lib1 br lib2 ext0 x0 lib' ext br0.
      eapply h; eauto.

    - pose proof (alla1 lib' br lib'0 ext x) as z; repnd.
      apply z.
      introv fb w; introv.

      pose proof (h lib'1) as h.
      simpl in h.

      autodimp h hyp.
      { exists lib' br lib'0 ext x; auto. }

      pose proof (h lib'2 w) as h; simpl in *.
      autodimp h hyp; eauto 3 with slow.
      exrepnd.

      pose proof (z0 lib'1 fb lib'2 w x0) as z0; simpl in *.

      pose proof (alla1 lib1 br0 lib2 ext0 x1) as q; repnd.
      pose proof (q0 lib0 fb0 lib'2 w0 (lib_extends_trans w0 (bar_lib_ext (fbar lib1 br0 lib2 ext0 x1) lib0 fb0))) as q0; simpl in *.
      eapply uv in q0; autodimp q0 hyp;[exact z0|].
      apply q0; auto.
  }
Qed.
Hint Resolve local_per_bar : slow.

Lemma type_extensionality_univi {o} :
  forall i, @type_extensionality o (univi i).
Proof.
  introv u e.
  allrw @univi_exists_iff; exrepnd.
  exists j; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve type_extensionality_univi : slow.

Lemma uniquely_valued_univi {o} :
  forall i, @uniquely_valued o (univi i).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd.
  spcast; computes_to_eqval.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve uniquely_valued_univi : slow.

Lemma local_univi_bar {o} :
  forall i, @local_ts o (univi_bar i).
Proof.
  introv eqiff alla.
  eapply local_per_bar in alla; eauto 3 with slow.
Qed.
Hint Resolve local_univi_bar : slow.

Lemma local_univ {o} : @local_ts o univ.
Proof.
  introv eqiff alla.

  (* Do we have to wrap a [per_bar] around [univ]?
     Or move the universe inside the [per_bar]? *)
Abort.
 *)
