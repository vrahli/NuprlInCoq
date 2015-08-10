(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import nuprl_props.

Lemma choice_teq :
  forall A v1 B1 v2 B2,
    (forall a1 a2 : CTerm,
       equality a1 a2 A
       -> tequality (substc a1 v1 B1) (substc a2 v2 B2))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality a1 a2 A,
            nuprl (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv F.
  exists (fun a1 a2 e => projT1 (F a1 a2 e)); sp; destruct (F a1 a2 e); sp.
Qed.

Lemma choice_spteq :
  forall F1 F2,
    (forall x y : CTerm, tequality (F1 x y) (F2 x y))
    -> {f : forall x y : CTerm, per
        , forall x y : CTerm, nuprl (F1 x y) (F2 x y) (f x y)}.
Proof.
  introv F.
  exists (fun a1 a2 => projT1 (F a1 a2)); sp; destruct (F x y); sp.
Qed.

Lemma choice_teqi :
  forall i A v1 B1 v2 B2,
    (forall a1 a2 : CTerm,
       equality a1 a2 A
       -> equality (substc a1 v1 B1) (substc a2 v2 B2) (mkc_uni i))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality a1 a2 A,
            nuprli i (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv F.

  assert (forall a1 a2 : CTerm,
            equality a1 a2 A ->
            {eq : per , nuprli i (substc a1 v1 B1) (substc a2 v2 B2) eq}) as fn.
  (* begin proof of the assert *)
  introv e.
  generalize (F a1 a2 e); intro es.
  unfold equality in es; exrepnd.
  inversion es1; try not_univ.
  duniv j h.
  allrw univi_exists_iff; exrepnd.
  computes_to_value_isvalue; GC.
  discover; exrepnd.
  allfold (nuprli j0).
  exists eqa; sp.
  (* end proof of the assert *)

  exists (fun a1 a2 e => projT1 (fn a1 a2 e)); sp; destruct (fn a1 a2 e); sp.
Qed.

Lemma choice_spteqi :
  forall i F1 F2,
    (forall x y : CTerm, equality (F1 x y) (F2 x y) (mkc_uni i))
    -> {f : forall x y : CTerm, per
        , forall x y : CTerm, nuprli i (F1 x y) (F2 x y) (f x y)}.
Proof.
  introv F.

  assert (forall x y : CTerm,
            {eq : per , nuprli i (F1 x y) (F2 x y) eq}) as fn.
  (* begin proof of the assert *)
  introv.
  generalize (F x y); intro es.
  unfold equality in es; exrepnd.
  inversion es1; try not_univ.
  duniv j h.
  allrw univi_exists_iff; exrepnd.
  computes_to_value_isvalue; GC.
  discover; exrepnd.
  allfold (nuprli j0).
  exists eqa; sp.
  (* end proof of the assert *)

  exists (fun x y => projT1 (fn x y)); sp; destruct (fn x y); sp.
Qed.

Lemma choice_eq :
  forall A v B F1 F2,
    (forall a1 a2 : CTerm,
       equality a1 a2 A
       -> equality (F1 a1) (F2 a2) (substc a1 v B))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality a1 a2 A,
            nuprl (substc a1 v B) (substc a1 v B) (f a1 a2 e)
            # f a1 a2 e (F1 a1) (F2 a2)}.
Proof.
  introv F.
  exists (fun a1 a2 e => projT1 (F a1 a2 e)); sp; destruct (F a1 a2 e); sp.
Qed.

Lemma choice_teq1 :
  forall A eqa v1 B1 v2 B2,
    nuprl A A eqa
    -> (forall a1 a2 : CTerm,
          equality a1 a2 A
          -> tequality (substc a1 v1 B1) (substc a2 v2 B2))
    -> {f : (forall a1 a2 (e : eqa a1 a2), per)
        , forall a1 a2 (e : eqa a1 a2),
            nuprl (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv na F.
  exists (fun a1 a2 e =>
            projT1 (F a1 a2 (existT (fun eq => nuprl A A eq # eq a1 a2) eqa (na, e))));
    sp; destruct (F a1 a2 (existT (fun eq => nuprl A A eq # eq a1 a2) eqa (na, e))); sp.
Qed.


Lemma choice_teq2 :
  forall eqp eqa P ap A bp1 ba1 B1 bp2 ba2 B2,
    nuprl P P eqp
    -> (forall p1 p2 (ep : eqp p1 p2),
          nuprl (substc p1 ap A) (substc p2 ap A) (eqa p1 p2 ep))
    -> (forall p1 p2 : CTerm,
          equality p1 p2 P
          -> forall a1 a2 : CTerm,
               equality a1 a2 (substc p1 ap A)
               -> tequality (lsubstc2 bp1 p1 ba1 a1 B1) (lsubstc2 bp2 p2 ba2 a2 B2))
    -> {f : (forall p1 p2 (ep : eqp p1 p2) a1 a2 (ea : eqa p1 p2 ep a1 a2), per)
        , forall p1 p2 (ep : eqp p1 p2) a1 a2 (ea : eqa p1 p2 ep a1 a2),
            nuprl (lsubstc2 bp1 p1 ba1 a1 B1)
                  (lsubstc2 bp2 p2 ba2 a2 B2)
                  (f p1 p2 ep a1 a2 ea)}.
Proof.
  introv np na F.

  exists (fun p1 p2 ep a1 a2 ea =>
            projT1 (F p1 p2
                      (existT (fun eq => nuprl P P eq # eq p1 p2) eqp (np, ep))
                      a1 a2
                      (existT (fun eq => nuprl (substc p1 ap A)
                                               (substc p1 ap A) eq
                                         # eq a1 a2)
                              (eqa p1 p2 ep)
                              (nuprl_refl (substc p1 ap A)
                                          (substc p2 ap A)
                                          (eqa p1 p2 ep)
                                          (na p1 p2 ep),
                               ea)))); sp.

  destruct (F p1 p2 exI(eqp, (np, ep)) a1 a2
              exI(eqa p1 p2 ep,
                  (nuprl_refl (substc p1 ap A) (substc p2 ap A)
                              (eqa p1 p2 ep) (na p1 p2 ep), ea))); sp.
Qed.
