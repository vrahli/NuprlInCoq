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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export nuprl_props.
Require Export axiom_func_choice_on.


Lemma choice_teq {p} :
  forall lib (A : @CTerm p) v1 B1 v2 B2,
    (forall a1 a2 : CTerm,
       equality lib a1 a2 A
       -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality lib a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality lib a1 a2 A,
            nuprl lib (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & equality lib a1 a2 A}}
                per
                (fun a b => nuprl lib (substc (projT1 a) v1 B1) (substc (projT1 (projT2 a)) v2 B2) b));
    intro C.
  dest_imp C hyp.

  intros; exrepnd.
  generalize (F a1 a2 a3); intros teq.
  unfold tequality in teq; exrepnd; simpl.
  exists eq; sp.

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                                   a1
                                   (existT (fun a2 => equality lib a1 a2 A)
                                           a2
                                           e))); introv.
  generalize (C0 (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                         a1
                         (existT (fun a2 => equality lib a1 a2 A)
                                 a2
                                 e))); simpl; sp.
Qed.

Lemma choice_spteq {p} :
  forall lib F1 F2,
    (forall x y : CTerm, tequality lib (F1 x y) (F2 x y))
    -> {f : forall x y : @CTerm p, per(p)
        , forall x y : CTerm, nuprl lib (F1 x y) (F2 x y) (f x y)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                (CTerm # CTerm)
                per
                (fun p e => nuprl lib
                                  (F1 (fst p) (snd p))
                                  (F2 (fst p) (snd p))
                                  e));
    intro C.
  dest_imp C hyp.

  intros; exrepnd.
  generalize (F a0 a); intros teq.
  unfold tequality in teq; exrepnd; simpl.
  exists eq; sp.

  exrepnd.

  exists (fun x y => f (x, y)); introv.
  generalize (C0 (x, y)); simpl; sp.
Qed.

(*
Lemma choice_teqi :
  forall i A v1 B1 v2 B2,
    (forall a1 a2 : CTerm,
       equality a1 a2 A
       -> tequalityi i (substc a1 v1 B1) (substc a2 v2 B2))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality a1 a2 A,
            nuprli i (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & equality a1 a2 A}}
                per
                (fun a b => nuprli i (substc (projT1 a) v1 B1) (substc (projT1 (projT2 a)) v2 B2) b));
    intro C.
  dest_imp C hyp.

  intros; exrepnd.
  rw <- tequalityi_eq.
  generalize (F a1 a2 a3); intros teq; simpl; sp.

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & equality a1 a2 A})
                                   a1
                                   (existT (fun a2 => equality a1 a2 A)
                                           a2
                                           e))); introv.
  generalize (C0 (existT (fun a1 => {a2 : CTerm & equality a1 a2 A})
                         a1
                         (existT (fun a2 => equality a1 a2 A)
                                 a2
                                 e))); simpl; sp.
Qed.
*)

Lemma all_in_bar_ext_exists_lib_per_implies_exists {o} :
  forall {lib} (bar : @BarLib o lib)
         (F : forall lib' (x : lib_extends lib' lib) (eqa : lib-per(lib',o)), Prop),
    all_in_bar_ext bar (fun lib' x => {eqa : lib-per(lib',o) , F lib' x eqa})
    ->
    exists (feqa : bar-lib-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 x (feqa lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => lib-per(plb_lib2 _ x,o))
                (fun x e => F (plb_lib2 _ x)
                              (plb_x _ x)
                              e)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; simpl in *; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

Notation "bar-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib), per(o)).

Lemma all_in_bar_ext_exists_per_implies_exists {o} :
  forall {lib} (bar : @BarLib o lib)
         (F : forall lib' (x : lib_extends lib' lib) (eqa : per(o)), Prop),
    all_in_bar_ext bar (fun lib' x => {eqa : per(o) , F lib' x eqa})
    ->
    exists (feqa : bar-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 x (feqa lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => per(o))
                (fun x e => F (plb_lib2 _ x)
                              (plb_x _ x)
                              e)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; simpl in *; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

Lemma nuprli_type_extensionality {o} :
  forall i, @type_extensionality o (nuprli i).
Proof.
  apply nuprli_type_system.
Qed.
Hint Resolve nuprli_type_extensionality : slow.

Definition bar_per2lib_per {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {x : lib_extends lib' lib
            , feqa lib1 br lib' ext x t1 t2}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br ext x0; auto.
  - exists lib1 br ext x0; auto.
Defined.

(* CRAZY *)
Lemma choice_teqi {o} :
  forall lib i (A : @CTerm o) v1 B1 v2 B2,
    (forall a1 a2 : CTerm,
       equality lib a1 a2 A
       -> equality lib (substc a1 v1 B1) (substc a2 v2 B2) (mkc_uni i))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality lib a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality lib a1 a2 A,
            nuprli i lib (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & equality lib a1 a2 A}}
                per
                (fun a b => nuprli
                              i
                              lib
                              (substc (projT1 a) v1 B1)
                              (substc (projT1 (projT2 a)) v2 B2)
                              b));
    intro C.
  dest_imp C hyp.

  {
    intros; exrepnd.
    generalize (F a1 a2 a3); intros teq; simpl; sp.
    unfold equality in teq; exrepnd.

    apply dest_nuprl_uni in teq1.
    apply univ_implies_univi_bar3 in teq1; exrepnd.
    apply teq2 in teq0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (univi_eq_lib_per lib i) (B1)[[v1\\a1]] (B2)[[v2\\a2]]) as h by (exists bar; auto).
    clear dependent bar.
    unfold per_bar_eq in h; simpl in *.

    pose proof (@collapse2bars_ext o lib (fun lib' x => univi_eq (univi_bar i) lib' (B1) [[v1\\a1]] (B2)[[v2\\a2]])) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in h; clear q.
    exrepnd.
    unfold univi_eq in h0; fold (@nuprli o i) in *.

    apply all_in_bar_ext_exists_per_implies_exists in h0; exrepnd.
    exists (per_bar_eq bar (bar_per2lib_per feqa)).
    apply CL_bar.
    exists bar (bar_per2lib_per feqa).
    dands; tcsp.

    introv br ext; introv; simpl; try (fold (@nuprli o i)).
    pose proof (h1 _ br _ ext x) as q.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro h.

    { exists lib' br ext x; auto. }

    exrepnd.
    pose proof (h1 _ br0 _ ext0 x0) as h1.
    eapply nuprli_uniquely_valued in h1; try exact q.
    apply h1; auto.
  }

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                                   a1
                                   (existT (fun a2 => equality lib a1 a2 A)
                                           a2
                                           e))); introv.
  generalize (C0 (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                         a1
                         (existT (fun a2 => equality lib a1 a2 A)
                                 a2
                                 e))); simpl; sp.
Qed.

Lemma choice_spteqi {o} :
  forall lib i F1 F2,
    (forall x y : CTerm, equality lib (F1 x y) (F2 x y) (mkc_uni i))
    -> {f : forall x y : @CTerm o, per(o)
        , forall x y : CTerm, nuprli i lib (F1 x y) (F2 x y) (f x y)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                (CTerm # CTerm)
                per
                (fun p e => nuprli i lib
                                   (F1 (fst p) (snd p))
                                   (F2 (fst p) (snd p))
                                   e));
    intro C.
  dest_imp C hyp.

  {
    intros; exrepnd.
    generalize (F a0 a); intros teq.
    unfold equality in teq; exrepnd; simpl.

    apply dest_nuprl_uni in teq1.
    apply univ_implies_univi_bar3 in teq1; exrepnd.
    apply teq2 in teq0.
    clear dependent eq.

    assert (exists (bar : BarLib lib), per_bar_eq bar (univi_eq_lib_per lib i) (F1 a0 a) (F2 a0 a)) as h by (exists bar; auto).
    clear dependent bar.
    unfold per_bar_eq in h; simpl in *.

    pose proof (@collapse2bars_ext o lib (fun lib' x => univi_eq (univi_bar i) lib' (F1 a0 a) (F2 a0 a))) as q.
    simpl in q; autodimp q hyp; tcsp;[].
    apply q in h; clear q.
    exrepnd.
    unfold univi_eq in h0; fold (@nuprli o i) in *.

    apply all_in_bar_ext_exists_per_implies_exists in h0; exrepnd.
    exists (per_bar_eq bar (bar_per2lib_per feqa)).
    apply CL_bar.
    exists bar (bar_per2lib_per feqa).
    dands; tcsp.

    introv br ext; introv; simpl; try (fold (@nuprli o i)).
    pose proof (h1 _ br _ ext x) as q.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro h.

    { exists lib' br ext x; auto. }

    exrepnd.
    pose proof (h1 _ br0 _ ext0 x0) as h1.
    eapply nuprli_uniquely_valued in h1; try exact q.
    apply h1; auto.
  }

  exrepnd.

  exists (fun x y => f (x, y)); introv.
  generalize (C0 (x, y)); simpl; sp.
Qed.

Lemma choice_eq {p} :
  forall lib (A : @CTerm p) v B F1 F2,
    (forall a1 a2 : CTerm,
       equality lib a1 a2 A
       -> equality lib (F1 a1) (F2 a2) (substc a1 v B))
    -> {f : forall a1 a2 : CTerm,
            forall e : equality lib a1 a2 A,
              per
        , forall a1 a2 : CTerm,
          forall e : equality lib a1 a2 A,
            nuprl lib (substc a1 v B) (substc a1 v B) (f a1 a2 e)
            # f a1 a2 e (F1 a1) (F2 a2)}.
Proof.
  introv F.
  generalize (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & equality lib a1 a2 A}}
                per
                (fun a b => nuprl lib
                                  (substc (projT1 a) v B)
                                  (substc (projT1 a) v B)
                                  b
                            # b (F1 (projT1 a))
                                (F2 (projT1 (projT2 a)))));
    intro C.
  dest_imp C hyp.

  {
    intros; exrepnd.
    generalize (F a1 a2 a3); intros teq.
    unfold equality in teq; exrepnd; simpl.
    exists eq; sp.
  }

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                                   a1
                                   (existT (fun a2 => equality lib a1 a2 A)
                                           a2
                                           e))); introv.
  generalize (C0 (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                         a1
                         (existT (fun a2 => equality lib a1 a2 A)
                                 a2
                                 e))); simpl; sp.
Qed.

Lemma choice_teq1 {p} :
  forall lib (A : @CTerm p) eqa v1 B1 v2 B2,
    nuprl lib A A eqa
    -> (forall a1 a2 : CTerm,
          equality lib a1 a2 A
          -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))
    -> {f : (forall a1 a2 (e : eqa a1 a2), per)
        , forall a1 a2 (e : eqa a1 a2),
            nuprl lib (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e)}.
Proof.
  introv na F.
  generalize (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & equality lib a1 a2 A}}
                per
                (fun a b => nuprl lib (substc (projT1 a) v1 B1) (substc (projT1 (projT2 a)) v2 B2) b));
    intro C.
  dest_imp C hyp.

  {
    intros; exrepnd.
    generalize (F a1 a2 a3); intros teq.
    unfold tequality in teq; exrepnd; simpl.
    exists eq; sp.
  }

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                                   a1
                                   (existT (fun a2 => equality lib a1 a2 A)
                                           a2
                                           (eq_equality1 lib a1 a2 A eqa e na)))); introv.
  generalize (C0 (existT (fun a1 => {a2 : CTerm & equality lib a1 a2 A})
                         a1
                         (existT (fun a2 => equality lib a1 a2 A)
                                 a2
                                 (eq_equality1 lib a1 a2 A eqa e na)))); simpl; sp.
Qed.


Lemma choice_teq2 {p} :
  forall lib (eqp : per(p)) eqa P ap A bp1 ba1 B1 bp2 ba2 B2,
    nuprl lib P P eqp
    -> (forall p1 p2 (ep : eqp p1 p2),
          nuprl lib (substc p1 ap A) (substc p2 ap A) (eqa p1 p2 ep))
    -> (forall p1 p2 : CTerm,
          equality lib p1 p2 P
          -> forall a1 a2 : CTerm,
               equality lib a1 a2 (substc p1 ap A)
               -> tequality lib (lsubstc2 bp1 p1 ba1 a1 B1) (lsubstc2 bp2 p2 ba2 a2 B2))
    -> {f : (forall p1 p2 (ep : eqp p1 p2) a1 a2 (ea : eqa p1 p2 ep a1 a2), per)
        , forall p1 p2 (ep : eqp p1 p2) a1 a2 (ea : eqa p1 p2 ep a1 a2),
            nuprl lib
                  (lsubstc2 bp1 p1 ba1 a1 B1)
                  (lsubstc2 bp2 p2 ba2 a2 B2)
                  (f p1 p2 ep a1 a2 ea)}.
Proof.
  introv np na F.

  generalize (FunctionalChoice_on
                {p1 : CTerm
                 & {p2 : CTerm
                 & {ep : eqp p1 p2
                 & {a1 : CTerm
                 & {a2 : CTerm
                 & eqa p1 p2 ep a1 a2}}}}}
                per
                (fun a b =>
                   let (p1,a) := a in
                   let (p2,a) := a in
                   let (ep,a) := a in
                   let (a1,a) := a in
                   let (a2,p) := a in
                     nuprl lib
                           (lsubstc2 bp1 p1 ba1 a1 B1)
                           (lsubstc2 bp2 p2 ba2 a2 B2)
                           b)).
  intro k; autodimp k hyp.

  {
    introv; exrepnd.
    generalize (F p1 p2 (eq_equality1 lib p1 p2 P eqp ep np)
                  a1 a0 (eq_equality2 lib a1 a0 (substc p1 ap A) (substc p2 ap A) (eqa p1 p2 ep)
                                      a3 (na p1 p2 ep))); intro teq.
    unfold tequality in teq; auto.
  }

  exrepnd.
  exists (fun p1 p2 ep a1 a2 ea =>
            f (existT (fun p1 => {p2 : CTerm
                                  & {ep : eqp p1 p2
                                  & {a1 : CTerm
                                  & {a2 : CTerm
                                  & eqa p1 p2 ep a1 a2}}}})
                      p1
                      (existT (fun p2 => {ep : eqp p1 p2
                                          & {a1 : CTerm
                                          & {a2 : CTerm
                                          & eqa p1 p2 ep a1 a2}}})
                              p2
                              (existT (fun ep => {a1 : CTerm
                                                  & {a2 : CTerm
                                                  & eqa p1 p2 ep a1 a2}})
                                      ep
                                      (existT (fun a1 => {a2 : CTerm
                                                          & eqa p1 p2 ep a1 a2})
                                              a1
                                              (existT (fun a2 => eqa p1 p2 ep a1 a2)
                                                      a2
                                                      ea)))))).
  introv.
  generalize (k0 (exI(p1, exI(p2, exI(ep, exI(a1, exI(a2, ea))))))); simpl; sp.
Qed.
