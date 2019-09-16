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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


(* MOVE *)
Lemma implies_all_in_bar_ext_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext_ext lib F
    -> all_in_bar_ext (trivial_bar lib) F.
Proof.
  introv i br ext; simpl in *.
  eapply i; eauto 3 with slow.
Qed.

Definition pair2lib_per2 {o}
           {lib A B u v}
           (f : {lib' : library $ lib_extends lib' lib} -> per(o))
           (p : forall a, nuprl (projT1 a) A B (f a) # f a u v) : lib-per(lib,o).
Proof.
  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).

  introv.
  pose proof (p (exI(lib',e))) as a.
  pose proof (p (exI(lib',y))) as b.
  repnd.
  apply nuprl_refl in a0.
  apply nuprl_refl in b0.
  simpl in *.
  eapply nuprl_uniquely_valued; eauto.
Defined.

(* MOVE *)
Lemma choice_ext_lib_eq {o} :
  forall lib (a b A : @CTerm o),
    (forall lib' (x : lib_extends lib' lib), equality lib' a b A)
    -> {eqa : lib-per(lib,o),
        forall lib' (x : lib_extends lib' lib), nuprl lib' A A (eqa lib' x) # eqa lib' x a b}.
Proof.
  introv F.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun x y => nuprl (projT1 x) A A y # y a b)) as C.
  autodimp C hyp.

  {
    unfold equality in F.
    introv; exrepnd; simpl in *; auto.
  }

  clear F.
  exrepnd.

  exists (pair2lib_per2 f C0).
  introv.
  pose proof (C0 (existT (fun lib' => lib_extends lib' lib) lib' x)) as C.
  simpl in *; auto.
Qed.

Definition bar_lib_per2lib_per {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (feqa : bar-lib-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {ext : lib_extends lib' lib1
            , {x : lib_extends lib' lib
            , feqa lib1 br lib' ext x lib' (lib_extends_refl lib') t1 t2}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br ext x0; auto.
  - exists lib1 br ext x0; auto.
Defined.

(* !!MOVE *)
Lemma nuprl_term_equality_symmetric {o} :
  forall lib (A B : @CTerm o) eq,
    nuprl lib A B eq
    -> term_equality_symmetric eq.
Proof.
  introv h.
  pose proof (@nuprl_type_system o) as q.
  nts.
  eapply nts_tes; eauto.
Qed.
Hint Resolve nuprl_term_equality_symmetric : slow.

Lemma all_in_bar_ext_nuprl_implies_nuprl {o} :
  forall (lib : @library o) A B (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> nuprl lib A B (per_bar_eq lib eqa).
Proof.
  introv all.
  apply CL_bar; exists eqa; dands; auto.
Qed.
Hint Resolve all_in_bar_ext_nuprl_implies_nuprl : slow.

Lemma all_in_bar_ext_nuprl_implies_tequality {o} :
  forall (lib : @library o) A B (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> tequality lib A B.
Proof.
  introv all.
  exists (per_bar_eq lib eqa); eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_nuprl_implies_tequality : slow.

Lemma all_in_bar_ext_nuprl_implies_type {o} :
  forall (lib : @library o) A (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => nuprl lib' A A (eqa lib' x))
    -> type lib A.
Proof.
  introv all.
  exists (per_bar_eq lib eqa); eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_nuprl_implies_type : slow.

Lemma all_in_bar_ext_eqorceq_commutes_equality {o} :
  forall (lib : @library o) a b c d A B (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) c d)
    -> equality lib a c A <=> equality lib b d B.
Proof.
  introv n eoa eob; split; intro h.

  - exists (per_bar_eq lib eqa); dands; auto.

    + apply CL_bar; exists eqa; dands; auto.
      fold (@nuprl o).
      eapply in_open_bar_ext_pres; try exact n; clear n; introv n.
      apply nuprl_sym in n; apply nuprl_refl in n; auto.

    + introv br ext; introv.
      exists (trivial_bar lib'0).
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
      introv.
      pose proof (eoa _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as eoa.
      pose proof (eob _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as eob.
      pose proof (n _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as n.
      simpl in *.
      assert (lib_extends lib'1 lib) as xt by eauto 3 with slow.
      eapply equality_monotone in h;[|exact xt].
      pose proof (equality_eq1 lib'1 A B b d (eqa lib'1 (lib_extends_trans e x))) as q.
      apply q; auto; clear q.
      apply nuprl_refl in n; auto.
      eapply eqorceq_commutes_equality; try exact h; try apply eqorceq_sym; eauto;
        eauto 3 with slow.

  - exists (per_bar_eq bar eqa); dands; auto.

    + apply CL_bar; exists bar eqa; dands; auto.
      fold (@nuprl o).
      introv br ext; introv.
      pose proof (n _ br _ ext x) as n; simpl in *.
      apply nuprl_refl in n; auto.

    + introv br ext; introv.
      exists (trivial_bar lib'0).
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
      introv.
      pose proof (eoa _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as eoa.
      pose proof (eob _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as eob.
      pose proof (n _ br lib'1 (lib_extends_trans e ext) (lib_extends_trans e x)) as n.
      simpl in *.
      assert (lib_extends lib'1 lib) as xt by eauto 3 with slow.
      eapply equality_monotone in h;[|exact xt].
      pose proof (equality_eq1 lib'1 A B a c (eqa lib'1 (lib_extends_trans e x))) as q.
      apply q; auto; clear q.
      eapply eqorceq_commutes_equality; try exact h; eauto 3 with slow.
Qed.

Lemma implies_all_in_ex_bar_equality_or_ccequivc_ext {o} :
  forall {lib} (bar : @BarLib o lib) a b A B (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> all_in_ex_bar lib (fun lib' => equality lib' a b A {+} ccequivc_ext lib' a b).
Proof.
  introv an ae.
  exists bar; introv br ext.
  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
  pose proof (an _ br _ ext xt) as an; simpl in *.
  pose proof (ae _ br _ ext xt) as ae; simpl in *.
  apply nuprl_refl in an.
  eapply eqorceq_implies_equality_or_cequivc in ae; eauto.
Qed.
Hint Resolve implies_all_in_ex_bar_equality_or_ccequivc_ext : slow.

(* MOVE *)
Lemma ccequivc_trans {o} :
  forall lib (a b c : @CTerm o),
    (a) ~=~(lib) (b)
    -> (b) ~=~(lib) (c)
    -> (a) ~=~(lib) (c).
Proof.
  introv h q; spcast; eapply cequivc_trans; eauto.
Qed.

(* MOVE *)
Lemma capproxc_trans {o} :
  forall lib (a b c : @CTerm o),
    (a) ~<~(lib) (b)
    -> (b) ~<~(lib) (c)
    -> (a) ~<~(lib) (c).
Proof.
  introv h q; spcast; eapply approxc_trans; eauto.
Qed.

(* MOVE *)
Lemma ccequivc_implies_capproxc {o} :
  forall lib (a b : @CTerm o),
    (a) ~=~(lib) (b)
    -> (a) ~<~(lib) (b).
Proof.
  introv h; spcast; destruct h; auto.
Qed.

(* MOVE *)
Lemma ccequivc_sym {o} :
  forall lib (a b : @CTerm o),
    (a) ~=~(lib) (b)
    -> (b) ~=~(lib) (a).
Proof.
  introv  q; spcast; eapply cequivc_sym; eauto.
Qed.

(* MOVE *)
Lemma implies_all_in_bar_iff_ccequivc {o} :
  forall lib (bar : @BarLib o lib) a b c d a' b' c' d',
    all_in_bar bar (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> all_in_bar bar (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a') ~=~(lib) (b') <=> (c') ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a) ~=~(lib) (b) <=> (c) ~=~(lib) (d)).
Proof.
  introv alla allb allc br ext.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  pose proof (allc lib' br lib'0 ext) as allc.
  simpl in *.
  repnd.
  split; introv q.

  { eapply ccequivc_trans;[eauto|].
    eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
    apply allc.
    eapply ccequivc_trans;[apply ccequivc_sym;eauto|].
    eapply ccequivc_trans;[|eauto]; auto. }

  { eapply ccequivc_trans;[eauto|].
    eapply ccequivc_trans;[|apply ccequivc_sym;eauto].
    apply allc.
    eapply ccequivc_trans;[apply ccequivc_sym;eauto|].
    eapply ccequivc_trans;[|eauto]; auto. }
Qed.

(* MOVE *)
Lemma implies_all_in_bar_iff_capproxc {o} :
  forall lib (bar : @BarLib o lib) a b c d a' b' c' d',
    all_in_bar bar (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> all_in_bar bar (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> all_in_bar bar (fun lib => (a') ~<~(lib) (b') <=> (c') ~<~(lib) (d'))
    -> all_in_bar bar (fun lib => (a) ~<~(lib) (b) <=> (c) ~<~(lib) (d)).
Proof.
  introv alla allb allc br ext.
  pose proof (alla lib' br lib'0 ext) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  pose proof (allc lib' br lib'0 ext) as allc.
  simpl in *.
  repnd.
  split; introv q.

  { eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
    apply allc.
    eapply capproxc_trans;[apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;eauto]; auto. }

  { eapply capproxc_trans;[apply ccequivc_implies_capproxc;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto].
    apply allc.
    eapply capproxc_trans;[apply ccequivc_implies_capproxc;apply ccequivc_sym;eauto|].
    eapply capproxc_trans;[|apply ccequivc_implies_capproxc;eauto]; auto. }
Qed.

(*(* MOVE *)
Lemma computes_to_valc_ceq_bar_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    iscvalue v
    -> v ==b==>(bar) v.
Proof.
  introv isv br ext.
  exists v; dands; spcast; eauto 3 with slow.
  apply computes_to_valc_refl; auto.
Qed.
Hint Resolve computes_to_valc_ceq_bar_refl : refl.*)

(* !!MOVE *)
Lemma nuprl_per_bar_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i,
    nuprl lib (mkc_uni i) (mkc_uni i) (per_bar_eq bar (univi_eq_lib_per lib i)).
Proof.
  introv.
  apply CL_init; exists bar (univi_eq_lib_per lib i); dands; tcsp.
  introv br ext; introv; simpl.
  exists (S i).
  apply univi_exists_iff; exists i; dands; spcast; tcsp; eauto 3 with slow.
Qed.
Hint Resolve nuprl_per_bar_eq_bar : slow.

(* MOVE *)
Hint Resolve approxc_refl : refl.

(* MOVE *)
Lemma all_in_bar_iff_capproxc_same {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~<~(lib) (a) <=> (b) ~<~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_capproxc_same : slow.

(* MOVE *)
Lemma in_ext_iff_capproxc_same {o} :
  forall (lib : @library o) a b,
    in_ext lib (fun lib => (a) ~<~(lib) (a) <=> (b) ~<~(lib) (b)).
Proof.
  introv ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve in_ext_iff_capproxc_same : slow.

(* MOVE *)
Lemma all_in_bar_iff_capproxc_same2 {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~<~(lib) (b) <=> (a) ~<~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_capproxc_same2 : slow.

(* MOVE *)
Lemma in_ext_iff_capproxc_same2 {o} :
  forall (lib : @library o) a b,
    in_ext lib (fun lib => (a) ~<~(lib) (b) <=> (a) ~<~(lib) (b)).
Proof.
  introv ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve in_ext_iff_capproxc_same2 : slow.

(* MOVE *)
Lemma all_in_bar_iff_ccequivc_same {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~=~(lib) (a) <=> (b) ~=~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_ccequivc_same : slow.

(* MOVE *)
Lemma in_ext_iff_ccequivc_same {o} :
  forall (lib : @library o) a b,
    in_ext lib (fun lib => (a) ~=~(lib) (a) <=> (b) ~=~(lib) (b)).
Proof.
  introv ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve in_ext_iff_ccequivc_same : slow.

(* MOVE *)
Lemma all_in_bar_iff_ccequivc_same2 {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    all_in_bar bar (fun lib => (a) ~=~(lib) (b) <=> (a) ~=~(lib) (b)).
Proof.
  introv br ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve all_in_bar_iff_ccequivc_same2 : slow.

(* MOVE *)
Lemma in_ext_iff_ccequivc_same2 {o} :
  forall (lib : @library o) a b,
    in_ext lib (fun lib => (a) ~=~(lib) (b) <=> (a) ~=~(lib) (b)).
Proof.
  introv ext; split; introv h; spcast; auto; eauto 3 with slow refl.
Qed.
Hint Resolve in_ext_iff_ccequivc_same2 : slow.

(* MOVE *)
Lemma all_in_bar_ccomputes_to_valc_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    iscvalue v
    -> all_in_bar bar (fun lib => v ===>(lib) v).
Proof.
  introv isv br ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ccomputes_to_valc_refl : refl.

(* MOVE *)
Lemma all_in_bar_ccequivc_refl {o} :
  forall {lib} (bar : @BarLib o lib) v,
    all_in_bar bar (fun lib => v ~=~(lib) v).
Proof.
  introv br ext; spcast; auto.
Qed.
Hint Resolve all_in_bar_ccequivc_refl : refl.

(* MOVE *)
Lemma implies_all_in_bar_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F
    -> all_in_bar (trivial_bar lib) F.
Proof.
  introv i br ext; simpl in *.
  eapply i; eauto 3 with slow.
Qed.

(* MOVE *)
Hint Resolve computes_to_valc_refl : refl.

Lemma all_in_ex_bar_iff_same {o} :
  forall (lib : @library o) (F : library -> Prop),
    all_in_ex_bar lib (fun lib => F lib <=> F lib).
Proof.
  introv; exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar.
  introv ext; tcsp.
Qed.
Hint Resolve all_in_ex_bar_iff_same : refl.

Lemma equality_implies_all_in_ex_bar_equality_or_ccequivc_ext {o} :
  forall lib (a b A : @CTerm o),
    equality lib a b A
    -> all_in_ex_bar lib (fun lib => equality lib a b A {+} ccequivc_ext lib a b).
Proof.
  introv ea.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar; introv e.
  left; eauto 3 with slow.
Qed.
Hint Resolve equality_implies_all_in_ex_bar_equality_or_ccequivc_ext : slow.

Definition equorsq_bar {o} lib (t1 t2 T : @CTerm o) :=
  all_in_ex_bar lib (fun lib => equorsq lib t1 t2 T).

Definition equorsq2_bar {o} lib (t1 t2 t3 t4 T : @CTerm o) :=
  equorsq_bar lib t1 t2 T # equorsq_bar lib t3 t4 T.

Lemma fold_equorsq_bar {p} :
  forall lib (t1 t2 T : @CTerm p),
    all_in_ex_bar lib (fun lib => equality lib t1 t2 T {+} ccequivc_ext lib t1 t2) = equorsq_bar lib t1 t2 T.
Proof. sp. Qed.

Lemma fold_equorsq2_bar {p} :
  forall lib (t1 t2 t3 t4 T : @CTerm p),
    (equorsq_bar lib t1 t2 T # equorsq_bar lib t3 t4 T) = equorsq2_bar lib t1 t2 t3 t4 T.
Proof. sp. Qed.

Lemma equality_respects_equorsq_bar_right {o} :
  forall lib (a1 a2 a3 T : @CTerm o),
    equality lib a1 a2 T
    -> equorsq_bar lib a2 a3 T
    -> equality lib a1 a3 T.
Proof.
  introv ea equ.
  unfold equorsq_bar in equ.
  dup ea as xxx.
  unfold equality in ea; exrepnd.

  pose proof (nuprl_monotone_func lib T T eq ea1) as tya; exrepnd.
  rename eq' into eqa.

  unfold all_in_ex_bar in *; exrepnd.
  exists (per_bar_eq bar eqa).
  dands; auto; eauto 3 with slow.

  {
    apply CL_bar; exists bar eqa; dands; auto.
    introv br ext; introv.
    fold (@nuprl o).
    pose proof (tya0 _ x) as tya0; repnd; auto.
  }

  {
    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
    pose proof (tya0 _ (lib_extends_trans e x)) as tya0; repnd; auto.
    pose proof (equ0 _ br _ (lib_extends_trans e ext)) as equ0; simpl in *.
    apply tya0 in ea0.
    assert (lib_extends lib'1 lib) as xt by eauto 3 with slow.
    eapply equality_monotone in xxx;[|exact xt].
    unfold equorsq in *; repndors.

    - eapply equality_trans in equ0;[|exact xxx].
      apply (equality_eq1 lib'1 T T a1 a3 (eqa lib'1 (lib_extends_trans e x))); auto.

    - apply (equality_eq1 lib'1 T T a1 a3 (eqa lib'1 (lib_extends_trans e x))); auto.
      apply (equality_eq1 lib'1 T T a1 a2 (eqa lib'1 (lib_extends_trans e x))) in ea0; auto.
      eauto 3 with slow.
      eapply equality_respects_cequivc_right; eauto.
  }
Qed.
Hint Resolve equality_respects_equorsq_bar_right : slow.

Lemma equality_respects_equorsq_bar_left {o} :
  forall lib (a1 a2 a3 T : @CTerm o),
    equality lib a1 a2 T
    -> equorsq_bar lib a1 a3 T
    -> equality lib a3 a2 T.
Proof.
  introv ea equ.
  pose proof (equality_respects_equorsq_bar_right lib a2 a1 a3 T) as q.
  repeat (autodimp q hyp); apply equality_sym; auto.
Qed.
Hint Resolve equality_respects_equorsq_bar_left : slow.

Lemma equality_respects_equorsq_bar1 {o} :
  forall lib (a1 a2 a3 T : @CTerm o),
    equality lib a1 a2 T
    -> equorsq_bar lib a1 a3 T
    -> equality lib a1 a3 T.
Proof.
  introv ea equ.
  pose proof (equality_respects_equorsq_bar_right lib a2 a1 a3 T) as q.
  repeat (autodimp q hyp).
  { apply equality_sym; auto. }
  eapply equality_trans; eauto.
Qed.
Hint Resolve equality_respects_equorsq_bar1 : slow.

Lemma equality_respects_equorsq_bar2 {o} :
  forall lib (a1 a2 a3 T : @CTerm o),
    equality lib a2 a1 T
    -> equorsq_bar lib a1 a3 T
    -> equality lib a1 a3 T.
Proof.
  introv ea equ.
  eapply equality_respects_equorsq_bar1; auto.
  apply equality_sym; eauto.
Qed.
Hint Resolve equality_respects_equorsq_bar2 : slow.

Lemma all_in_bar_exists_per_implies_exists {o} :
  forall {lib} (bar : @BarLib o lib)
         (F : forall lib' (eqa : per(o)), Prop),
    all_in_bar bar (fun lib' => {eqa : per(o) , F lib' eqa})
    ->
    exists (feqa : bar-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 (feqa lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => per(o))
                (fun x e => F (plb_lib2 _ x)
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

Lemma all_in_ex_bar_tequality_implies_tequality {o} :
  forall lib (T1 T2 : @CTerm o),
    all_in_ex_bar lib (fun lib => tequality lib T1 T2)
    -> tequality lib T1 T2.
Proof.
  introv a.
  unfold all_in_ex_bar in a; exrepnd.
  unfold tequality in a0.

  apply all_in_bar_exists_per_implies_exists in a0; exrepnd.
  exists (per_bar_eq bar (bar_per2lib_per feqa)).
  apply CL_bar; exists bar (bar_per2lib_per feqa); dands; auto.
  fold (@nuprl o).
  introv br ext; introv.
  pose proof (a1 _ br _ ext x) as q; simpl in *; auto.

  eapply type_extensionality_nuprl;[eauto|].
  introv; split; intro h.

  { exists lib' br ext x; auto. }

  exrepnd.
  pose proof (a1 _ br0 _ ext0 x0) as w.
  apply nuprl_refl in w; apply nuprl_refl in q.
  eapply nuprl_uniquely_valued in w; try exact q.
  apply w; auto.
Qed.
Hint Resolve all_in_ex_bar_tequality_implies_tequality : slow.

Hint Resolve meta_type_monotone : slow.

Lemma inhabited_type_iff_exists_per {o} :
  forall lib (T : @CTerm o),
    inhabited_type lib T
    <=> exists eq t, nuprl lib T T eq # eq t t.
Proof.
  introv.
  unfold inhabited_type, member, equality; split; intro h; exrepnd; eexists; eexists; eauto.
Qed.

Lemma all_in_ex_bar_modus_ponens1 {o} :
  forall (lib : @library o) (F G : library -> Prop),
    in_ext lib (fun lib => G lib -> F lib)
    -> all_in_ex_bar lib G
    -> all_in_ex_bar lib F.
Proof.
  introv h q.
  unfold all_in_ex_bar in *; exrepnd; exists bar.
  introv br ext; pose proof (q0 _ br _ ext) as q0; simpl in *.
  apply h; eauto 3 with slow.
Qed.

Lemma all_in_ex_bar_modus_ponens2 {o} :
  forall (lib : @library o) (G H F : library -> Prop),
    in_ext lib (fun lib => G lib -> H lib -> F lib)
    -> all_in_ex_bar lib G
    -> all_in_ex_bar lib H
    -> all_in_ex_bar lib F.
Proof.
  introv h q w.
  unfold all_in_ex_bar in *; exrepnd.
  apply (implies_all_in_bar_intersect_bars_left _ bar) in q0.
  apply (implies_all_in_bar_intersect_bars_right _ bar0) in w0.
  remember (intersect_bars bar0 bar) as bar'.
  clear dependent bar0.
  clear dependent bar.
  exists bar'.
  introv br ext.
  pose proof (q0 _ br _ ext) as q0; simpl in *.
  pose proof (w0 _ br _ ext) as w0; simpl in *.
  apply h; eauto 3 with slow.
Qed.

Hint Resolve inhabited_type_if_equality : slow.

Lemma all_in_ex_bar_type_implies_type {o} :
  forall lib (A : @CTerm o),
    all_in_ex_bar lib (fun lib' => type lib' A)
    -> type lib A.
Proof.
  introv a.
  apply all_in_ex_bar_tequality_implies_tequality; auto.
Qed.

Definition inhabited_type_bar {o} lib (A : @CTerm o) :=
  all_in_ex_bar lib (fun lib => inhabited_type lib A).

Lemma collapse_all_in_ex_bar {o} :
  forall (lib : @library o) F,
    all_in_ex_bar lib F <=> all_in_ex_bar lib (fun lib => all_in_ex_bar lib F).
Proof.
  unfold all_in_ex_bar; introv.
  rw <- @collapse2bars; split; intro h; exrepnd; exists bar;
    introv br ext; try intro x; eapply h0; eauto 3 with slow.
Qed.

Lemma all_in_ex_bar_equality_implies_equality {o} :
  forall lib (a b A : @CTerm o),
    all_in_ex_bar lib (fun lib => equality lib a b A)
    -> equality lib a b A.
Proof.
  introv h.
  unfold all_in_ex_bar in h; exrepnd.
  unfold equality in h0.

  apply all_in_bar_exists_per_implies_exists in h0; exrepnd.
  exists (per_bar_eq bar (bar_per2lib_per feqa)).
  dands; auto.

  {
    eapply local_ts_nuprl;[apply eq_term_equals_refl|].
    introv br ext; introv; simpl.
    pose proof (h1 _ br _ ext x) as q; repnd.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro h.

    { exists lib' br ext x; auto. }

    exrepnd.
    pose proof (h1 _ br0 _ ext0 x0) as w; repnd.
    apply nuprl_refl in w0; apply nuprl_refl in q0.
    eapply nuprl_uniquely_valued in w0; try exact q0.
    apply w0; auto.
  }

  {
    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl.
    pose proof (h1 _ br _ (lib_extends_trans e ext) (lib_extends_trans e x)) as h1; repnd.
    eexists; eexists; eexists; eexists; eauto.
  }
Qed.
Hint Resolve all_in_ex_bar_equality_implies_equality : slow.

Definition computes_to_valc_ex_bar {o} lib (a b : @CTerm o) :=
  all_in_ex_bar lib (fun lib => a ===>(lib) b).
Notation "t1 ===b>( lib ) t2" := (computes_to_valc_ex_bar lib t1 t2) (at level 0).

Lemma computes_to_valc_implies_computes_to_valc_ex_bar {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> a ===b>(lib) b.
Proof.
  introv comp.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar; introv x; spcast; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_implies_computes_to_valc_ex_bar : slow.

Lemma in_ext_implies_all_in_ex_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F -> all_in_ex_bar lib F.
Proof.
  introv h.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar; auto.
Qed.

Lemma non_dep_all_in_ex_bar_implies {o} :
  forall (lib : @library o) P,
    all_in_ex_bar lib (fun _ => P) -> P.
Proof.
  introv h.
  unfold all_in_ex_bar in h; exrepnd.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (h0 _ b0 _ (lib_extends_refl lib')) as h0; simpl in *; auto.
Qed.

Lemma lib_extends_preserves_all_in_ex_bar {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) F,
    all_in_ex_bar lib F
    -> all_in_ex_bar lib' F.
Proof.
  introv x h.
  unfold all_in_ex_bar in *; exrepnd.
  exists (raise_bar bar x); introv br ext; simpl in *; exrepnd.
  apply (h0 _ br1); eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_all_in_ex_bar : slow.

Lemma lib_extends_inhabited_type {o} :
  forall {lib lib'} (x : lib_extends lib' lib) (T : @CTerm o),
    inhabited_type lib T
    -> inhabited_type lib' T.
Proof.
  introv x inh.
  unfold inhabited_type in *; exrepnd; exists t; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_inhabited_type : slow.

Lemma inhabited_type_implies_inhabited_type_bar {o} :
  forall lib (T : @CTerm o),
    inhabited_type lib T -> inhabited_type_bar lib T.
Proof.
  introv h.
  apply in_ext_implies_all_in_ex_bar; introv x; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_implies_inhabited_type_bar : slow.

Lemma fold_inhabited_type_bar {o} :
  forall lib (A : @CTerm o),
    all_in_ex_bar lib (fun lib => inhabited_type lib A)
    = inhabited_type_bar lib A.
Proof.
  tcsp.
Qed.

Lemma inhabited_type_bar_cequivc {p} :
  forall lib (a b : @CTerm p),
    ccequivc_ext lib a b
    -> inhabited_type_bar lib a
    -> inhabited_type_bar lib b.
Proof.
  introv ceq inh.
  eapply all_in_ex_bar_modus_ponens1;try exact inh; clear inh; introv w inh; exrepnd; spcast.
  eapply inhabited_type_cequivc; eauto; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_bar_cequivc : slow.

Lemma inhabited_type_bar_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@inhabited_type_bar o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_ccequivc_ext lib) in aeq; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_bar_respects_alphaeqc : respects.

Lemma computes_to_valc_implies_reduces_toc {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    -> reduces_toc lib t1 t2.
Proof.
  introv comp.
  allrw @computes_to_valc_iff_reduces_toc; sp.
Qed.
Hint Resolve computes_to_valc_implies_reduces_toc : slow.

Definition ccequivc_ext_bar {o} lib (t1 t2 : @CTerm o) :=
  all_in_ex_bar lib (fun lib => ccequivc_ext lib t1 t2).

Definition ccequivc_bar {o} lib (a b : @CTerm o) :=
  all_in_ex_bar lib (fun lib => ccequivc lib a b).

Lemma ccequivc_ext_bar_iff_ccequivc_bar {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext_bar lib a b <=> ccequivc_bar lib a b.
Proof.
  introv; split; introv e.

  - eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; eauto 3 with slow.

  - unfold ccequivc_bar, ccequivc_ext_bar, all_in_ex_bar in *; exrepnd.
    exists bar.
    introv br ext x.
    apply (e0 _ br); eauto 3 with slow.
Qed.

Lemma all_in_ex_bar_member_implies_member {o} :
  forall lib (a A : @CTerm o),
    all_in_ex_bar lib (fun lib => member lib a A)
    -> member lib a A.
Proof.
  introv h.
  apply all_in_ex_bar_equality_implies_equality in h; auto.
Qed.

Lemma univ_uniquely_valued {o} :
  @uniquely_valued o univ.
Proof.
  apply univ_type_system.
Qed.
Hint Resolve univ_uniquely_valued : slow.

Lemma all_in_ex_bar_teq_and_eq_implies_teq_and_eq {o} :
  forall lib (A B a b T : @CTerm o),
    all_in_ex_bar lib (fun lib => tequality lib A B # equality lib a b T)
    -> tequality lib A B # equality lib a b T.
Proof.
  introv e; dands.

  - apply all_in_ex_bar_tequality_implies_tequality; auto.
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; eauto 3 with slow.

  - apply all_in_ex_bar_equality_implies_equality; auto.
    eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; eauto 3 with slow.
Qed.

Lemma inhabited_type_implies_type {o} :
  forall lib (T : @CTerm o),
    inhabited_type lib T
    -> type lib T.
Proof.
  introv e.
  unfold inhabited_type in e; exrepnd.
  apply inhabited_implies_tequality in e0; auto.
Qed.
Hint Resolve inhabited_type_implies_type : slow.

Lemma inhabited_type_bar_implies_type {o} :
  forall lib (T : @CTerm o),
    inhabited_type_bar lib T
    -> type lib T.
Proof.
  introv e.
  apply all_in_ex_bar_type_implies_type.
  eapply all_in_ex_bar_modus_ponens1;[|exact e]; clear e; introv x e; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_bar_implies_type : slow.

Lemma all_in_ex_bar_modus_ponens3 {o} :
  forall (lib : @library o) (G H K F : library -> Prop),
    in_ext lib (fun lib => G lib -> H lib -> K lib -> F lib)
    -> all_in_ex_bar lib G
    -> all_in_ex_bar lib H
    -> all_in_ex_bar lib K
    -> all_in_ex_bar lib F.
Proof.
  introv h q z w.
  unfold all_in_ex_bar in *; exrepnd.
  apply (implies_all_in_bar_intersect_bars_left _ bar) in q0.
  apply (implies_all_in_bar_intersect_bars_left _ bar0) in q0.
  apply (implies_all_in_bar_intersect_bars_right _ bar1) in w0.
  apply (implies_all_in_bar_intersect_bars_left _ bar0) in w0.
  apply (implies_all_in_bar_intersect_bars_right _ (intersect_bars bar1 bar)) in z0.
  remember (intersect_bars (intersect_bars bar1 bar) bar0) as bar'.
  clear dependent bar0.
  clear dependent bar1.
  clear dependent bar.
  exists bar'.
  introv br ext.
  pose proof (q0 _ br _ ext) as q0; simpl in *.
  pose proof (w0 _ br _ ext) as w0; simpl in *.
  pose proof (z0 _ br _ ext) as z0; simpl in *.
  apply h; eauto 3 with slow.
Qed.

Lemma ccequivc_bar_refl {o} :
  forall lib (T : @CTerm o),
    ccequivc_bar lib T T.
Proof.
  introv.
  apply in_ext_implies_all_in_ex_bar; introv x; spcast; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_bar_refl : slow.

Lemma ccequivc_ext_beta {o} :
  forall lib v (b : @CVTerm o [v]) (a : CTerm),
    ccequivc_ext lib (mkc_apply (mkc_lam v b) a) (b) [[v \\ a]].
Proof.
  introv ext; spcast; apply cequivc_beta.
Qed.

Ltac betared2 :=
  match goal with
  (* on conclusion *)
  | [ lib : library |- context[mkc_apply (mkc_lam ?v ?b) ?a] ] =>
    let h := fresh "h" in
    pose proof (ccequivc_ext_beta lib v b a) as h;
    first
      [ eapply equality_respects_cequivc_left;
        [apply ccequivc_ext_sym;exact h|]
      | eapply equality_respects_cequivc_right;
        [apply ccequivc_ext_sym;exact h|]
      ];
    clear h
  end.

Lemma equality_implies_all_in_ex_bar_equality {o} :
  forall lib (a b : @CTerm o) A,
    equality lib a b A
    -> all_in_ex_bar lib (fun lib => equality lib a b A).
Proof.
  introv equ.
  apply in_ext_implies_all_in_ex_bar; introv x; eauto 3 with slow.
Qed.

Lemma all_in_ex_bar_modus_ponens4 {o} :
  forall (lib : @library o) (G H K L F : library -> Prop),
    in_ext lib (fun lib => G lib -> H lib -> K lib -> L lib -> F lib)
    -> all_in_ex_bar lib G
    -> all_in_ex_bar lib H
    -> all_in_ex_bar lib K
    -> all_in_ex_bar lib L
    -> all_in_ex_bar lib F.
Proof.
  introv h q z w x.
  unfold all_in_ex_bar in *; exrepnd.
  apply (implies_all_in_bar_intersect_bars_left _ bar) in q0.
  apply (implies_all_in_bar_intersect_bars_left _ bar0) in q0.
  apply (implies_all_in_bar_intersect_bars_left _ bar1) in q0.
  apply (implies_all_in_bar_intersect_bars_right _ (intersect_bars (intersect_bars bar2 bar) bar0)) in z0.
  apply (implies_all_in_bar_intersect_bars_right _ (intersect_bars bar2 bar)) in w0.
  apply (implies_all_in_bar_intersect_bars_left _ bar1) in w0.
  apply (implies_all_in_bar_intersect_bars_right _ bar2) in x0.
  apply (implies_all_in_bar_intersect_bars_left _ bar0) in x0.
  apply (implies_all_in_bar_intersect_bars_left _ bar1) in x0.
  remember (intersect_bars (intersect_bars (intersect_bars bar2 bar) bar0) bar1) as bar'.
  clear dependent bar2.
  clear dependent bar0.
  clear dependent bar1.
  clear dependent bar.
  exists bar'.
  introv br ext.
  pose proof (q0 _ br _ ext) as q0; simpl in *.
  pose proof (w0 _ br _ ext) as w0; simpl in *.
  pose proof (z0 _ br _ ext) as z0; simpl in *.
  pose proof (x0 _ br _ ext) as x0; simpl in *.
  apply h; eauto 3 with slow.
Qed.

Lemma implies_all_in_ex_bar_in_ext {o} :
  forall (lib : @library o) F,
    all_in_ex_bar lib F -> all_in_ex_bar lib (fun lib' => in_ext lib' F).
Proof.
  introv h; unfold all_in_ex_bar in *; exrepnd; exists bar.
  apply implies_all_in_bar_in_ext; auto.
Qed.

Lemma eqorceq_ext_ccequivc_ext_trans_left {o} :
  forall lib (a b c : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> ccequivc_ext lib a b
    -> eqorceq_ext lib eqa b c
    -> eqorceq_ext lib eqa a c.
Proof.
  introv trans sym resp ceq eoc; introv.
  pose proof (eoc _ e) as eoc.
  simpl in *; spcast.
  unfold eqorceq in *; repndors; tcsp.

  - left.
    pose proof (resp _ e) as resp; simpl in resp.
    pose proof (resp b a) as w; repeat (autodimp w hyp); eauto 3 with slow;[|].
    { eapply trans;[eauto|]; apply sym; auto. }
    apply sym in w.
    eapply trans; eauto.

  - right.
    eapply ccequivc_ext_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma eqorceq_ext_ccequivc_ext_trans_right {o} :
  forall lib (a b c : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> eqorceq_ext lib eqa a b
    -> ccequivc_ext lib b c
    -> eqorceq_ext lib eqa a c.
Proof.
  introv trans sym resp eoc ceq; introv.
  pose proof (eoc _ e) as eoc.
  simpl in *; spcast.
  unfold eqorceq in *; repndors; tcsp.

  - left.
    pose proof (resp _ e) as resp; simpl in resp.
    pose proof (resp b c) as w; repeat (autodimp w hyp); eauto 3 with slow;[|].
    { eapply trans;[|eauto]; apply sym; auto. }
    eapply trans; eauto.

  - right.
    eapply ccequivc_ext_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma in_ext_computes_to_valc_implies_ccomputes_to_valc_ext {o} :
  forall lib (a b : @CTerm o),
    in_ext lib (fun lib => ccomputes_to_valc lib a b)
    -> ccomputes_to_valc_ext lib a b.
Proof.
  introv h ext; apply h in ext; clear h; spcast.
  exists b; dands; spcast; eauto 2 with slow.
Qed.
