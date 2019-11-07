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


(*(* MOVE *)
Lemma implies_all_in_bar_ext_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext_ext lib F
    -> all_in_bar_ext (trivial_bar lib) F.
Proof.
  introv i br ext; simpl in *.
  eapply i; eauto 3 with slow.
Qed.*)

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

(*Definition bar_lib_per2lib_per {o}
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
Defined.*)

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

    + eapply in_open_bar_ext_comb; try exact n; clear n.
      eapply in_open_bar_ext_comb; try exact eoa; clear eoa.
      eapply in_open_bar_ext_pres; try exact eob; clear eob; introv eob eoa n.
      eapply equality_monotone in h;[|exact e].
      pose proof (equality_eq1 lib' A B b d (eqa lib' e)) as q.
      apply q; auto; clear q.
      apply nuprl_refl in n; auto.
      eapply eqorceq_commutes_equality; try exact h; try apply eqorceq_sym; eauto;
        eauto 3 with slow.

  - exists (per_bar_eq lib eqa); dands; auto.

    + apply CL_bar; exists eqa; dands; auto.
      fold (@nuprl o).
      eapply in_open_bar_ext_pres; try exact n; clear n; introv n.
      apply nuprl_refl in n; auto.

    + eapply in_open_bar_ext_comb; try exact n; clear n.
      eapply in_open_bar_ext_comb; try exact eoa; clear eoa.
      eapply in_open_bar_ext_pres; try exact eob; clear eob; introv eob eoa n.
      eapply equality_monotone in h;[|exact e].
      pose proof (equality_eq1 lib' A B a c (eqa lib' e)) as q.
      apply q; auto; clear q.
      eapply eqorceq_commutes_equality; try exact h; eauto 3 with slow.
Qed.

Lemma implies_all_in_ex_bar_equality_or_ccequivc_ext {o} :
  forall (lib : @library o) a b A B (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> in_open_bar lib (fun lib' => equality lib' a b A {+} ccequivc_ext lib' a b).
Proof.
  introv an ae.
  eapply in_open_bar_comb2; try exact an; clear an.
  eapply in_open_bar_ext_pres; try exact ae; clear ae; introv ae an.
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
  forall (lib : @library o) a b c d a' b' c' d',
    in_open_bar lib (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> in_open_bar lib (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> in_open_bar lib (fun lib => (a') ~=~(lib) (b') <=> (c') ~=~(lib) (d'))
    -> in_open_bar lib (fun lib => (a) ~=~(lib) (b) <=> (c) ~=~(lib) (d)).
Proof.
  introv alla allb allc.
  eapply in_open_bar_comb; try exact alla; clear alla.
  eapply in_open_bar_comb; try exact allb; clear allb.
  eapply in_open_bar_pres; try exact allc; clear allc; introv ext allc allb alla.
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
  forall (lib : @library o) a b c d a' b' c' d',
    in_open_bar lib (fun lib => (a) ~=~(lib) (a') # (b) ~=~(lib) (b'))
    -> in_open_bar lib (fun lib => (c) ~=~(lib) (c') # (d) ~=~(lib) (d'))
    -> in_open_bar lib (fun lib => (a') ~<~(lib) (b') <=> (c') ~<~(lib) (d'))
    -> in_open_bar lib (fun lib => (a) ~<~(lib) (b) <=> (c) ~<~(lib) (d)).
Proof.
  introv alla allb allc.
  eapply in_open_bar_comb; try exact alla; clear alla.
  eapply in_open_bar_comb; try exact allb; clear allb.
  eapply in_open_bar_pres; try exact allc; clear allc; introv ext allc allb alla.
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
  forall (lib : @library o) i,
    nuprl lib (mkc_uni i) (mkc_uni i) (per_bar_eq lib (univi_eq_lib_per lib i)).
Proof.
  introv.
  apply CL_init; exists (univi_eq_lib_per lib i); dands; tcsp.
  apply in_ext_ext_implies_in_open_bar_ext; introv.
  exists (S i).
  apply univi_exists_iff; exists i; dands; spcast; tcsp; eauto 3 with slow.
Qed.
Hint Resolve nuprl_per_bar_eq_bar : slow.

(* MOVE *)
Hint Resolve approxc_refl : refl.

(* MOVE *)
Lemma all_in_bar_iff_capproxc_same {o} :
  forall (lib : @library o) a b,
    in_open_bar lib (fun lib => (a) ~<~(lib) (a) <=> (b) ~<~(lib) (b)).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext.
  split; introv h; spcast; auto; eauto 3 with slow refl.
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
  forall (lib : @library o) a b,
    in_open_bar lib (fun lib => (a) ~<~(lib) (b) <=> (a) ~<~(lib) (b)).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext.
  split; introv h; spcast; auto; eauto 3 with slow refl.
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
  forall (lib : @library o) a b,
    in_open_bar lib (fun lib => (a) ~=~(lib) (a) <=> (b) ~=~(lib) (b)).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext.
  split; introv h; spcast; auto; eauto 3 with slow refl.
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
  forall (lib : @library o) a b,
    in_open_bar lib (fun lib => (a) ~=~(lib) (b) <=> (a) ~=~(lib) (b)).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext.
  split; introv h; spcast; auto; eauto 3 with slow refl.
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
  forall (lib : @library o) v,
    iscvalue v
    -> in_open_bar lib (fun lib => v ===>(lib) v).
Proof.
  introv isv; apply in_ext_implies_in_open_bar; introv ext.
  spcast; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ccomputes_to_valc_refl : refl.

(* MOVE *)
Lemma all_in_bar_ccequivc_refl {o} :
  forall (lib : @library o) v,
    in_open_bar lib (fun lib => v ~=~(lib) v).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext; spcast; auto.
Qed.
Hint Resolve all_in_bar_ccequivc_refl : refl.

(* MOVE *)
Lemma implies_all_in_bar_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F
    -> in_open_bar lib F.
Proof.
  introv i; apply in_ext_implies_in_open_bar; introv ext.
  eapply i; eauto 3 with slow.
Qed.

(* MOVE *)
Hint Resolve computes_to_valc_refl : refl.

Lemma all_in_ex_bar_iff_same {o} :
  forall (lib : @library o) (F : library -> Prop),
    in_open_bar lib (fun lib => F lib <=> F lib).
Proof.
  introv; apply in_ext_implies_in_open_bar; introv ext; tcsp.
Qed.
Hint Resolve all_in_ex_bar_iff_same : refl.

Lemma equality_implies_all_in_ex_bar_equality_or_ccequivc_ext {o} :
  forall lib (a b A : @CTerm o),
    equality lib a b A
    -> in_open_bar lib (fun lib => equality lib a b A {+} ccequivc_ext lib a b).
Proof.
  introv ea.
  apply in_ext_implies_in_open_bar; introv ext.
  left; eauto 3 with slow.
Qed.
Hint Resolve equality_implies_all_in_ex_bar_equality_or_ccequivc_ext : slow.

Definition equorsq_bar {o} lib (t1 t2 T : @CTerm o) :=
  in_open_bar lib (fun lib => equorsq lib t1 t2 T).

Definition equorsq2_bar {o} lib (t1 t2 t3 t4 T : @CTerm o) :=
  equorsq_bar lib t1 t2 T # equorsq_bar lib t3 t4 T.

Lemma fold_equorsq_bar {p} :
  forall lib (t1 t2 T : @CTerm p),
    in_open_bar lib (fun lib => equality lib t1 t2 T {+} ccequivc_ext lib t1 t2) = equorsq_bar lib t1 t2 T.
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

  exists (per_bar_eq lib eqa).
  dands; auto; eauto 3 with slow.

  {
    apply CL_bar; exists eqa; dands; auto.
    apply in_ext_ext_implies_in_open_bar_ext; introv.
    fold (@nuprl o).
    pose proof (tya0 _ e) as tya0; repnd; auto.
  }

  {
    eapply in_open_bar_ext_comb2; eauto; clear equ.
    apply in_ext_ext_implies_in_open_bar_ext; introv equ.

    pose proof (tya0 _ e) as tya0; repnd; auto.
    apply tya0 in ea0.
    eapply equality_monotone in xxx;[|exact e].
    unfold equorsq in *; repndors.

    - eapply equality_trans in equ;[|exact xxx].
      apply (equality_eq1 lib' T T a1 a3 (eqa lib' e)); auto.

    - apply (equality_eq1 lib' T T a1 a3 (eqa lib' e)); auto.
      apply (equality_eq1 lib' T T a1 a2 (eqa lib' e)) in ea0; auto.
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

(*Lemma all_in_bar_exists_per_implies_exists {o} :
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
Qed.*)

Lemma in_open_bar_implies_in_open_bar_ext {o} :
  forall (lib : @library o) (F : library -> Prop),
    in_open_bar lib F
    -> in_open_bar_ext lib (fun lib' _ => F lib').
Proof.
  introv h; eapply in_open_bar_ext_comb2; eauto; clear h.
  apply in_ext_ext_implies_in_open_bar_ext; introv ext h; tcsp.
Qed.

Lemma all_in_ex_bar_tequality_implies_tequality {o} :
  forall lib (T1 T2 : @CTerm o),
    in_open_bar lib (fun lib => tequality lib T1 T2)
    -> tequality lib T1 T2.
Proof.
  introv a.
  unfold tequality in a.

  apply in_open_bar_implies_in_open_bar_ext in a.
  apply in_open_bar_ext_choice in a; exrepnd.
  apply in_open_bar_eqa_choice_non_dep in a0; exrepnd.

  exists (per_bar_eq lib (lib_fun_non_dep_eqa Feqa)).
  apply CL_bar; exists (lib_fun_non_dep_eqa Feqa); dands; auto.
  fold (@nuprl o).
  introv ext.
  assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
  exists (Flib _ ext) xta.
  introv xtb; introv.

  pose proof (a1 _ ext _ xtb z) as a2; simpl in *.
  eapply type_extensionality_nuprl;[eauto|].
  introv; split; intro h.

  { exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto. }

  exrepnd.
  pose proof (a1 _ ext1 _ ext2 extz) as w.
  eapply (nuprl_monotone _ lib'0) in w; try exact z0; exrepnd.
  apply nuprl_refl in w1.
  apply nuprl_refl in a2.
  eapply nuprl_uniquely_valued in w1; try exact a2; apply w1; clear w1; apply w0; auto.
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
    -> in_open_bar lib G
    -> in_open_bar lib F.
Proof.
  introv h q.
  eapply in_open_bar_pres; eauto.
Qed.

Lemma all_in_ex_bar_modus_ponens2 {o} :
  forall (lib : @library o) (G H F : library -> Prop),
    in_ext lib (fun lib => G lib -> H lib -> F lib)
    -> in_open_bar lib G
    -> in_open_bar lib H
    -> in_open_bar lib F.
Proof.
  introv h q w.
  eapply in_open_bar_comb; try exact w; clear w.
  eapply in_open_bar_pres; try exact q; clear q; auto.
Qed.

Hint Resolve inhabited_type_if_equality : slow.

Lemma all_in_ex_bar_type_implies_type {o} :
  forall lib (A : @CTerm o),
    in_open_bar lib (fun lib' => type lib' A)
    -> type lib A.
Proof.
  introv a.
  apply all_in_ex_bar_tequality_implies_tequality; auto.
Qed.

Definition inhabited_type_bar {o} lib (A : @CTerm o) :=
  in_open_bar lib (fun lib => inhabited_type lib A).

Lemma collapse_all_in_ex_bar {o} :
  forall (lib : @library o) F,
    in_open_bar lib F <=> in_open_bar lib (fun lib => in_open_bar lib F).
Proof.
  introv; split; intro h; exrepnd.
  { eapply in_open_bar_implies_in_open_bar_ext in h.
    apply in_open_bar_ext_twice in h; simpl in *.
    eapply in_open_bar_comb2; eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv xta h.
    eapply in_open_bar_comb2; eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv xtb h; auto. }
  { apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_comb2; eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv xta h; auto. }
Qed.

Lemma all_in_ex_bar_equality_implies_equality {o} :
  forall lib (a b A : @CTerm o),
    in_open_bar lib (fun lib => equality lib a b A)
    -> equality lib a b A.
Proof.
  introv h.
  apply in_open_bar_implies_in_open_bar_ext in h.
  apply in_open_bar_ext_choice in h; exrepnd.
  apply in_open_bar_eqa_choice_non_dep in h0; exrepnd.

  exists (per_bar_eq lib (lib_fun_non_dep_eqa Feqa)).
  dands; auto.

  {
    eapply local_ts_nuprl;[apply eq_term_equals_refl|].
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv.

    pose proof (h1 _ ext _ xtb z) as h2; simpl in *; repnd.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro h.

    { exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (h1 _ ext1 _ ext2 extz) as w; repnd.
    apply nuprl_refl in w0; apply nuprl_refl in h0.
    eapply (nuprl_monotone _ lib'0) in w0; try exact z0; exrepnd.
    eapply nuprl_uniquely_valued in w0; try exact h0.
    apply w0; apply w1; auto.
  }

  {
    introv ext.
    assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
    exists (Flib _ ext) xta.
    introv xtb; introv.
    pose proof (h1 _ ext _ xtb z) as h1; repnd; simpl in *.
    exists lib' ext lib'0 xtb z (lib_extends_refl lib'0); auto.
  }
Qed.
Hint Resolve all_in_ex_bar_equality_implies_equality : slow.

Definition computes_to_valc_ex_bar {o} lib (a b : @CTerm o) :=
  in_open_bar lib (fun lib => a ===>(lib) b).
Notation "t1 ===b>( lib ) t2" := (computes_to_valc_ex_bar lib t1 t2) (at level 0).

Lemma computes_to_valc_implies_computes_to_valc_ex_bar {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> a ===b>(lib) b.
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_implies_computes_to_valc_ex_bar : slow.

Lemma in_ext_implies_all_in_ex_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F -> in_open_bar lib F.
Proof.
  introv h; apply in_ext_implies_in_open_bar; auto.
Qed.

Lemma non_dep_all_in_ex_bar_implies {o} :
  forall (lib : @library o) P,
    in_open_bar lib (fun _ => P) -> P.
Proof.
  introv h.
  apply (in_open_bar_const lib); auto.
Qed.

Lemma lib_extends_preserves_all_in_ex_bar {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) F,
    in_open_bar lib F
    -> in_open_bar lib' F.
Proof.
  introv x h; eauto 3 with slow.
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
    in_open_bar lib (fun lib => inhabited_type lib A)
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
  in_open_bar lib (fun lib => ccequivc_ext lib t1 t2).

Definition ccequivc_bar {o} lib (a b : @CTerm o) :=
  in_open_bar lib (fun lib => ccequivc lib a b).

Lemma implies_in_ext_in_ext {o} :
  forall (lib : @library o) F,
    in_ext lib F
    -> in_ext lib (fun lib' => in_ext lib' F).
Proof.
  introv h xta xtb; apply h; eauto 3 with slow.
Qed.
Hint Resolve implies_in_ext_in_ext : slow.

Lemma implies_in_open_bar_in_ext {o} :
  forall (lib : @library o) F,
    in_open_bar lib F
    -> in_open_bar lib (fun lib' => in_ext lib' F).
Proof.
  introv h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' xt; eauto 3 with slow.
Qed.
Hint Resolve implies_in_open_bar_in_ext : slow.

Lemma ccequivc_ext_bar_iff_ccequivc_bar {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext_bar lib a b <=> ccequivc_bar lib a b.
Proof.
  introv; split; introv e.

  - eapply all_in_ex_bar_modus_ponens1;try exact e; clear e; introv x e; exrepnd; eauto 3 with slow.

  - unfold ccequivc_bar, ccequivc_ext_bar in *; exrepnd.
    apply implies_in_open_bar_in_ext; auto.
Qed.

Lemma all_in_ex_bar_member_implies_member {o} :
  forall lib (a A : @CTerm o),
    in_open_bar lib (fun lib => member lib a A)
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
    in_open_bar lib (fun lib => tequality lib A B # equality lib a b T)
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
    -> in_open_bar lib G
    -> in_open_bar lib H
    -> in_open_bar lib K
    -> in_open_bar lib F.
Proof.
  introv h q z w.
  eapply in_open_bar_comb; try exact q; clear q.
  eapply in_open_bar_comb; try exact z; clear z.
  eapply in_open_bar_pres; try exact w; clear w; introv ext w z q; eauto.
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
    -> in_open_bar lib (fun lib => equality lib a b A).
Proof.
  introv equ.
  apply in_ext_implies_all_in_ex_bar; introv x; eauto 3 with slow.
Qed.

Lemma all_in_ex_bar_modus_ponens4 {o} :
  forall (lib : @library o) (G H K L F : library -> Prop),
    in_ext lib (fun lib => G lib -> H lib -> K lib -> L lib -> F lib)
    -> in_open_bar lib G
    -> in_open_bar lib H
    -> in_open_bar lib K
    -> in_open_bar lib L
    -> in_open_bar lib F.
Proof.
  introv h q z w x.
  eapply in_open_bar_comb; try exact q; clear q.
  eapply in_open_bar_comb; try exact z; clear z.
  eapply in_open_bar_comb; try exact w; clear w.
  eapply in_open_bar_pres; try exact x; clear x; introv ext x w z q; eauto.
Qed.

Lemma implies_all_in_ex_bar_in_ext {o} :
  forall (lib : @library o) F,
    in_open_bar lib F -> in_open_bar lib (fun lib' => in_ext lib' F).
Proof.
  apply implies_in_open_bar_in_ext.
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
