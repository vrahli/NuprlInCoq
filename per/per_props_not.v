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


Require Export per_props_cequiv.
Require Export per_props_function.


Lemma tequality_false {p} :
  forall lib, @tequality p lib mkc_false mkc_false.
Proof.
  introv.
  rw @mkc_false_eq.
  rw @tequality_mkc_approx; split; intro k; spcast;
  apply not_axiom_approxc_bot in k; sp.
Qed.
Hint Immediate tequality_false.

Lemma tequality_void {p} :
  forall lib, @tequality p lib mkc_void mkc_void.
Proof.
  introv; rw @mkc_void_eq_mkc_false; sp.
Qed.
Hint Immediate tequality_void.

Lemma type_void {p} :
  forall lib, @type p lib mkc_void.
Proof.
  introv; apply fold_type; apply tequality_void.
Qed.
Hint Resolve type_void : slow.

Lemma equality_in_false {p} :
  forall lib (t1 t2 : @CTerm p), equality lib t1 t2 mkc_false <=> False.
Proof.
  introv; split; intro e; sp.
  rw @mkc_false_eq in e.
  rw <- @equality_in_approx in e; repnd; spcast.
  allapply @not_axiom_approxc_bot; sp.
Qed.

Lemma equality_in_void {p} :
  forall lib (t1 t2 : @CTerm p), equality lib t1 t2 mkc_void <=> False.
Proof.
  introv.
  rw @mkc_void_eq_mkc_false; sp.
  apply equality_in_false.
Qed.

Lemma equality_in_not {p} :
  forall lib (t1 t2 A : @CTerm p),
    equality lib t1 t2 (mkc_not A)
    <=>
    (type lib A # !inhabited_type lib A).
Proof.
  introv.
  rw @equality_in_fun; split; intro e; repnd; dands; auto; try (complete sp).

  intro inh.
  destruct inh.
  discover.
  allapply @equality_in_void; sp.

  introv ea.
  apply equality_in_void.
  apply e.
  exists a.
  allapply @equality_refl; auto.
Qed.

Hint Resolve equality_refl : slow.

Lemma tequality_not {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_not A1) (mkc_not A2)
    <=>
    (
      type lib A1
      # type lib A2
      # (!inhabited_type lib A1 <=> !inhabited_type lib A2)
    ).
(* tequality lib A1 A2.*)
Proof.
  intros.
  rw @tequality_fun.
  split; intro h; repnd; dands; auto; eauto 2 with slow.

  - split; introv w q; unfold inhabited_type in *; exrepnd.

    + pose proof (h t t) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp.
      { apply equality_in_fun; dands; auto.
        introv ea.
        assert False; tcsp.
        destruct w; exists a; eauto 2 with slow. }
      { apply equality_in_fun in q; repnd.
        pose proof (q t t) as q; autodimp q hyp.
        apply equality_in_void in q; auto. }

    + pose proof (h t t) as q.
      destruct q as [q' q]; clear q'.
      autodimp q hyp.
      { apply equality_in_fun; dands; auto.
        introv ea.
        assert False; tcsp.
        destruct w; exists a; eauto 2 with slow. }
      { apply equality_in_fun in q; repnd.
        pose proof (q t t) as q; autodimp q hyp.
        apply equality_in_void in q; auto. }

  - introv.
    repeat (rw @equality_in_fun); split; intro q;
      repnd; dands; auto; eauto 2 with slow.

    + introv ea.
      assert False; tcsp.
      destruct h as [h h']; clear h'.
      autodimp h hyp.
      { intro z; unfold inhabited_type in z; exrepnd.
        pose proof (q t t) as w; autodimp w hyp.
        apply equality_in_void in w; auto. }
      { destruct h; exists a0; eauto 2 with slow. }

    + introv ea.
      assert False; tcsp.
      destruct h as [h' h]; clear h'.
      autodimp h hyp.
      { intro z; unfold inhabited_type in z; exrepnd.
        pose proof (q t t) as w; autodimp w hyp.
        apply equality_in_void in w; auto. }
      { destruct h; exists a0; eauto 2 with slow. }
Qed.
