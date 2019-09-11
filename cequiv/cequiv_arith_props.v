 (*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export cequiv.
Require Export arith_props.


Lemma reduces_to_add_integer {o} :
  forall lib (k1 k2 : Z),
    @reduces_to o lib (mk_add (mk_integer k1) (mk_integer k2)) (mk_integer (k1 + k2)).
Proof.
  introv.
  apply reduces_to_if_step.
  csunf; simpl; dcwf h; simpl; auto.
Qed.

Lemma cequiv_mk_add_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_add (mk_integer k1) (mk_integer k2)) (mk_integer (k1 + k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_add_implies; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_add_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_add (mkc_integer k1) (mkc_integer k2)) (mkc_integer (k1 + k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_add_integer.
Qed.

Lemma implies_approx_add {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_add f a) (mk_add g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  unfold mk_add.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_mkc_add {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_add a b) (mkc_add c d).
Proof.
  introv c1 c2; destruct_cterms; allunfold @cequivc; allsimpl.
  destruct c1, c2.
  split; apply implies_approx_add; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
