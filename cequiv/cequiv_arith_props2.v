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


Lemma implies_approx_arithop {o} :
  forall lib op (a1 b1 a2 b2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib (mk_arithop op a1 b1) (mk_arithop op a2 b2).
Proof.
  introv apa apb.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  repnd.
  unfold mk_arithop.
  repeat prove_approx; sp.
Qed.

Lemma implies_cequiv_arithop {o} :
  forall lib op (a1 b1 a2 b2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_arithop op a1 b1) (mk_arithop op a2 b2).
Proof.
  introv apa apb.
  destruct apa, apb.
  split; apply implies_approx_arithop; auto.
Qed.

Lemma implies_cequivc_mkc_arithop {o} :
  forall lib op (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_arithop op a1 b1) (mkc_arithop op a2 b2).
Proof.
  introv ceq1 ceq2; destruct_cterms; allunfold @cequivc; allsimpl.
  apply implies_cequiv_arithop; auto.
Qed.

Lemma cequivc_arithop_integer_exception {o} :
  forall lib op k (a b : @CTerm o),
    cequivc
      lib
      (mkc_arithop op (mkc_integer k) (mkc_exception a b))
      (mkc_exception a b).
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; auto.
Qed.
