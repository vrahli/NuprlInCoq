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


Require Export per_props_isect.


Lemma tequality_mkc_ufun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_ufun A1 B1) (mkc_ufun A2 B2)
    <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_ufun.
  rw @tequality_isect.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @csubst_mk_cv; auto.

  introv e.
  allrw @csubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

Lemma equality_in_ufun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_ufun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (inhabited_type lib A -> equality lib f g B)).
Proof.
  introv.
  rw <- @fold_mkc_ufun.
  rw @equality_in_isect.
  split; intro k; repnd; dands; auto.

  - introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.

  - introv e.
    unfold inhabited_type in e; exrepnd.
    unfold member in e0.
    apply k in e0.
    repeat (rw @csubst_mk_cv in e0); sp.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp.
    exists a; apply equality_refl in e; auto.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    apply k.
    exists a; apply equality_refl in e; auto.
Qed.
