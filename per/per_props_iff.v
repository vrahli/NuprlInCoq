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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_function.
Require Export per_props_product.


Lemma equality_in_iff {p} :
  forall lib (p1 p2 A B : @CTerm p),
    equality lib p1 p2 (mkc_iff A B)
    <=>
    (type lib A
     # type lib B
     # {f1, f2, g1, g2 : CTerm
        , p1 ===>(lib) (mkc_pair f1 g1)
        # p2 ===>(lib) (mkc_pair f2 g2)
        # (forall a1 a2,
             equality lib a1 a2 A
             -> equality lib (mkc_apply f1 a1) (mkc_apply f2 a2) B)
        # (forall b1 b2,
             equality lib b1 b2 B
             -> equality lib (mkc_apply g1 b1) (mkc_apply g2 b2) A)}).
Proof.
  introv.
  rw @equality_in_prod; split; intro e; exrepnd;
  allrw @type_mkc_fun; repnd; dands; auto;
  allrw @equality_in_fun; repnd; auto.

  exists a1 a2 b1 b2; dands; auto.

  exists f1 f2 g1 g2; dands; auto; rw @equality_in_fun; dands; auto.
Qed.

Lemma tequality_mkc_iff {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_iff A1 B1) (mkc_iff A2 B2)
    <=> (tequality lib A1 A2
         # (inhabited_type lib A1 -> tequality lib B1 B2)
         # (inhabited_type lib (mkc_fun A1 B1) -> tequality lib B1 B2)).
Proof.
  introv.
  allrw @tequality_mkc_prod.
  allrw @tequality_mkc_fun.
  split; intro k; repnd; dands; auto.
  intro i; autodimp k hyp; repnd; auto.
Qed.
