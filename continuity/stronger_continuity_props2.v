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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export list.
Require Export per_props.
Require Export continuity_defs.
Require Export stronger_continuity_defs0.
Require Export cequiv_props.
Require Export terms_pi.

Lemma fresh_in_product {o} :
  forall lib v (t1 t2 : @CVTerm o [v]) A x B,
    equality lib (mkc_fresh v (mkcv_pi1 [v] t1)) (mkc_fresh v (mkcv_pi2 [v] t2)) A
    -> equality
         lib
         (mkc_fresh v (mkcv_pi2 [v] t1))
         (mkc_fresh v (mkcv_pi2 [v] t2))
         (substc (mkc_fresh v (mkcv_pi1 [v] t1)) x B)
    -> (forall a1 a2,
          equality lib a1 a2 A
          -> tequality lib (substc a1 x B) (substc a2 x B))
    -> equality lib (mkc_fresh v t1) (mkc_fresh v t2) (mkc_product A x B).
Proof.
  introv ea eb tb.
  apply equality_in_product.
  dands; auto.
  { eapply inhabited_implies_tequality; eauto. }

  Check computes_to_pair_eta_c.

Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
