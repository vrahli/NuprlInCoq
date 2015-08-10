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


Require Export per_props_equality.


Lemma tequality_mkc_equality_sp_eq {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    equality lib a1 a2 A
    -> (tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
        <=> (tequality lib A B # equality lib a1 b1 A # equality lib a2 b2 A)).
Proof.
  introv eqa.
  split; intro h; repnd; dands; auto.
  - rw @tequality_mkc_equality_sp in h; sp.
  - rw @tequality_mkc_equality_sp in h; repnd.
    repndors; spcast; eauto 3 with nequality.
  - rw @tequality_mkc_equality_sp in h; repnd.
    repndors; spcast; eauto 3 with nequality.
    + eapply equality_respects_cequivc_right;[exact h|].
      apply equality_sym in eqa; apply equality_refl in eqa; auto.
    + eapply equality_respects_cequivc_right;[exact h|].
      apply equality_sym in eqa; apply equality_refl in eqa; auto.
  - apply tequality_mkc_equality_sp; dands; auto.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
