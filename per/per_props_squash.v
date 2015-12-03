(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props.


Lemma implies_tequality_equality_mkc_squash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> inhabited_type lib t1
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv teq inh.
  rw @equality_in_mkc_squash.
  rw @tequality_mkc_squash.
  dands; auto; spcast;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
