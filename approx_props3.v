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

Require Export approx_props1.

Lemma respects_alpha_2 {o} :
  forall (r1 r2 : bin_rel (@NTerm o)),
    respects_alpha r1
    -> respects_alpha r2
    -> respects_alpha (r1 \2/ r2).
Proof.
  introv resp1 resp2.
  allunfold @respects2; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve respects_alpha_2 : slow.

Lemma respects_alpha_approx_aux {o} :
  forall lib (r : bin_rel (@NTerm o)),
    respects_alpha r
    -> respects_alpha (approx_aux lib r).
Proof.
  introv resp.
  allunfold @respects2; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve respects_alpha_approx_aux : slow.

Lemma respects_alpha_bot2 {o} :
  respects_alpha (@bot2 o).
Proof.
  allunfold @respects2; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve respects_alpha_bot2 : slow.
