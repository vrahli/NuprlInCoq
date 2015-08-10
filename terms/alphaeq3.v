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


Require Export alphaeq.


Lemma al_bterm_aux {o} :
  forall (lv lv1 lv2 : list NVar) (nt1 nt2 : @NTerm o),
    disjoint lv (all_vars nt1 ++ all_vars nt2)
    -> length lv1 = length lv2
    -> length lv1 = length lv
    -> no_repeats lv
    -> alpha_eq (lsubst_aux nt1 (var_ren lv1 lv)) (lsubst_aux nt2 (var_ren lv2 lv))
    -> alpha_eq_bterm (bterm lv1 nt1) (bterm lv2 nt2).
Proof.
  introv disj len1 len2 norep aeq.
  apply (al_bterm _ _ lv); auto.
  allrw @lsubst_lsubst_aux; auto;
  rw @flat_map_free_var_vars_range;
  allrw disjoint_app_r; repnd; eauto 3 with slow; try omega.
Qed.
