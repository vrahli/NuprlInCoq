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

Require Export alphaeq3.
Require Export substitution3.

Lemma alpha_eq_bterm_bterm_disjoint {o} :
  forall vs1 vs2 (t : @NTerm o),
    disjoint vs1 (free_vars t)
    -> disjoint vs2 (free_vars t)
    -> length vs1 = length vs2
    -> alpha_eq_bterm (bterm vs1 t) (bterm vs2 t).
Proof.
  introv d1 d2 len.
  pose proof (fresh_vars (length vs1)
                         (vs1 ++ vs2
                              ++ free_vars t
                              ++ bound_vars t)) as fvs; exrepnd.
  allrw disjoint_app_r; repnd.
  apply (al_bterm_aux lvn); auto.
  { allrw disjoint_app_r; tcsp. }
  rw @lsubst_aux_trivial_cl_term;[|rw @dom_sub_var_ren;eauto with slow].
  rw @lsubst_aux_trivial_cl_term;[|rw @dom_sub_var_ren;eauto with slow; try lia].
  eauto with slow.
Qed.
