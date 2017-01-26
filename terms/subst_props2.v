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

Require Export substitution3.

Hint Resolve isprog_void.

Lemma covered_implies_remove_nvars {o} :
  forall (t : @NTerm o) vs1 vs2,
    subvars vs1 vs2
    -> covered t vs1
    -> remove_nvars vs2 (free_vars t) = [].
Proof.
  introv sv cov.
  unfold covered in cov.
  remember (free_vars t) as vs; clear Heqvs.
  rw subvars_prop in cov.
  rw subvars_prop in sv.
  apply null_iff_nil.
  apply null_remove_nvars.
  introv i.
  apply cov in i.
  apply sv in i; auto.
Qed.

Lemma closed_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> covered t (dom_sub sub)
    -> closed (lsubst_aux t sub).
Proof.
  introv cl cov.
  pose proof (free_vars_lsubst_aux_cl t sub) as fv.
  autodimp fv hyp.
  unfold closed; rw fv; simpl.
  apply (covered_implies_remove_nvars _ (dom_sub sub)); auto.
Qed.

Lemma free_vars_lsubst_aux_subset {o} :
  forall (t : @NTerm o) (sub : Sub),
    subset (free_vars (lsubst_aux t sub))
           (remove_nvars (dom_sub sub) (free_vars t) ++ sub_free_vars sub).
Proof.
  introv.
  pose proof (free_vars_lsubst_aux_subvars t sub) as h.
  rw subvars_eq in h; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
