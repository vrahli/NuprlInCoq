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


Require Export computation2.


Lemma cl_sub_csub2sub {o} :
  forall (s : @CSub o), cl_sub (csub2sub s).
Proof.
  induction s; simpl; eauto with slow.
Qed.
Hint Resolve cl_sub_csub2sub : slow.

Lemma cover_vars_iff_closed_lsubst_aux {o} :
  forall (t : @NTerm o) s,
    cover_vars t s <=> closed (lsubst_aux t (csub2sub s)).
Proof.
  introv; rw @cover_vars_iff_closed_lsubstc.
  unfold csubst.
  pose proof (unfold_lsubst (csub2sub s) t) as h; exrepnd.
  rw h0.
  unfold closed.
  repeat (rw @free_vars_lsubst_aux_cl; eauto with slow).
  apply alphaeq_preserves_free_vars in h1.
  rw h1; tcsp.
Qed.
