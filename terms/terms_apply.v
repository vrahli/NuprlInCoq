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


Require Export terms2.

Fixpoint apply_list {o} (t : @NTerm o) (ts : list (@NTerm o)) : @NTerm o :=
  match ts with
    | [] => t
    | u :: us => apply_list (mk_apply t u) us
  end.

Lemma wf_apply_list {o} :
  forall (ts : list (@NTerm o)) f,
    wf_term (apply_list f ts)
    <=> (wf_term f # (forall t, LIn t ts -> wf_term t)).
Proof.
  induction ts; simpl; split; intro k; allsimpl; tcsp.
  - apply IHts in k; repnd.
    rw <- @wf_apply_iff in k0; repnd; dands; auto.
    introv i; dorn i; subst; sp.
  - repnd.
    apply IHts; dands; auto.
    apply wf_apply_iff; dands; auto.
Qed.

Lemma free_vars_apply_list {o} :
  forall (ts : list (@NTerm o)) f,
    free_vars (apply_list f ts) = free_vars f ++ flat_map free_vars ts.
Proof.
  induction ts; simpl; introv.
  - rw app_nil_r; auto.
  - rw IHts; simpl.
    repeat (rw remove_nvars_nil_l).
    rw app_nil_r.
    rw app_assoc; auto.
Qed.
