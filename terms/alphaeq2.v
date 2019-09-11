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

Require Export alphaeq.


Lemma sub_free_vars_csub2sub {o} :
  forall (sub : @CSub o),
    sub_free_vars (csub2sub sub) = [].
Proof.
  induction sub; simpl; auto.
  destruct a; allsimpl; allrw.
  rw @free_vars_cterm; auto.
Qed.

Lemma alpha_eq_mk_vbot {o} :
  forall v1 v2, @alpha_eq o (mk_vbot v1) (mk_vbot v2).
Proof.
  introv.
  unfold mk_vbot, mk_fix, mk_lam, mk_var.

  prove_alpha_eq4.
  introv i; destruct n; cpx; clear i.
  apply alphaeqbt_nilv2; auto.

  prove_alpha_eq4.
  introv i; destruct n; cpx; clear i.
  pose proof (ex_fresh_var [v1,v2]) as fv; exrepnd.
  apply (al_bterm _ _ [v]); simpl; auto.

  - unfold all_vars; simpl; rw disjoint_singleton_l; auto.

  - unfold lsubst; simpl; boolvar; auto.
Qed.
Hint Resolve alpha_eq_mk_vbot : slow.
