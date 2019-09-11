(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export substitution.


Lemma sub_filter_eqvars {o} :
  forall vs1 vs2 (sub : @Sub o),
    eqvars vs1 vs2
    -> sub_filter sub vs1 = sub_filter sub vs2.
Proof.
  induction sub; introv eqv; allsimpl; auto.
  destruct a; boolvar; simpl; tcsp.
  - rw eqvars_prop in eqv; apply eqv in Heqb; sp.
  - rw eqvars_prop in eqv; apply eqv in Heqb0; sp.
  - apply IHsub in eqv; rw eqv; auto.
Qed.

Lemma lsubst_aux_cons_sub_filter {o} :
  forall (t : @NTerm o) v u sub,
    lsubst_aux t ((v,u) :: sub_filter sub [v])
    = lsubst_aux t ((v,u) :: sub).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; allsimpl; auto.

  - Case "vterm".
    boolvar; auto.
    rw @sub_find_sub_filter_eta; simpl; auto; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i; destruct x; simpl.
    f_equal.
    boolvar; auto.

    + rw <- @sub_filter_app_r; allsimpl.
      rw (sub_filter_eqvars (v :: l) l sub); auto.
      rw eqvars_prop; simpl; introv; split; intro k; tcsp.
      dorn k; subst; tcsp.

    + rw @sub_filter_swap.
      eapply ind; eauto.
Qed.

Lemma lsubst_cons_sub_filter {o} :
  forall (t : @NTerm o) v u sub,
    disjoint (bound_vars t) (free_vars u)
    -> disjoint (bound_vars t) (flat_map free_vars (range sub))
    -> lsubst t ((v,u) :: sub_filter sub [v])
       = lsubst t ((v,u) :: sub).
Proof.
  introv d1 d2.
  change_to_lsubst_aux4; allsimpl.
  - apply lsubst_aux_cons_sub_filter.
  - allrw disjoint_app_r; repnd; dands; auto.
  - allrw disjoint_app_r; dands; auto.
    allrw disjoint_flat_map_r; introv i.
    apply d2.
    apply in_range in i; exrepnd.
    apply in_range_iff.
    apply in_sub_filter in i0; repnd.
    eexists; eauto.
Qed.

Hint Rewrite @free_vars_cterm : slow.

Lemma csubst_cons_trim {p} :
  forall t x a s,
    @csubst p t ((x, a) :: s)
    = csubst t ((x, a) :: csub_filter s [x]).
Proof.
  unfold csubst; sp; simpl.
  rewrite <- sub_filter_csub2sub.
  rw @lsubst_cons_sub_filter; simpl; auto;
  autorewrite with slow in *; auto.
  rw @prog_sub_flatmap_range; eauto 3 with slow.
Qed.
