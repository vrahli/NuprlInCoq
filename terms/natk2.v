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


Require Export natk.


Lemma cover_vars_upto_csub_filter_single_cons_disj {o} :
  forall (t : @NTerm o) s v vs,
    !LIn v (free_vars t)
    -> (cover_vars_upto t (csub_filter s [v]) (v :: vs)
        <=> cover_vars_upto t s vs).
Proof.
  introv niv.
  unfold cover_vars_upto; simpl.
  rw @dom_csub_csub_filter.
  allrw subvars_eq.
  split; intros ss i x; applydup ss in x; allsimpl;
  allrw in_app_iff; allrw in_remove_nvars; allsimpl;
  allrw not_over_or; repndors; subst; tcsp.
  right; right.
  dands; tcsp.
  intro xx; subst; tcsp.
Qed.

Lemma cover_vars_upto_int {o} :
  forall (s : @CSub o) vs, cover_vars_upto mk_int s vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl; auto.
Qed.
Hint Resolve cover_vars_upto_int : slow.

Lemma cover_vars_upto_natk {o} :
  forall (t : @NTerm o) s vs,
    cover_vars_upto (mk_natk t) s vs
    <=> cover_vars_upto t s vs.
Proof.
  introv.
  unfold mk_natk, mk_natk_aux.
  rw @cover_vars_upto_set.
  rw @cover_vars_upto_prod.
  rw @cover_vars_upto_le.
  rw @cover_vars_upto_less_than.
  rw @cover_vars_upto_var.

  pose proof (newvar_prop t) as p.
  remember (newvar t) as v; clear Heqv.

  rw (cover_vars_upto_csub_filter_single_cons_disj t s v vs p).
  simpl.

  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Definition mk_nat2T {o} T : @NTerm o := mk_fun mk_tnat T.
Definition mk_natk2T {o} (t : @NTerm o) T : @NTerm o := mk_fun (mk_natk t) T.

Definition natk2T {o} (t T : @CTerm o) := mkc_fun (mkc_natk t) T.
Definition nat2T {o} (T : @CTerm o) := mkc_fun mkc_tnat T.

Lemma wf_term_mk_natk2T {o} :
  forall (t T : @NTerm o),
    wf_term (mk_natk2T t T) <=> (wf_term t # wf_term T).
Proof.
  introv.
  rw @wf_fun_iff.
  rw @wf_term_mk_natk; sp.
Qed.

Hint Resolve wf_mk_nat : slow.

Lemma wf_term_mk_zero {o} :
  @wf_term o mk_zero.
Proof.
  introv.
  unfold mk_zero.
  eauto 3 with slow.
Qed.
Hint Resolve wf_term_mk_zero : slow.

Lemma wf_term_mk_tnat {o} :
  @wf_term o mk_tnat.
Proof.
  introv.
  unfold mk_tnat.
  apply wf_set; auto.
  - apply wf_int.
  - apply wf_le; dands; eauto 3 with slow.
Qed.
Hint Resolve wf_term_mk_tnat : slow.

Lemma wf_term_mk_nat2T {o} :
  forall (T : @NTerm o),
    wf_term (mk_nat2T T) <=> wf_term T.
Proof.
  introv.
  rw @wf_fun_iff.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
