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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Abhishek Anand

*)


Require Export per_props_util.
Require Export per_props_compute.


Definition chaltsc_bar {o} lib (t : @CTerm o) :=
  all_in_ex_bar lib (fun lib => chaltsc lib t).

Definition comp_val_bar {o} lib (t : @CTerm o) :=
  all_in_ex_bar lib (fun lib => exists v, ccomputes_to_valc_ext lib t v).

Hint Resolve computes_to_valc_implies_hasvaluec : slow.

Lemma ccomputes_to_valc_ext_implies_hasvaluec {o} :
  forall lib lib' (a b : @CTerm o),
    lib_extends lib' lib
    -> (a ===>(lib) b)
    -> hasvaluec lib' a.
Proof.
  introv ext comp.
  apply hasvaluec_stable.
  pose proof (comp _ ext) as comp; simpl in *; exrepnd; spcast; eauto 3 with slow.
Qed.
Hint Resolve ccomputes_to_valc_ext_implies_hasvaluec : slow.

Lemma computes_to_valc_implies_chaltsc_bar_left {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> chaltsc_bar lib a.
Proof.
  introv comp.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar; introv x.
  spcast; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_implies_chaltsc_bar_left : slow.

Lemma ccomputes_to_valc_ext_implies_comp_val_bar {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> comp_val_bar lib a.
Proof.
  introv comp.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar; introv x.
  exists b; eauto 3 with slow.
Qed.
Hint Resolve ccomputes_to_valc_ext_implies_comp_val_bar : slow.


Lemma types_converge {o} :
  forall lib (t : @CTerm o), type lib t -> chaltsc_bar lib t.
Proof.
  introv n.
  unfold type, tequality, nuprl in n; exrepnd.
  remember univ as u.
  revert Hequ.
  close_cases (induction n0 using @close_ind') Case; intro Hequ; subst;
    allunfold_per; uncast; eauto 3 with slow.

  {
    rename_hyp_with @univ h.
    unfold univ, per_bar in h; exrepnd.
    exists bar.
    introv br ext.
    assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
    pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold univ_ex in *; exrepnd.
    rw @univi_exists_iff in h2; exrepnd.
    spcast; eauto 3 with slow.
  }

  {
    apply collapse_all_in_ex_bar.
    exists bar.
    introv br ext.
    assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
    fold (chaltsc_bar lib'0 T').
    apply (reca _ br); eauto 3 with slow.
  }
Qed.

Lemma types_converge2 {o} :
  forall lib (t : @CTerm o), type lib t -> comp_val_bar lib t.
Proof.
  introv n.
  unfold type, tequality, nuprl in n; exrepnd.
  remember univ as u.
  revert Hequ.
  close_cases (induction n0 using @close_ind') Case; intro Hequ; subst;
    allunfold_per; uncast; eauto 3 with slow.

  {
    rename_hyp_with @univ h.
    unfold univ, per_bar in h; exrepnd.
    exists bar.
    introv br ext.
    assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
    pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold univ_ex in *; exrepnd.
    rw @univi_exists_iff in h2; exrepnd.
    spcast; eauto 3 with slow.
  }

  {
    apply collapse_all_in_ex_bar.
    exists bar.
    introv br ext.
    assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
    fold (chaltsc_bar lib'0 T').
    apply (reca _ br); eauto 3 with slow.
  }
Qed.
