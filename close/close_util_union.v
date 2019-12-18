(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export type_sys.
Require Export per_ceq_bar.
Require Export close_util_bar.



Definition per_union_eq_bar_lib_per
           {o} {inh}
           {lib : @library o}
           (eqa eqb : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) =>
            per_union_eq_bar inh lib' (raise_lib_per inh eqa x) (raise_lib_per inh eqb x)).

  repeat introv.
  unfold per_union_eq_bar, raise_lib_per, raise_ext_per; simpl.
  split; intro h; exrepnd;
      eapply in_open_bar_ext_comb; try exact h; clear h;
        apply in_ext_ext_implies_in_open_bar_ext; introv h.

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
      [left|right]; eexists; eexists; dands; eauto.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
      [left|right]; eexists; eexists; dands; eauto.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }
Defined.

Lemma implies_eq_term_equals_per_union_eq {o} :
  forall inh lib (eqa eqb eqc eqd : per(o)),
    (eqa <=2=> eqb)
    -> (eqc <=2=> eqd)
    -> (per_union_eq inh lib eqa eqc) <=2=> (per_union_eq inh lib eqb eqd).
Proof.
  introv eqas eqbs; introv.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R; introv; split; intro h; introv;
    repndors; exrepnd;[left|right|left|right]; eexists; eexists; dands; eauto;
      try (complete (apply eqas; auto));
      try (complete (apply eqbs; auto)).
Qed.

Lemma per_bar_eq_per_union_eq_bar_lib_per {o} :
  forall inh (lib : @library o) (eqa eqb : lib-per(inh,lib,o)),
    (per_bar_eq inh lib (per_union_eq_bar_lib_per eqa eqb))
    <=2=> (per_union_eq_bar inh lib eqa eqb).
Proof.
  introv; simpl; unfold per_bar_eq; split; intro h; eauto 3 with slow.

  - unfold per_union_eq_bar.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_union_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_union_eq; try exact h;
      try apply (lib_per_cond _ _ eqa);
      try apply (lib_per_cond _ _ eqb).

  - unfold per_union_eq_bar in *.
    apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_union_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_union_eq; try exact h;
      try apply (lib_per_cond _ _ eqa);
      try apply (lib_per_cond _ _ eqb).
Qed.
