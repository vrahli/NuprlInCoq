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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export local.


(*Lemma local_equality_of_int_bar {o} :
  forall {lib} (bar : @BarLib o lib) t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => equality_of_int_bar lib' t1 t2)
    -> equality_of_int_bar lib t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.
Hint Resolve local_equality_of_int_bar : slow.*)

Lemma local_per_int {o} :
  forall inh (lib : @library o) ts T T' eq eqa,
    (eq <=2=> (per_bar_eq inh lib eqa))
    -> in_open_bar_ext inh lib (fun lib' x => per_int inh ts lib' T T' (eqa lib' x))
    -> per_bar inh (per_int inh ts) lib T T' eq.
Proof.
  introv eqiff alla.
  unfold per_int in *.
  exists eqa; dands; auto.
Qed.

Lemma per_int_implies_per_int_bar {o} :
  forall inh ts lib (T T' : @CTerm o) eq,
    per_int inh ts lib T T' eq
    -> per_int_bar inh ts lib T T' eq.
Proof.
  introv per.
  unfold per_int in per; repnd.
  unfold per_int_bar.
  dands; auto;
    apply in_ext_implies_in_open_bar; introv ext; eauto 3 with slow.
Qed.
Hint Resolve per_int_implies_per_int_bar : slow.

Lemma per_bar_eq_equality_of_int_bar_implies {o} :
  forall inh (lib : @library o) t1 t2,
    per_bar_eq inh lib (equality_of_int_bar_lib_per inh lib) t1 t2
    -> equality_of_int_bar inh lib t1 t2.
Proof.
  introv alla.
  unfold per_bar_eq in alla.
  unfold equality_of_int_bar.
  apply in_open_bar_ext_in_open_bar.
  eapply in_open_bar_ext_pres; eauto; clear alla; introv h; simpl in *.
  unfold equality_of_int_bar in h; auto.
Qed.
Hint Resolve per_bar_eq_equality_of_int_bar_implies : slow.

Lemma all_in_bar_ext_equal_equality_of_int_bar_implies_per_bar_eq_implies_equality_of_int_bar {o} :
  forall inh (lib : @library o) (eqa : lib-per(inh,lib,o)),
    in_open_bar_ext inh lib (fun lib' x => (eqa lib' x) <=2=> (equality_of_int_bar inh lib'))
    -> (per_bar_eq inh lib eqa) <=2=> (equality_of_int_bar inh lib).
Proof.
  introv alla; introv; unfold per_bar_eq, equality_of_int_bar; split; introv h.

  - pose proof (in_open_bar_ext_eq_term_equals_preserves_per_bar_eq
                  _ _ eqa (equality_of_int_bar_lib_per inh lib) t1 t2 alla h) as q.
    eauto 3 with slow.
    apply per_bar_eq_equality_of_int_bar_implies; auto.

  - eapply in_open_bar_ext_pres;[|exact alla]; clear alla; introv alla; apply alla; clear alla.
    unfold equality_of_int_bar; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_equal_equality_of_int_bar_implies_per_bar_eq_implies_equality_of_int_bar : slow.

Lemma local_per_int_bar {o} :
  forall inh (ts : cts(o)), local_ts inh (per_int_bar inh ts).
Proof.
  introv eqiff alla.
  unfold per_int_bar in *.
  apply in_open_bar_ext_prod in alla; repnd.
  apply in_open_bar_ext_prod in alla; repnd.
  dands; try (complete (apply in_open_bar_ext_in_open_bar; auto)).
  eapply eq_term_equals_trans;[eauto|]; clear eqiff; eauto 3 with slow.
Qed.
Hint Resolve local_per_int_bar : slow.

Lemma dest_close_per_int_l {p} :
  forall inh (ts : cts(p)) lib T T' eq,
    type_system inh ts
    -> defines_only_universes inh ts
    -> ccomputes_to_valc_ext inh lib T mkc_int
    -> close inh ts lib T T' eq
    -> per_int_bar inh (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca; apply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_int_r {p} :
  forall inh (ts : cts(p)) lib T T' eq,
    type_system inh ts
    -> defines_only_universes inh ts
    -> ccomputes_to_valc_ext inh lib T' mkc_int
    -> close inh ts lib T T' eq
    -> per_int_bar inh (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca; apply reca; eauto 3 with slow.
Qed.

(*Lemma dest_close_per_int_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_int)
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_int_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_int)
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_int_ceq_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) mkc_int
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_int_ceq_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T' ==b==>(bar) mkc_int
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_int_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
 *)
