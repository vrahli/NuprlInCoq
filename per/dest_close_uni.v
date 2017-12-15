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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export dest_close_tacs.


(*Definition ts_or_per_bar {o} ts lib (T1 T2 : @CTerm o) eq :=
  ts lib T1 T2 eq {+} per_bar (close ts) lib T1 T2 eq.*)

Lemma dest_close_per_uni_l {p} :
  forall (ts : cts(p)) lib T i T' eq,
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_uni i)
    -> close ts lib T T' eq
    -> (*ts_or_per_bar*) ts lib  T T' eq.
Proof.
  introv locts tysys dou comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_uni_r {p} :
  forall (ts : cts(p)) lib T i T' eq,
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_uni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv locts tysys dou comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_uni_bar_l {p} :
  forall (ts : cts(p)) lib T i T' eq (bar : BarLib lib),
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_uni i))
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv locts tysys dou mon comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_uni_bar_r {p} :
  forall (ts : cts(p)) lib T i T' eq (bar : BarLib lib),
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_uni i))
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv locts tysys dou mon comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_uni_ceq_bar_l {p} :
  forall (ts : cts(p)) lib T i T' eq (bar : BarLib lib),
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_uni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv locts tysys dou mon comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_uni_ceq_bar_r {p} :
  forall (ts : cts(p)) lib T i T' eq (bar : BarLib lib),
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T' ==b==>(bar) (mkc_uni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv locts tysys dou mon comp cl; unfold ts_or_per_bar.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto.
  eapply locts; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
