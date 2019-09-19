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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

 *)


Require Export per_props_qtime.
Require Export per_props_nat.


Definition mkc_qtnat {o} := @mkc_qtime o mkc_tnat.

Definition mk_qtnat {o} := @mk_qtime o mk_tnat.

Lemma lsubstc_qtnat {o} :
  forall w (s : @CSub o) c,
    lsubstc mk_qtnat w s c = mkc_qtnat.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.
Hint Rewrite @lsubstc_qtnat : slow.

Lemma tequality_qtnat {o} :
  forall (lib : @library o), tequality lib mkc_qtnat mkc_qtnat.
Proof.
  introv; apply tequality_mkc_qtime; apply type_tnat.
Qed.
Hint Resolve tequality_qtnat : slow.

Lemma ccomputes_to_valc_ext_nat_implies_computes_to_valc {o} :
  forall (lib : @library o) a n,
    (a) ===>(lib) (mkc_nat n)
    -> ccomputes_to_valc lib a (mkc_nat n).
Proof.
  introv comp.
  eapply ccomputes_to_valc_ext_integer_implies_computes_to_valc_in_ext;[|eauto]; eauto 2 with slow.
Qed.

Lemma equality_in_qtnat {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_qtnat
    <=> in_open_bar lib (fun lib => {a1, a2 : CTerm
             , ccequivc lib t1 a1
             # ccequivc lib t2 a2
             # ccequivc_ext lib t1 t2
             # in_open_bar lib (fun lib => {n : nat
                    , ccomputes_to_valc_ext lib a1 (mkc_nat n)
                    # ccomputes_to_valc_ext lib a2 (mkc_nat n)})}).
Proof.
  introv.
  rw @equality_mkc_qtime.
  split; intro h; repnd; dands; eauto 2 with slow;[|].

  - eapply all_in_ex_bar_modus_ponens1;[|exact h]; clear h; introv x h; exrepnd; spcast.
    exists a1 a2; dands; spcast; auto.
    apply equality_in_tnat in h2; apply e_all_in_ex_bar_as in h2.
    eapply all_in_ex_bar_modus_ponens1;[|exact h2]; clear h2; introv y h2; exrepnd; spcast.
    unfold equality_of_nat in h2; exrepnd.
    eexists; dands; eauto.

  - eapply all_in_ex_bar_modus_ponens1;[|exact h]; clear h; introv x h; exrepnd; spcast.
    exists a1 a2; dands; spcast; auto.
    apply equality_in_tnat; apply e_all_in_ex_bar_as.
    eapply all_in_ex_bar_modus_ponens1;[|exact h1]; clear h1; introv y h1; exrepnd; spcast.
    unfold equality_of_nat; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma equality_nat_in_qtnat {o} :
  forall (lib : @library o) k, equality lib (mkc_nat k) (mkc_nat k) mkc_qtnat.
Proof.
  introv.
  apply equality_in_qtnat; eauto 2 with slow.
  apply in_ext_implies_all_in_ex_bar; introv xt.
  exists (@mkc_nat o k) (@mkc_nat o k).
  dands; spcast; eauto 2 with slow.
  apply in_ext_implies_all_in_ex_bar; introv xt'.
  exists k; dands; eauto 2 with slow.
Qed.
Hint Resolve equality_nat_in_qtnat : slow.
