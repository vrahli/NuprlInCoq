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
    <=> all_in_ex_bar lib (fun lib => equal_in_qtime lib mkc_tnat t1 t2).
Proof.
  introv.
  rw @equality_mkc_qtime.
  split; intro h; repnd; dands; eauto 2 with slow.
Qed.

Lemma nat_in_tnat {o} :
  forall (lib : @library o) k,
    equality lib (mkc_nat k) (mkc_nat k) mkc_tnat.
Proof.
  introv.
  apply equality_in_tnat.
  apply in_ext_implies_all_in_ex_bar; introv xt'.
  exists k; dands; eauto 2 with slow.
Qed.
Hint Resolve nat_in_tnat : slow.

Lemma equal_in_qtime_nat {o} :
  forall (lib : @library o) k,
    equal_in_qtime lib mkc_tnat (mkc_nat k) (mkc_nat k).
Proof.
  introv; apply (eq_in_qtime_eq _ _ _ _ (mkc_nat k) (mkc_nat k)); spcast; eauto 3 with slow.
Qed.
Hint Resolve equal_in_qtime_nat : slow.

Lemma equality_nat_in_qtnat {o} :
  forall (lib : @library o) k, equality lib (mkc_nat k) (mkc_nat k) mkc_qtnat.
Proof.
  introv.
  apply equality_in_qtnat; eauto 2 with slow.
  apply in_ext_implies_all_in_ex_bar; introv xt; eauto 3 with slow.
Qed.
Hint Resolve equality_nat_in_qtnat : slow.
