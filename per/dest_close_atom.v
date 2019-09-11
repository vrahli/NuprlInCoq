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
Require Export bar_fam.


Lemma local_equality_of_atom_bar {o} :
  forall {lib} (bar : @BarLib o lib) t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => equality_of_atom_bar lib' t1 t2)
    -> equality_of_atom_bar lib t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.
Hint Resolve local_equality_of_atom_bar : slow.

Lemma per_bar_eq_equality_of_atom_bar_implies {o} :
  forall {lib} (bar : @BarLib o lib) t1 t2,
    per_bar_eq bar (equality_of_atom_bar_lib_per lib) t1 t2
    -> equality_of_atom_bar lib t1 t2.
Proof.
  introv alla.
  unfold per_bar_eq in alla.

  apply e_all_in_ex_bar_as; introv ext.
  rewrite e_all_in_bar_ext_as in alla.
  pose proof (alla _ ext) as alla; exrepnd.
  apply in_ext_ext_implies in alla1.
  pose proof (alla1 (lib_extends_trans y ext)) as alla1.
  rewrite e_all_in_ex_bar_ext_as in alla1.
  pose proof (alla1 _ (lib_extends_refl _)) as alla1; exrepnd.
  apply in_ext_ext_implies in alla1.
  pose proof (alla1 y0) as alla1; simpl in *.
  unfold equality_of_atom_bar in *.
  rewrite e_all_in_ex_bar_as in alla1.
  pose proof (alla1 _ (lib_extends_refl _)) as alla1; exrepnd.
  assert (lib_extends lib''1 lib') as xt' by eauto 3 with slow.
  exists lib''1 xt'; auto.
Qed.
Hint Resolve per_bar_eq_equality_of_atom_bar_implies : slow.

Lemma in_ext_equality_of_atom_implies_equality_of_atom_bar {o} :
  forall (lib1 lib2 : @library o) t1 t2,
    lib_extends lib2 lib1
    -> in_ext lib1 (fun lib => equality_of_atom lib t1 t2)
    -> equality_of_atom_bar lib2 t1 t2.
Proof.
  introv ext h.
  unfold equality_of_atom_bar.
  apply e_all_in_ex_bar_as.
  introv xt.
  exists lib' (lib_extends_refl lib'); eauto 3 with slow.
Qed.
Hint Resolve in_ext_equality_of_atom_implies_equality_of_atom_bar : slow.

Lemma in_open_bar_ext_equal_equality_of_atom_bar_implies_per_bar_eq_implies_equality_of_atom_bar {o} :
  forall lib (bar : @BarLib o lib) (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (equality_of_atom_bar lib'))
    -> (per_bar_eq bar eqa) <=2=> (equality_of_atom_bar lib).
Proof.
  introv alla; introv; split; introv h.

  - pose proof (in_open_bar_ext_eq_term_equals_preserves_per_bar_eq
                  _ bar eqa (equality_of_atom_bar_lib_per lib) t1 t2 alla h) as q.
    eauto 3 with slow.

  - apply e_all_in_ex_bar_as in h.
    apply e_all_in_bar_ext_as.
    introv ext.
    exists lib' (lib_extends_refl lib'); introv xta; introv.
    apply e_all_in_ex_bar_ext_as.
    introv ext'.
    pose proof (h lib'1 (lib_extends_trans ext' z)) as h; exrepnd.

    assert (lib_extends lib'' lib) as xtb by eauto 3 with slow.
    pose proof (alla lib'' xtb) as alla; exrepnd.

    assert (lib_extends lib''0 lib'1) as xtc by eauto 3 with slow.
    exists lib''0 xtc; introv xtd; introv.
    pose proof (alla1 _ xtd (lib_extends_trans z0 z)) as alla1; simpl in *.
    apply alla1; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_ext_equal_equality_of_atom_bar_implies_per_bar_eq_implies_equality_of_atom_bar : slow.

Lemma local_per_atom_bar {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> e_all_in_bar_ext bar (fun lib' x => per_atom_bar ts lib' T T' (eqa lib' x))
    -> per_atom_bar ts lib T T' eq.
Proof.
  introv eqiff alla.
  unfold per_atom_bar in *.
  apply e_all_in_bar_ext_as in alla.
  apply @in_open_bar_ext_prod in alla; repnd.
  dands.

  { exists (trivial_bar lib); dands; apply e_all_in_bar_as.

    { introv ext.
      pose proof (alla0 _ ext) as alla0; exrepnd.
      apply in_ext_ext_implies in alla0; autodimp alla0 hyp; eauto 3 with slow; exrepnd.
      apply e_all_in_bar_as in alla0.
      pose proof (alla0 _ (lib_extends_refl _)) as alla0; exrepnd.
      exists lib''0; dands; eauto 3 with slow. }

    { introv ext.
      pose proof (alla0 _ ext) as alla0; exrepnd.
      apply in_ext_ext_implies in alla0; autodimp alla0 hyp; eauto 3 with slow; exrepnd.
      apply e_all_in_bar_as in alla1.
      pose proof (alla1 _ (lib_extends_refl _)) as alla1; exrepnd.
      exists lib''0; dands; eauto 3 with slow. } }

  eapply eq_term_equals_trans;[eauto|]; eauto 3 with slow.
Qed.

Lemma per_atom_implies_per_atom_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_atom ts lib T T' eq
    -> per_atom_bar ts lib T T' eq.
Proof.
  introv per.
  unfold per_atom in per; repnd.
  unfold per_atom_bar.
  dands; auto.
  exists (trivial_bar lib).
  dands; eauto 3 with slow.
Qed.
Hint Resolve per_atom_implies_per_atom_bar : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_atom_l {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_atom_bar; eauto.
  apply e_all_in_bar_ext_as in reca.
  apply e_all_in_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto.
  introv h; apply h; eauto 3 with slow.
Qed.

Lemma dest_close_per_atom_r {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_atom_bar; eauto.
  apply e_all_in_bar_ext_as in reca.
  apply e_all_in_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto.
  introv h; apply h; eauto 3 with slow.
Qed.

(*
Lemma dest_close_per_atom_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_atom)
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_atom_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_atom_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_atom)
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_atom_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_atom_ceq_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_atom_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_atom_ceq_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T' ==b==>(bar) mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_atom_bar; eauto.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
*)
