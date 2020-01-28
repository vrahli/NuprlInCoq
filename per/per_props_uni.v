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

 *)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.

(*Require Export per_props_nat.*)


Lemma per_bar_eq_univi_eq_lib_per_implies {o} :
  forall (lib : @library o) i a b,
    per_bar_eq lib (univi_eq_lib_per lib i) a b
    -> in_open_bar_ext lib (fun (lib' : library) x => univi_eq (univi_bar i) lib' a b).
Proof.
  introv per; tcsp.
Qed.

Lemma equality_in_uni {o} :
  forall lib (a b : @CTerm o) i,
    equality lib a b (mkc_uni i)
    -> tequality lib a b.
Proof.
  unfold tequality, equality, nuprl; introv e; exrepnd.

  apply dest_nuprl_uni in e1.
  apply univ_implies_univi_bar3 in e1; exrepnd.
  apply e1 in e0.
  clear dependent eq.
  unfold per_bar_eq in e0; simpl in *.
  unfold univi_eq in e0.
  fold (@nuprli o i) in *.

  apply in_open_bar_ext_choice in e0; exrepnd.
  apply in_open_bar_eqa_choice_non_dep in e1; exrepnd.

  exists (per_bar_eq lib (lib_fun_non_dep_eqa Feqa)).
  apply CL_bar; exists (lib_fun_non_dep_eqa Feqa); dands; auto.
  fold (@nuprl o); simpl.
  introv ext.
  assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
  exists (Flib _ ext) xta.
  introv xtb xtc.

  pose proof (e0 _ ext _ xtb xtc) as q; simpl in *.
  eapply type_extensionality_nuprl;[eauto 3 with slow|].
  introv; split; intro h.

  { exists lib' ext lib'0 xtb xtc (lib_extends_refl lib'0); auto. }

  exrepnd.
  pose proof (e0 _ ext1 _ ext2 extz) as w.
  eapply (nuprli_monotone _ lib2 lib'0) in w; auto; exrepnd.
  apply nuprli_refl in w1.
  apply nuprli_refl in q.
  eapply nuprli_uniquely_valued in w1; try exact q; apply w1; clear w1; apply w0; auto.
Qed.
Hint Resolve equality_in_uni : slow.

Lemma member_in_uni {p} :
  forall lib a i, @member p lib a (mkc_uni i) -> type lib a.
Proof.
  unfold member, type; introv e.
  apply equality_in_uni in e; sp.
Qed.
Hint Resolve member_in_uni : slow.

Lemma mkc_uni_in_nuprl {o} :
  forall (lib : @library o) (i : nat),
    nuprl lib (mkc_uni i) (mkc_uni i) (per_bar_eq lib (univi_eq_lib_per lib i)).
Proof.
  introv.
  apply CL_init.
  exists (univi_eq_lib_per lib i); dands; tcsp.
  apply in_ext_ext_implies_in_open_bar_ext; introv.
  exists (S i); simpl.
  left; sp; eauto 3 with slow.
Qed.
Hint Resolve mkc_uni_in_nuprl : slow.

Lemma uni_in_uni {o} :
  forall lib i j, i < j -> @member o lib (mkc_uni i) (mkc_uni j).
Proof.
  introv h.
  unfold member, equality.
  exists (per_bar_eq lib (univi_eq_lib_per lib j)); dands; eauto 2 with slow.

  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl.
  exists (per_bar_eq lib' (univi_eq_lib_per lib' i)); dands; eauto 2 with slow.
  apply CL_init.
  exists (univi_eq_lib_per lib' i); dands; tcsp.
  apply in_ext_ext_implies_in_open_bar_ext; introv.
  apply univi_exists_iff.
  exists i; dands; spcast; eauto 3 with slow.
Qed.

Lemma cumulativity {o} :
  forall lib i j (A B : @CTerm o),
    i <= j
    -> equality lib A B (mkc_uni i)
    -> equality lib A B (mkc_uni j).
Proof.
  introv h e.
  unfold member, equality in *; exrepnd.
  apply dest_nuprl_uni in e1.
  apply univ_implies_univi_bar3 in e1; exrepnd.
  apply e1 in e0; clear e1.

  exists (per_bar_eq lib (univi_eq_lib_per lib j)); dands; eauto 2 with slow.
  eapply in_open_bar_ext_pres; try exact e0; clear e0; introv e0; simpl in *.

  unfold univi_eq in *; exrepnd.
  exists eqa.
  fold (@nuprli o i) in *.
  fold (@nuprli o j) in *.
  pose proof (typable_in_higher_univ i lib' A B eqa e1 (j - i)) as q.
  rewrite minus_plus_n in q; auto; try omega.
Qed.

Lemma nuprl_mkc_uni {p} :
  forall lib (i : nat),
    {eq : per(p) , nuprl lib (mkc_uni i) (mkc_uni i) eq}.
Proof.
  introv.
  exists (per_bar_eq lib (univi_eq_lib_per lib i)); eauto 2 with slow.
Qed.

Lemma tequality_mkc_uni {p} :
  forall lib (i : nat), @tequality p lib (mkc_uni i) (mkc_uni i).
Proof.
  generalize (@nuprl_mkc_uni p); sp.
Qed.
Hint Resolve tequality_mkc_uni : slow.

Lemma type_mkc_uni {o} :
  forall lib (i : nat), @type o lib (mkc_uni i).
Proof.
  unfold type; eauto 3 with slow.
Qed.
Hint Resolve type_mkc_uni : slow.

Lemma per_bar_eq_univi_eq_lib_per_implies_eq_nuprli {o} :
  forall lib i (A B : @CTerm o),
    per_bar_eq lib (univi_eq_lib_per lib i) A B
    -> exists eq', nuprli i lib A B eq'.
Proof.
  introv e0.
  unfold per_bar_eq in e0; simpl in *.
  unfold univi_eq in e0.

  apply in_open_bar_ext_choice in e0; exrepnd.
  apply in_open_bar_eqa_choice_non_dep in e1; exrepnd.

  exists (per_bar_eq lib (lib_fun_non_dep_eqa Feqa)).
  apply CL_bar; exists (lib_fun_non_dep_eqa Feqa); dands; auto.
  fold (@nuprl o); simpl.
  introv ext.
  assert (lib_extends (Flib lib' ext) lib') as xta by eauto 3 with slow.
  exists (Flib _ ext) xta.
  introv xtb xtc.
  fold (@nuprli o i) in *.

  pose proof (e0 _ ext _ xtb xtc) as q; simpl in *.
  eapply nuprli_type_extensionality;[eauto 3 with slow|].
  introv; split; intro h.

  { exists lib' ext lib'0 xtb xtc (lib_extends_refl lib'0); auto. }

  exrepnd.
  pose proof (e0 _ ext1 _ ext2 extz) as w.
  eapply (nuprli_monotone _ lib2 lib'0) in w; auto; exrepnd.
  apply nuprli_refl in w1.
  apply nuprli_refl in q.
  eapply nuprli_uniquely_valued in w1; try exact q; apply w1; clear w1; apply w0; auto.
Qed.

Lemma equality_nuprli {o} :
  forall lib (A B C : @CTerm o) i eq,
    equality lib A B (mkc_uni i)
    -> nuprli i lib A C eq
    -> nuprli i lib A B eq.
Proof.
  introv e n.
  unfold equality in e; exrepnd.
  apply dest_nuprl_uni in e1.
  apply univ_implies_univi_bar3 in e1; exrepnd.
  apply e1 in e0; clear e1.
  apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in e0; exrepnd.
  eapply nuprli_type_extensionality;[eauto|].
  apply nuprli_refl in e1.
  apply nuprli_refl in n.
  eapply nuprli_uniquely_valued; eauto.
Qed.
