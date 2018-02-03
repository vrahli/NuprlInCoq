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
  forall {lib} (bar : @BarLib o lib) i a b,
    per_bar_eq bar (univi_eq_lib_per lib i) a b
    -> exists (bar : BarLib lib), all_in_bar_ext bar (fun (lib' : library) x => univi_eq (univi_bar i) lib' a b).
Proof.
  introv per.

  assert (exists (bar : BarLib lib), per_bar_eq bar (univi_eq_lib_per lib i) a b) as h by (exists bar; auto).
  clear per; rename h into per.

  pose proof (@collapse2bars_ext o lib (fun lib' x => univi_eq (univi_bar i) lib' a b)) as q.
  simpl in q; autodimp q hyp; tcsp;[].
  apply q in per; clear q.
  exrepnd.
  exists bar0; auto.
Qed.

Lemma equality_in_uni {o} :
  forall lib (a b : @CTerm o) i,
    equality lib a b (mkc_uni i)
    -> tequality lib a b.
Proof.
  unfold tequality, equality, nuprl; introv e; exrepnd.

  apply dest_nuprl_uni in e1.
  apply univ_implies_univi_bar3 in e1; exrepnd.
  apply e2 in e0.
  clear dependent eq.

  apply per_bar_eq_univi_eq_lib_per_implies in e0.
  clear dependent bar; exrepnd.
  unfold univi_eq in e1.
  fold (@nuprli o i) in *.

  apply all_in_bar_ext_exists_per_implies_exists in e1; exrepnd.
  exists (per_bar_eq bar (bar_per2lib_per feqa)).
  apply CL_bar; exists bar (bar_per2lib_per feqa); dands; tcsp;[].

  introv br xt ; introv; simpl; fold (@nuprl o).
  pose proof (e0 _ br _ xt x) as q.
  eapply type_extensionality_nuprl;[eauto 3 with slow|].

  introv; split; intro h.

  { exists lib' br xt x; auto. }

  exrepnd.
  pose proof (e0 _ br0 _ ext x0) as e0.
  eapply nuprli_uniquely_valued in e0; try exact q.
  apply e0; auto.
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
  forall (lib : @library o) (i : nat) (bar : BarLib lib),
    nuprl lib (mkc_uni i) (mkc_uni i) (per_bar_eq bar (univi_eq_lib_per lib i)).
Proof.
  introv.
  apply CL_init.
  exists bar (univi_eq_lib_per lib i); dands; tcsp.
  exists (S i); simpl.
  left; sp; spcast; apply computes_to_valc_refl; sp.
Qed.
Hint Resolve mkc_uni_in_nuprl : slow.

Lemma uni_in_uni {o} :
  forall lib i j, i < j -> @member o lib (mkc_uni i) (mkc_uni j).
Proof.
  introv h.
  unfold member, equality.
  exists (per_bar_eq (trivial_bar lib) (univi_eq_lib_per lib j)); dands; eauto 2 with slow.

  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
  exists (trivial_bar lib').
  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
  simpl.

  exists (per_bar_eq (trivial_bar lib'0) (univi_eq_lib_per lib'0 i)); dands; eauto 2 with slow.

  apply CL_init.
  exists (trivial_bar lib'0) (univi_eq_lib_per lib'0 i); dands; tcsp.
  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv.
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
  apply e2 in e0.

  exists (per_bar_eq bar (univi_eq_lib_per lib j)); dands; eauto 2 with slow.
  introv br ext; introv.
  pose proof (e0 _ br _ ext x) as e0; simpl in *.
  exrepnd.
  exists bar'.
  introv br' ext' x'.
  pose proof (e1 _ br' _ ext' x') as e1; simpl in *.

  unfold univi_eq in *; exrepnd.
  exists eqa.
  fold (@nuprli o i) in *.
  fold (@nuprli o j) in *.
  pose proof (typable_in_higher_univ i lib'2 A B eqa e0 (j - i)) as q.
  rewrite minus_plus_n in q; auto; try omega.
Qed.

Lemma nuprl_mkc_uni {p} :
  forall lib (i : nat),
    {eq : per(p) , nuprl lib (mkc_uni i) (mkc_uni i) eq}.
Proof.
  introv.
  exists (per_bar_eq (trivial_bar lib) (univi_eq_lib_per lib i)); eauto 2 with slow.
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
  forall lib (bar : BarLib lib) i (A B : @CTerm o),
    per_bar_eq bar (univi_eq_lib_per lib i) A B
    -> exists eq', nuprli i lib A B eq'.
Proof.
  introv e0.
  unfold per_bar_eq in e0; simpl in *.
  apply per_bar_eq_univi_eq_lib_per_implies in e0.
  clear dependent bar.
  exrepnd.
  unfold univi_eq in e1.
  apply all_in_bar_ext_exists_per_implies_exists in e1; exrepnd.

  exists (per_bar_eq bar (bar_per2lib_per feqa)).
  apply CL_bar; exists bar (bar_per2lib_per feqa); dands; tcsp;[].
  introv br ext; introv.
  pose proof (e0 _ br _ ext x) as q; simpl in *.
  fold (@nuprli o i) in *.
  eapply nuprli_type_extensionality;[eauto 3 with slow|].

  introv; split; intro h.

  { exists lib' br ext x; auto. }

  exrepnd.
  pose proof (e0 _ br0 _ ext0 x0) as e0.
  eapply nuprli_uniquely_valued in e0; try exact q.
  apply e0; auto.
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
  apply e2 in e0.
  apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in e0; exrepnd.
  eapply nuprli_type_extensionality;[eauto|].
  apply nuprli_refl in e1.
  apply nuprli_refl in n.
  eapply nuprli_uniquely_valued; eauto.
Qed.
