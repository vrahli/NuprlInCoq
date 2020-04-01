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
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export local.
Require Export per_ceq_bar.


(*Lemma in_ext_implies_all_in_bar_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext lib F
    -> all_in_bar (trivial_bar lib) F.
Proof.
  introv f br ext; introv.
  eapply f; eauto 3 with slow.
Qed.*)

(*Lemma collapse2bars {o} :
  forall {lib} F,
    (exists (bar : @BarLib o lib),
        all_in_bar_ext
          bar
          (fun lib' x => exists (bar' : @BarLib o lib'), all_in_bar bar' F))
      <=> exists (bar : @BarLib o lib), all_in_bar bar F.
Proof.
  introv; split; introv h.

  - exrepnd.
    apply all_in_bar_ext_exists_bar_implies in h0; exrepnd; simpl in *.
    exists (bar_of_bar_fam fbar).
    introv br ext; simpl in *; exrepnd.
    pose proof (h1 _ br _ ext0 x _ br0 _ ext) as h1; auto.

  - exrepnd.
    exists bar.
    introv br ext x.
    exists (trivial_bar lib'0).
    apply in_ext_implies_all_in_bar_trivial_bar.
    introv y.
    eapply h0; eauto 3 with slow.
Qed.*)

(*Lemma collapse2bars_ext {o} :
  forall {lib}
         (F : forall (lib' : library) (x : lib_extends lib' lib), Prop)
         (cond : forall lib' (x y : lib_extends lib' lib), F lib' x <=> F lib' y),
    (exists (bar : @BarLib o lib),
        all_in_bar_ext
          bar
          (fun lib' x =>
             exists (bar' : @BarLib o lib'),
               all_in_bar_ext
                 bar'
                 (fun lib'' y => F lib'' (lib_extends_trans y x))))
      <=> exists (bar : @BarLib o lib), all_in_bar_ext bar F.
Proof.
  introv cond; split; introv h.

  - exrepnd.
    apply all_in_bar_ext_exists_bar_implies in h0; exrepnd; simpl in *.
    exists (bar_of_bar_fam fbar).
    introv br ext; introv; simpl in *; exrepnd.
    assert (lib_extends lib'0 lib2) as xt by eauto 3 with slow.
    pose proof (h1 _ br _ ext0 x0 _ br0 _ ext xt) as h1; simpl in *; auto.
    eapply cond; eauto.

  - exrepnd.
    exists bar.
    introv br ext; introv.
    exists (trivial_bar lib'0).
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv.
    eapply h0; eauto 3 with slow.
Qed.*)

Lemma type_extensionality_per_bar {o} :
  forall (ts : cts(o)),
    type_extensionality (per_bar ts).
Proof.
  introv per eqiff.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_bar : slow.

Lemma type_symmetric_per_bar {o} :
  forall (ts : cts(o)),
    type_symmetric ts
    -> type_symmetric (per_bar ts).
Proof.
  introv sym per.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; introv h; auto.
Qed.
Hint Resolve type_symmetric_per_bar : slow.

(*Lemma per_bar_eq_intersect_bars_left {o} :
  forall {lib} (bar bar' : @BarLib o lib) eqa,
    (per_bar_eq (intersect_bars bar bar') eqa) <=2=> (per_bar_eq bar eqa).
Proof.
  repeat introv; unfold per_bar_eq; split; introv h; eauto 3 with slow;[].
  apply per_bar_eq_iff2.
  exists bar'; auto.
Qed.
Hint Resolve per_bar_eq_intersect_bars_left : slow.*)

(*Lemma implies_all_in_bar_ext_intersect_bars_swap {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar bar') F
    -> all_in_bar_ext (intersect_bars bar' bar) F.
Proof.
  introv h br ext; introv; simpl in *; exrepnd.
  pose proof (h lib') as h; simpl in *; autodimp h hyp.
  eexists; eexists; dands; eauto.
Qed.*)

(*Lemma per_bar_eq_intersect_bars_right {o} :
  forall {lib} (bar bar' : @BarLib o lib) eqa,
    (per_bar_eq (intersect_bars bar' bar) eqa) <=2=> (per_bar_eq bar eqa).
Proof.
  repeat introv; unfold per_bar_eq; split; introv h; eauto 3 with slow;[].
  apply per_bar_eq_iff2.
  exists bar'; auto.
  apply implies_all_in_bar_ext_intersect_bars_swap; auto.
Qed.
Hint Resolve per_bar_eq_intersect_bars_right : slow.*)

Lemma type_transitive_per_bar {o} :
  forall (ts : cts(o)),
    uniquely_valued ts
    -> type_extensionality ts
    -> type_symmetric ts
    -> type_transitive ts
    -> type_transitive (per_bar ts).
Proof.
  introv uv text sym trans pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb;[|exact pera1]; clear pera1.
  eapply in_open_bar_ext_comb;[|exact perb1]; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext.
  introv pera1 perb1.
  eapply uniquely_valued_trans7; eauto.
Qed.
Hint Resolve type_transitive_per_bar : slow.

Lemma type_value_respecting_per_bar {o} :
  forall (ts : cts(o)),
    type_value_respecting ts
    -> type_value_respecting (per_bar ts).
Proof.
  introv resp per ceq.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb;[|exact per1]; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv h; auto.
  apply resp; eauto 3 with slow.
Qed.
Hint Resolve type_value_respecting_per_bar : slow.

(*Lemma term_symmetric_all_in_bar_ext_implies {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> term_symmetric ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv alla sym br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply sym; eauto.
Qed.*)

Lemma term_symmetric_in_open_bar_ext_implies {o} :
  forall uk (lib : @library o) ts T T' (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => ts uk lib' T T' (eqa lib' x))
    -> term_symmetric ts
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv alla sym.
  eapply in_open_bar_ext_comb;[|exact alla]; clear alla.
  apply in_ext_ext_implies_in_open_bar_ext; introv h.
  eapply sym; eauto.
Qed.

Lemma per_bar_eq_sym {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> per_bar_eq lib eqa t1 t2
    -> per_bar_eq lib eqa t2 t1.
Proof.
  introv sym per; unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb;[|exact sym];clear sym.
  eapply in_open_bar_ext_comb;[|exact per];clear per.
  apply in_ext_ext_implies_in_open_bar_ext; introv per sym.
  eapply sym; eauto 3 with slow.
Qed.
Hint Resolve per_bar_eq_sym : slow.

Lemma term_symmetric_per_bar {o} :
  forall (ts : cts(o)),
    term_symmetric ts
    -> term_symmetric (per_bar ts).
Proof.
  introv sym per e.
  unfold per_bar in *; exrepnd.
  allrw per0.
  apply term_symmetric_in_open_bar_ext_implies in per1; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_per_bar : slow.

(*Lemma term_transitive_all_in_bar_ext_implies {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> term_transitive ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv alla sym br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply sym; eauto.
Qed.*)

Lemma term_transitive_in_open_bar_ext_implies {o} :
  forall uk (lib : @library o) ts T T' (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => ts uk lib' T T' (eqa lib' x))
    -> term_transitive ts
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv alla sym.
  eapply in_open_bar_ext_comb;[|exact alla];clear alla.
  apply in_ext_ext_implies_in_open_bar_ext; introv alla.
  eapply sym; eauto.
Qed.

Lemma per_bar_eq_trans {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) t1 t2 t3,
    in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> per_bar_eq lib eqa t1 t2
    -> per_bar_eq lib eqa t2 t3
    -> per_bar_eq lib eqa t1 t3.
Proof.
  introv trans pera perb; unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb;[|exact trans];clear trans.
  eapply in_open_bar_ext_comb;[|exact pera];clear pera.
  eapply in_open_bar_ext_comb;[|exact perb];clear perb.
  apply in_ext_ext_implies_in_open_bar_ext; introv pera perb trans.
  eapply trans; eauto 4 with slow.
Qed.
Hint Resolve per_bar_eq_trans : slow.

Lemma term_transitive_per_bar {o} :
  forall (ts : cts(o)),
    term_transitive ts
    -> term_transitive (per_bar ts).
Proof.
  introv sym per e1 e2.
  unfold per_bar in *; exrepnd.
  allrw per0.
  apply term_transitive_in_open_bar_ext_implies in per1; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_per_bar : slow.

(*Lemma term_value_respecting_all_in_bar_ext_implies {o} :
  forall {lib} (bar : @BarLib o lib) ts T (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T (eqa lib' x))
    -> term_value_respecting ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv alla val br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply val; eauto.
Qed.*)

Lemma term_value_respecting_in_open_bar_ext_implies {o} :
  forall uk (lib : @library o) ts T (eqa : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => ts uk lib' T T (eqa lib' x))
    -> term_value_respecting ts
    -> in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv alla val.
  eapply in_open_bar_ext_comb;[|exact alla];clear alla.
  apply in_ext_ext_implies_in_open_bar_ext; introv alla.
  eapply val; eauto.
Qed.

Lemma per_bar_eq_value_respecting {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) t t',
    in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> ccequivc_ext lib t t'
    -> per_bar_eq lib eqa t t
    -> per_bar_eq lib eqa t t'.
Proof.
  introv resp ceq pera; unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb;[|exact resp];clear resp.
  eapply in_open_bar_ext_comb;[|exact pera];clear pera.
  apply in_ext_ext_implies_in_open_bar_ext; introv pera resp.
  eapply resp; eauto 3 with slow.
Qed.
Hint Resolve per_bar_eq_value_respecting : slow.

Lemma term_value_respecting_per_bar {o} :
  forall (ts : cts(o)),
    term_value_respecting ts
    -> term_value_respecting (per_bar ts).
Proof.
  introv val per e1 e2.
  unfold per_bar in *; exrepnd.
  allrw per0.
  apply term_value_respecting_in_open_bar_ext_implies in per1; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_per_bar : slow.

Definition uniquely_valued2 {p} (ts : cts(p)) :=
  forall uk lib T T1 T2 eq eq',
    ts uk lib T T1 eq -> ts uk lib T T2 eq' -> eq <=2=> eq'.

Lemma uniquely_valued2_per_bar {o} :
  forall (ts : cts(o)),
    uniquely_valued2 ts
    -> uniquely_valued2 (per_bar ts).
Proof.
  introv uv p q.
  unfold per_bar, per_bar_eq in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear p0 q0.

  introv; split; introv h.

  - eapply in_open_bar_ext_comb;[|exact p1];clear p1.
    eapply in_open_bar_ext_comb;[|exact q1];clear q1.
    eapply in_open_bar_ext_comb;[|exact h];clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv h q1 p1.
    eapply uv in p1; autodimp p1 hyp;[exact q1|].
    apply p1; auto.

  - eapply in_open_bar_ext_comb;[|exact p1];clear p1.
    eapply in_open_bar_ext_comb;[|exact q1];clear q1.
    eapply in_open_bar_ext_comb;[|exact h];clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv h q1 p1.
    eapply uv in p1; autodimp p1 hyp;[exact q1|].
    apply p1; auto.
Qed.
Hint Resolve uniquely_valued2_per_bar : slow.
