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


Lemma in_ext_implies_all_in_bar_trivial_bar {o} :
  forall (lib : @SL o) F,
    in_ext lib F
    -> all_in_bar (trivial_bar lib) F.
Proof.
  introv f br ext; introv.
  eapply f; eauto 3 with slow.
Qed.

Lemma collapse2bars {o} :
  forall {lib : SL} F,
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
Qed.

Lemma collapse2bars_ext {o} :
  forall {lib : SL}
         (F : forall (lib' : SL) (x : lib_extends lib' lib), Prop)
         (cond : forall (lib' : SL) (x y : lib_extends lib' lib), F lib' x <=> F lib' y),
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
Qed.

Lemma type_extensionality_per_bar {o} :
  forall (ts : cts(o)),
    type_extensionality (per_bar ts).
Proof.
  introv per eqiff.
  unfold per_bar in *; exrepnd.
  exists bar eqa; dands; auto.
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
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply sym; auto.
Qed.
Hint Resolve type_symmetric_per_bar : slow.

Lemma per_bar_eq_intersect_bars_left {o} :
  forall {lib : SL} (bar bar' : @BarLib o lib) eqa,
    (per_bar_eq (intersect_bars bar bar') eqa) <=2=> (per_bar_eq bar eqa).
Proof.
  repeat introv; unfold per_bar_eq; split; introv h; eauto 3 with slow;[].
  apply per_bar_eq_iff2.
  exists bar'; auto.
Qed.
Hint Resolve per_bar_eq_intersect_bars_left : slow.

Lemma implies_all_in_bar_ext_intersect_bars_swap {o} :
  forall {lib : SL} (bar bar' : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar bar') F
    -> all_in_bar_ext (intersect_bars bar' bar) F.
Proof.
  introv h br ext; introv; simpl in *; exrepnd.
  pose proof (h lib') as h; simpl in *; autodimp h hyp.
  eexists; eexists; dands; eauto.
Qed.

Lemma per_bar_eq_intersect_bars_right {o} :
  forall {lib : SL} (bar bar' : @BarLib o lib) eqa,
    (per_bar_eq (intersect_bars bar' bar) eqa) <=2=> (per_bar_eq bar eqa).
Proof.
  repeat introv; unfold per_bar_eq; split; introv h; eauto 3 with slow;[].
  apply per_bar_eq_iff2.
  exists bar'; auto.
  apply implies_all_in_bar_ext_intersect_bars_swap; auto.
Qed.
Hint Resolve per_bar_eq_intersect_bars_right : slow.

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
  exists (intersect_bars bar0 bar) eqa0; dands; auto.

  {
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (pera0 _ br0 lib'0 (lib_extends_trans ext br3) x) as pera0; simpl in *.
    pose proof (perb0 _ br2 lib'0 (lib_extends_trans ext br1) x) as perb0; simpl in *.
    eapply uniquely_valued_trans7; eauto.
  }

  {
    eapply eq_term_equals_trans;[exact pera1|].
    apply eq_term_equals_sym; eauto 3 with slow.
  }
Qed.
Hint Resolve type_transitive_per_bar : slow.

Lemma type_value_respecting_per_bar {o} :
  forall (ts : cts(o)),
    type_value_respecting ts
    -> type_value_respecting (per_bar ts).
Proof.
  introv resp per ceq.
  unfold per_bar in *; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply resp; eauto 3 with slow.
Qed.
Hint Resolve type_value_respecting_per_bar : slow.

Lemma term_symmetric_all_in_bar_ext_implies {o} :
  forall {lib : SL} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> term_symmetric ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv alla sym br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply sym; eauto.
Qed.

Lemma per_bar_eq_sym {o} :
  forall {lib : SL} (bar1 bar2 : @BarLib o lib) (eqa : lib-per(lib,o)) t1 t2,
    all_in_bar_ext bar1 (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> per_bar_eq bar2 eqa t1 t2
    -> per_bar_eq bar2 eqa t2 t1.
Proof.
  introv sym per; unfold per_bar_eq in *; introv br ext; introv.
  pose proof (per _ br _ ext x) as per; simpl in *; exrepnd.
  exists (intersect_bars bar' (raise_bar bar1 x)).
  introv br' ext'; introv; simpl in *; exrepnd.
  pose proof (per0 _ br'0 _ (lib_extends_trans ext' br'3) x0) as per0; simpl in *.
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
  allrw per1.
  apply term_symmetric_all_in_bar_ext_implies in per0; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_per_bar : slow.

Lemma term_transitive_all_in_bar_ext_implies {o} :
  forall {lib : SL} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> term_transitive ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv alla sym br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply sym; eauto.
Qed.

Lemma per_bar_eq_trans {o} :
  forall {lib : SL} (bar1 bar2 : @BarLib o lib) (eqa : lib-per(lib,o)) t1 t2 t3,
    all_in_bar_ext bar1 (fun lib' x => term_equality_transitive (eqa lib' x))
    -> per_bar_eq bar2 eqa t1 t2
    -> per_bar_eq bar2 eqa t2 t3
    -> per_bar_eq bar2 eqa t1 t3.
Proof.
  introv trans pera perb; unfold per_bar_eq in *; introv br ext; introv.
  pose proof (pera _ br _ ext x) as pera; simpl in *; exrepnd.
  pose proof (perb _ br _ ext x) as perb; simpl in *; exrepnd.
  exists (intersect3bars bar' bar'0 (raise_bar bar1 x)).
  introv br' ext'; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br'0 lib'2 (lib_extends_trans ext' br'3) x0) as pera0; simpl in *.
  pose proof (perb0 _ br'4 lib'2 (lib_extends_trans (lib_extends_trans ext' br'1) br'6) x0) as perb0; simpl in *.
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
  allrw per1.
  apply term_transitive_all_in_bar_ext_implies in per0; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_per_bar : slow.

Lemma term_value_respecting_all_in_bar_ext_implies {o} :
  forall {lib : SL} (bar : @BarLib o lib) ts T (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => ts lib' T T (eqa lib' x))
    -> term_value_respecting ts
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv alla val br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  eapply val; eauto.
Qed.

Lemma per_bar_eq_value_respecting {o} :
  forall {lib : SL} (bar1 bar2 : @BarLib o lib) (eqa : lib-per(lib,o)) t t',
    all_in_bar_ext bar1 (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> ccequivc_ext lib t t'
    -> per_bar_eq bar2 eqa t t
    -> per_bar_eq bar2 eqa t t'.
Proof.
  introv resp ceq pera; unfold per_bar_eq in *; introv br ext; introv.
  pose proof (pera _ br _ ext x) as pera; simpl in *; exrepnd.
  exists (intersect_bars bar' (raise_bar bar1 x)).
  introv br' ext'; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br'0 _ (lib_extends_trans ext' br'3) x0) as pera0; simpl in *.
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
  allrw per1.
  apply term_value_respecting_all_in_bar_ext_implies in per0; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_per_bar : slow.

Definition uniquely_valued2 {p} (ts : cts(p)) :=
  forall lib T T1 T2 eq eq',
    ts lib T T1 eq -> ts lib T T2 eq' -> eq <=2=> eq'.

Lemma uniquely_valued2_per_bar {o} :
  forall (ts : cts(o)),
    uniquely_valued2 ts
    -> uniquely_valued2 (per_bar ts).
Proof.
  introv uv p q.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear p1 q1.

  introv; split; introv h br ext; introv.

  - apply per_bar_eq_iff in h.
    unfold per_bar_eq_bi in h; exrepnd.
    exists (raise_bar (intersect_bars bar0 bar') x).
    introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (h0 lib1) as h0; autodimp h0 hyp; simpl in *.
    { simpl; eexists; eexists; dands; eauto. }
    pose proof (h0 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as h0; simpl in *.

    pose proof (p0 _ br'3 lib'2 (lib_extends_trans ext' (lib_extends_trans br'2 br'5)) (lib_extends_trans x0 x)) as p0; simpl in *.
    pose proof (q0 _ br lib'2 (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as q0; simpl in *.

    eapply uv in p0; autodimp p0 hyp;[exact q0|].
    apply p0; auto.

  - apply per_bar_eq_iff in h.
    unfold per_bar_eq_bi in h; exrepnd.
    exists (raise_bar (intersect_bars bar bar') x).
    introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (h0 lib1) as h0; autodimp h0 hyp; simpl in *.
    { simpl; eexists; eexists; dands; eauto. }
    pose proof (h0 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as h0; simpl in *.

    pose proof (p0 _ br lib'2 (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as p0; simpl in *.
    pose proof (q0 _ br'3 lib'2 (lib_extends_trans ext' (lib_extends_trans br'2 br'5)) (lib_extends_trans x0 x)) as q0; simpl in *.

    eapply uv in p0; autodimp p0 hyp;[exact q0|].
    apply p0; auto.
Qed.
Hint Resolve uniquely_valued2_per_bar : slow.
