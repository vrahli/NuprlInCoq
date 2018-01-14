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


Require Export bar_fam.
Require Export type_sys.
Require Export per_ceq_bar.
Require Export nuprl_mon.


Notation "bar-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib), lib-per(lib2,o)).

Lemma all_in_bar_ext2_exists_eqa_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    (forall lib1 (br : bar_lib_bar bar lib1)
            lib2 (ext : lib_extends lib2 lib1)
            (x : lib_extends lib2 lib),
        {eqa : lib-per(lib2,o) , F lib1 br lib2 ext x eqa})
    ->
    exists (feqa : bar-lib-per(lib,bar,o)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib1 br lib2 ext x (feqa lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => lib-per(plb_lib2 _ x,o))
                (fun x e => F (plb_lib1 _ x)
                              (plb_br _ x)
                              (plb_lib2 _ x)
                              (plb_ext _ x)
                              (plb_x _ x)
                              e)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

Definition local_ts {o} (ts : cts(o)) :=
  forall {lib} (bar : @BarLib o lib) T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

Definition lib_per_per_bar {o}
           {lib  : @library o}
           {bar  : BarLib lib}
           (fbar : bar_fam bar)
           (feqa : bar-lib-per(lib,bar,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) t1 t2 =>
            {lib1 : library
            , {br : bar_lib_bar bar lib1
            , {lib2 : library
            , {ext : lib_extends lib2 lib1
            , {x : lib_extends lib2 lib
            , {lib0 : library
            , {w : lib_extends lib' lib0
            , {fb : bar_lib_bar (fbar lib1 br lib2 ext x) lib0
            , feqa lib1 br lib2 ext x lib'
                   (lib_extends_trans
                      w
                      (bar_lib_ext (fbar lib1 br lib2 ext x) lib0 fb))
                   t1 t2}}}}}}}}).

  introv x y; introv.
  split; introv h; exrepnd.
  - exists lib1 br lib2 ext x0 lib0 w fb; auto.
  - exists lib1 br lib2 ext x0 lib0 w fb; auto.
Defined.

Definition sub_per_from_bar {o} {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) :=
  forall lib1 (br : bar_lib_bar bar lib1)
         lib2 (x1 : lib_extends lib2 lib1)
         (y1 : lib_extends lib2 lib)
         lib3 (x2 : lib_extends lib3 lib2)
         (y2 : lib_extends lib3 lib),
    sub_per (eqa lib2 y1) (eqa lib3 y2).

Lemma all_in_bar_ext_lib_per_implies_mon {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)),
    uniquely_valued ts
    -> type_monotone ts
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> sub_per_from_bar bar eqa.
Proof.
  introv uv mon alla br x1 x2 e.
  pose proof (alla _ br _ x1 y1) as h; simpl in *.
  pose proof (alla _ br _ (lib_extends_trans x2 x1) y2) as q; simpl in *.
  pose proof (mon lib2 lib3 T T' (eqa lib2 y1)) as w.
  repeat (autodimp w hyp).
  exrepnd.
  apply w0 in e; clear w0.
  eapply uv in q; autodimp q hyp;[exact w1|]; apply q; auto.
Qed.

Lemma uniquely_valued_per_bar {o} :
  forall (ts : cts(o)),
    uniquely_valued ts
    -> uniquely_valued (per_bar ts).
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
Hint Resolve uniquely_valued_per_bar : slow.

Definition local_unique {o} (ts : cts(o)) :=
  forall {lib} (bar : @BarLib o lib) T T' eq (eqa : lib-per(lib,o)),
    ts lib T T' eq
    -> all_in_bar_ext bar (fun lib' x => ts lib' T T' (eqa lib' x))
    -> sub_per (per_bar_eq bar eqa) eq.

Lemma close_local_unique {o} :
  forall (ts : cts(o)),
    local_unique ts
    -> local_unique (close ts).
Proof.
  introv loc cl.
  close_cases (induction cl using @close_ind') Case; introv alla.

  - Case "CL_init".
    rename_hyp_with eq tsts.

Abort.

Lemma local_unique_bar {o} :
  forall (ts : cts(o)) T T'
         {lib1} (b1 : @BarLib o lib1)
         {lib} (br : bar_lib_bar b1 lib)
         {lib2} (x : lib_extends lib2 lib) (b2 : @BarLib o lib2)
         (y : lib_extends lib2 lib1)
         (eqa1 : lib-per(lib1,o))
         (eqa2 : lib-per(lib2,o)),
    local_unique ts
    -> uniquely_valued ts
    -> type_monotone ts
    -> all_in_bar_ext b1 (fun lib' x => ts lib' T T' (eqa1 lib' x))
    -> all_in_bar_ext b2 (fun lib' x => ts lib' T T' (eqa2 lib' x))
    -> (eqa1 lib2 y) <=2=> (per_bar_eq b2 eqa2).
Proof.
  introv br y loc uv mon alla allb.
  applydup @all_in_bar_ext_lib_per_implies_mon in alla as sub; auto.
  introv; split; intro h.

  - apply per_bar_eq_iff.
    exists b2.
    introv br' ext'; introv; simpl in *; exrepnd.

    assert (lib_extends lib'0 lib) as x1 by eauto 3 with slow.
    assert (lib_extends lib'0 lib1) as x2 by eauto 3 with slow.
    assert (lib_extends lib'0 lib0) as x3 by eauto 3 with slow.

    pose proof (alla _ br lib'0 x1 x2) as q; simpl in *.
    pose proof (allb _ br'0 lib'0 x3 x) as w; simpl in *.
    eapply uv in w; autodimp w hyp;[exact q|]; clear q.
    apply w; clear w.
    eapply sub;try exact h; eauto.

  - eapply loc in h;[eauto| |exact allb].
    eapply alla; eauto 3 with slow.
Qed.

Lemma eq_term_equals_per_bar_eq_bar_of_bar_fam {o} :
  forall {lib} (bar : @BarLib o lib) (fbar : bar_fam bar) (eqa : lib-per(lib,o)),
    (per_bar_eq bar eqa) <=2=> (per_bar_eq (bar_of_bar_fam fbar) eqa).
Proof.
  introv.
  unfold per_bar_eq; split; introv h; exrepnd.

  - introv br ext; introv; simpl in *; exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.

    assert (lib_extends lib'0 lib1) as x1 by eauto 4 with slow.

    pose proof (h lib1 br lib'0 x1 x) as h; simpl in *.
    exrepnd.

    exists bar'.
    introv br' ext'; introv.

    pose proof (h0 _ br' _ ext' x2) as h0; simpl in *; auto.

  - introv br ext; introv.

    apply all_in_bar_ext_exists_bar_implies in h; exrepnd.
    exists (raise_bar (bar_of_bar_fam fbar0) x).
    introv br' ext'; introv; simpl in *.

    destruct br' as [lib'' br']; repnd.
    destruct br'0 as [lib1' br'0].
    destruct br'0 as [br'' br'0].
    destruct br'0 as [lib2' br'0].
    destruct br'0 as [ext'' br'0].
    destruct br'0 as [x'' br'0].

    assert (lib_extends lib'2 lib'') as xt1 by eauto 3 with slow.
    assert (lib_extends lib'2 lib2') as xt2 by eauto 3 with slow.

    pose proof (h0 _ br'' lib2' ext'' x'' lib'' br'0 lib'2 xt1 xt2) as h0; simpl in *.
    eapply (lib_per_cond _ eqa); eauto.
Qed.
Hint Resolve eq_term_equals_per_bar_eq_bar_of_bar_fam : slow.

Definition per_bar_eq2 {o}
           {lib}
           (bar : @BarLib o lib)
           (eqa : lib-per(lib,o))
           (t1 t2 : CTerm) :=
  {bar0 : BarLib lib
  , all_in_bar_ext
      (intersect_bars bar bar0)
      (fun lib' (x : lib_extends lib' lib) =>
         {bar' : BarLib lib'
         , all_in_bar_ext
             bar' (fun lib'' (y : lib_extends lib'' lib') =>
                     eqa lib'' (lib_extends_trans y x) t1 t2) })}.

Lemma all_in_bar_ext_intersect_bars_same {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar bar) F
    <=> all_in_bar_ext bar F.
Proof.
  introv; split; introv h br ext; introv; simpl in *.

  - pose proof (h lib') as h; simpl in h; autodimp h hyp.
    eexists; eexists; dands; eauto 3 with slow.

  - exrepnd.
    eapply (h _ br0 lib'0); eauto 3 with slow.
Qed.

Lemma per_bar_eq_iff2 {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) t1 t2,
    per_bar_eq bar eqa t1 t2
    <=> per_bar_eq2 bar eqa t1 t2.
Proof.
  introv; unfold per_bar_eq, per_bar_eq2; split; introv h.

  - exists bar.
    apply all_in_bar_ext_intersect_bars_same; auto.

  - exrepnd.
    introv br ext; introv.
    apply all_in_bar_ext_exists_bar_implies in h0; simpl in *; exrepnd.
    exists (raise_bar (bar_of_bar_fam fbar) x).
    introv br' ext'; introv; simpl in *.

    destruct br' as [lib'' br']; repnd.
    destruct br'0 as [lib1' br'0].
    destruct br'0 as [br'' br'0].
    destruct br'0 as [lib2' br'0].
    destruct br'0 as [ext'' br'0].
    destruct br'0 as [x'' br'0].

    assert (lib_extends lib'2 lib'') as xt1 by eauto 3 with slow.
    assert (lib_extends lib'2 lib2') as xt2 by eauto 3 with slow.
    pose proof (h1 _ br'' _ ext'' x'' _ br'0 lib'2 xt1 xt2) as h1; simpl in *.
    eapply (lib_per_cond _ eqa); eauto.
Qed.

Lemma local_per_bar {o} :
  forall (ts : cts(o)),
    type_extensionality ts
    -> uniquely_valued ts
    -> local_ts (per_bar ts).
Proof.
  introv text uv eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).

  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.
  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext b lib' br0)))
      as alla2; simpl in *.

    eapply text;[eauto|].

    introv; split; introv w.

    { subst.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    eapply uv in z0; autodimp z0 hyp;[exact alla2|].
    apply z0; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear eqiff.

    introv; split; intro h.

    - rw @per_bar_eq_iff in h; unfold per_bar_eq_bi in *; exrepnd.
      apply per_bar_eq_iff2.
      exists bar'.
      introv br ext; introv; simpl in *; exrepnd.
      pose proof (h0 lib') as h0; simpl in *; autodimp h0 hyp.
      { eexists; eexists; dands; eauto 4 with slow. }
      pose proof (h0 _ ext x) as h0; simpl in *.

      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.

      pose proof (alla1 _ br lib'0 xt1 x) as allb; repnd.
      apply allb in h0.
      rw @per_bar_eq_iff in h0; unfold per_bar_eq_bi in *; exrepnd.

      exists (intersect_bars (fbar lib0 br lib'0 xt1 x) bar'0).
      introv br' ext' x'.
      pose proof (h1 _ br' _ ext' x') as h1; simpl in h1.
      simpl in *; exrepnd.

      exists lib0 br lib'0 xt1 x lib4 (lib_extends_trans ext' br'3) br'0.
      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      eapply (lib_per_cond _ eqb); eauto.

    - rw @per_bar_eq_iff.
      exists (bar_of_bar_fam fbar).
      introv br ext; introv; simpl in *; exrepnd.
      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.
      pose proof (alla1 _ br lib'0 xt1 x) as allb; simpl in *; repnd.
      apply allb; clear allb.

      introv br' ext'; introv.
      pose proof (h lib'1) as h; simpl in *; autodimp h hyp.
      { eexists; eexists; eexists; eexists; eexists; eauto. }
      assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.
      pose proof (h lib'2 ext' xt2) as h; simpl in h; exrepnd.
      exists bar'.

      introv br'' ext''; introv.
      pose proof (h0 _ br'' _ ext'' x2) as h0; simpl in *; exrepnd.

      assert (lib_extends lib'4 lib'1) as xt3 by eauto 3 with slow.
      assert (lib_extends lib'4 lib'0) as xt4 by eauto 3 with slow.
      pose proof (allb0 _ br' lib'4 xt3 xt4) as allb0; simpl in *.

      pose proof (alla1 _ br2 _ ext1 x3) as q; repnd.
      assert (lib_extends lib'4 lib5) as xt5 by eauto 3 with slow.
      pose proof (q0 _ fb _ w xt5) as q0; simpl in *.
      eapply uv in q0; autodimp q0 hyp;[exact allb0|].

      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqc.
      eapply (lib_per_cond _ eqb); apply q0.
      eapply (lib_per_cond _ eqc); apply h0.
  }
Qed.
Hint Resolve local_per_bar : slow.

Lemma local_per_bar2 {o} :
  forall (ts : cts(o)),
    type_extensionality ts
    -> uniquely_valued ts
    -> local_unique ts
    -> type_monotone ts
    -> local_ts (per_bar ts).
Proof.
  introv text uv loc mon eqiff alla.

  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  exists eqa.
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    assert (lib_extends lib'0 lib1) as xt1 by eauto 4 with slow.
    assert (lib_extends lib'0 lib2) as xt2 by eauto 3 with slow.

    pose proof (alla0 lib1 br lib2 ext0 x0) as allb.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b1.

    assert (lib_extends lib'0 lib1) as x1 by eauto 4 with slow.

    pose proof (alla0 _ br _ x1 x) as allc.
    exrepnd.
    remember (fbar lib1 br lib'0 x1 x) as b2.

    pose proof (local_unique_bar ts T T' b1 br0 ext b2 xt2 eqa0 eqa1) as h.
    repeat (autodimp h hyp).
    eapply text;[|apply eq_term_equals_sym;exact allc0].
    eapply text;[|exact h].
    eapply allb1; eauto 3 with slow.
  }

  {
    clear text uv loc mon alla0.
    eapply eq_term_equals_trans;[eauto|]; clear eqiff.
    apply eq_term_equals_per_bar_eq_bar_of_bar_fam.
  }
Qed.

Lemma uniquely_valued_univi {o} :
  forall i, @uniquely_valued o (univi i).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd.
  spcast; computes_to_eqval.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve uniquely_valued_univi : slow.

Lemma uniquely_valued_univ_ex {o} : @uniquely_valued o univ_ex.
Proof.
  introv u v.
  unfold univ_ex in *; exrepnd.

  eapply uni_in_higher_univ in u0.
  eapply uni_in_higher_univ_r in v0.
  eapply uniquely_valued_univi in v0; autodimp v0 hyp;[exact u0|].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve uniquely_valued_univ_ex : slow.

Lemma local_univi_bar {o} :
  forall i, @local_ts o (univi_bar i).
Proof.
  introv eqiff alla.
  eapply local_per_bar in alla; eauto 3 with slow.
Qed.
Hint Resolve local_univi_bar : slow.

Lemma local_univ {o} : @local_ts o univ.
Proof.
  introv eqiff alla.
  eapply local_per_bar; eauto; eauto 3 with slow.
Qed.
Hint Resolve local_univ : slow.
