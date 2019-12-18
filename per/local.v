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


(*Notation "bar-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1)
          (x : lib_extends lib2 lib), lib-per(lib2,o)).*)

(*Lemma all_in_bar_ext2_exists_eqa_implies {o} :
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
Qed.*)

Definition local_ts {o} inh (ts : cts(o)) :=
  forall (lib : @library o) T T' eq eqa,
    (eq <=2=> (per_bar_eq inh lib eqa))
    -> in_open_bar_ext inh lib (fun lib' x => ts lib' T T' (eqa lib' x))
    -> ts lib T T' eq.

(*Definition lib_per_per_bar {o}
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
  introv; tcsp.
Defined.*)

(*Definition sub_per_from_bar {o} {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) :=
  forall lib1 (br : bar_lib_bar bar lib1)
         lib2 (x1 : lib_extends lib2 lib1)
         (y1 : lib_extends lib2 lib)
         lib3 (x2 : lib_extends lib3 lib2)
         (y2 : lib_extends lib3 lib),
    sub_per (eqa lib2 y1) (eqa lib3 y2).*)

(*Lemma all_in_bar_ext_lib_per_implies_mon {o} :
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
Qed.*)

Lemma uniquely_valued_per_bar {o} :
  forall inh (ts : cts(o)),
    uniquely_valued ts
    -> uniquely_valued (per_bar inh ts).
Proof.
  introv uv p q.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear p0 q0.

  unfold per_bar_eq; introv; split; introv h.

  { eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact q1]; clear q1.
    eapply in_open_bar_ext_comb;[|exact p1]; clear p1.
    apply in_ext_ext_implies_in_open_bar_ext; introv h q z.
    eapply uv in h; autodimp h hyp; try exact q.
    apply h; auto. }

  { eapply in_open_bar_ext_comb;[|exact h]; clear h.
    eapply in_open_bar_ext_comb;[|exact q1]; clear q1.
    eapply in_open_bar_ext_comb;[|exact p1]; clear p1.
    apply in_ext_ext_implies_in_open_bar_ext; introv h q z.
    eapply uv in h; autodimp h hyp; try exact q.
    apply h; auto. }
Qed.
Hint Resolve uniquely_valued_per_bar : slow.

Definition local_unique {o} (ts : cts(o)) :=
  forall inh (lib : @library o) T T' eq (eqa : lib-per(inh,lib,o)),
    ts lib T T' eq
    -> in_open_bar_ext inh lib (fun lib' x => ts lib' T T' (eqa lib' x))
    -> sub_per (per_bar_eq inh lib eqa) eq.

Lemma close_local_unique {o} :
  forall inh (ts : cts(o)),
    local_unique ts
    -> local_unique (close inh ts).
Proof.
  introv loc cl.
  close_cases (induction cl using @close_ind') Case; introv alla.

  - Case "CL_init".
    rename_hyp_with eq tsts.

Abort.

(*Lemma local_unique_bar {o} :
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
Qed.*)

(*Lemma eq_term_equals_per_bar_eq_bar_of_bar_fam {o} :
  forall {lib} (bar : @BarLib o lib) (fbar : bar_fam bar) (eqa : lib-per(lib,o)),
    (per_bar_eq lib eqa) <=2=> (per_bar_eq (bar_of_bar_fam fbar) eqa).
Proof.
  introv.
  unfold per_bar_eq; split; introv h; exrepnd.

  { apply e_all_in_bar_ext_as in h.
    apply e_all_in_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv ext; tcsp. }

  { apply e_all_in_bar_ext_as in h.
    apply e_all_in_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv ext; tcsp. }
Qed.
Hint Resolve eq_term_equals_per_bar_eq_bar_of_bar_fam : slow.*)

(*Definition per_bar_eq2 {o}
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
                     eqa lib'' (lib_extends_trans y x) t1 t2) })}.*)

(*Lemma all_in_bar_ext_intersect_bars_same {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars bar bar) F
    <=> all_in_bar_ext bar F.
Proof.
  introv; split; introv h br ext; introv; simpl in *.

  - pose proof (h lib') as h; simpl in h; autodimp h hyp.
    eexists; eexists; dands; eauto 3 with slow.

  - exrepnd.
    eapply (h _ br0 lib'0); eauto 3 with slow.
Qed.*)

(*Lemma per_bar_eq_iff2 {o} :
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
Qed.*)

Record LibExt {o} inh (lib : @library o) :=
  MkLibExt
    {
      lib_ext_lib :> @library o;
      lib_ext_ext : lib_extends inh lib_ext_lib lib;
    }.
Arguments MkLibExt [o] [inh] [lib] _ _.
Arguments lib_ext_lib [o] [inh] [lib] _.
Arguments lib_ext_ext [o] [inh] [lib] _.

Definition FunLibExt {o} inh (lib : @library o) :=
  forall lib' (x : lib_extends inh lib' lib), LibExt inh lib'.

Definition FunLibExtProp {o} inh (lib : @library o) :=
  forall lib' (x : lib_extends inh lib' lib), Prop.

Lemma in_open_bar_ext_choice {o} :
  forall inh (lib : @library o) (F : FunLibExtProp inh lib),
    in_open_bar_ext inh lib F
    -> exists (Flib : FunLibExt inh lib),
      in_ext_ext
        inh lib
        (fun lib' x =>
           in_ext_ext inh (Flib lib' x) (fun lib0 x0 => forall (z : lib_extends inh lib0 lib), F lib0 z)).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (LibExt inh lib)
                (LibExt inh)
                (fun le1 le2 =>
                   in_ext_ext inh le2 (fun lib0 x0 => forall (z : lib_extends inh lib0 lib), F lib0 z))) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x as [lib' ext'].
    pose proof (h lib' ext') as h; exrepnd.
    exists (MkLibExt lib'' y); simpl; auto. }

  exrepnd.
  exists (fun lib' ext' => f (MkLibExt lib' ext')).
  introv.
  apply (C0 (MkLibExt lib' e)).
Qed.

Record DepLibExt {o} inh (lib : @library o) (F : FunLibExt inh lib) :=
  MkDepLibExt
    {
      lib_ext_lib1 :> @library o;
      lib_ext_ext1 : lib_extends inh lib_ext_lib1 lib;
      lib_ext_lib2 : @library o;
      lib_ext_ext2 : lib_extends inh lib_ext_lib2 (F lib_ext_lib1 lib_ext_ext1);
      lib_ext_extz : lib_extends inh lib_ext_lib2 lib;
    }.
Arguments MkDepLibExt  [o] [inh] [lib] [F] _ _ _ _ _.
Arguments lib_ext_lib1 [o] [inh] [lib] [F] _.
Arguments lib_ext_ext1 [o] [inh] [lib] [F] _.
Arguments lib_ext_lib2 [o] [inh] [lib] [F] _.
Arguments lib_ext_ext2 [o] [inh] [lib] [F] _.
Arguments lib_ext_extz [o] [inh] [lib] [F] _.

Definition FunDepEqa {o} {inh} {lib} (F : @FunLibExt o inh lib) :=
  forall lib1 (ext1 : lib_extends inh lib1 lib)
         lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1))
         (z : lib_extends inh lib2 lib),
    lib-per(inh,lib2,o).

Lemma in_open_bar_eqa_choice {o} :
  forall inh (lib : @library o)
         (F : FunLibExt inh lib)
         (G : forall lib1 (ext1 : lib_extends inh lib1 lib) lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1)) (z : lib_extends inh lib2 lib) (eqa : lib-per(inh,lib2,o)), Prop),
    in_ext_ext
      inh lib
      (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
         in_ext_ext
           inh
           (F lib1 ext1)
           (fun lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1)) =>
              forall (z : lib_extends inh lib2 lib),
              exists (eqa : lib-per(inh,lib2,o)),
                G lib1 ext1 lib2 ext2 z eqa))
    -> exists (Feqa : FunDepEqa F),
      in_ext_ext
        inh lib
        (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
           in_ext_ext
             inh
             (F lib1 ext1)
             (fun lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1)) =>
                forall (z : lib_extends inh lib2 lib),
                  G lib1 ext1 lib2 ext2 z (Feqa lib1 ext1 lib2 ext2 z))).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (DepLibExt inh lib F)
                (fun d => lib-per(inh,lib_ext_lib2 d,o))
                (fun d eqa =>
                   G (lib_ext_lib1 d) (lib_ext_ext1 d) (lib_ext_lib2 d) (lib_ext_ext2 d) (lib_ext_extz d) eqa)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x as [lib1 ext1 lib2 ext2 extz]; simpl in *.
    pose proof (h lib1 ext1 lib2 ext2 extz) as h; exrepnd.
    exists eqa; auto. }

  exrepnd.
  exists (fun lib1 ext1 lib2 ext2 z => f (MkDepLibExt lib1 ext1 lib2 ext2 z)).
  repeat introv.
  apply (C0 (MkDepLibExt lib' e lib'0 e0 z)).
Qed.

Definition FunLibExt2 {o} {inh} {lib} (F : @FunLibExt o inh lib) :=
  forall lib1 (ext1 : lib_extends inh lib1 lib)
         lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1))
         (z : lib_extends inh lib2 lib),
    FunLibExt inh lib2.

Definition FunLibExtProp2 {o} {inh} {lib} (F : @FunLibExt o inh lib) :=
  forall lib1 (ext1 : lib_extends inh lib1 lib)
         lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1))
         (z : lib_extends inh lib2 lib),
    FunLibExtProp inh lib2.

Definition FunLibExtProp1 {o} {inh} {lib} (F : @FunLibExt o inh lib) :=
  forall lib1 (ext1 : lib_extends inh lib1 lib)
         lib2 (ext2 : lib_extends inh lib2 (F lib1 ext1))
         (z : lib_extends inh lib2 lib), Prop.

Record DepLibExt2 {o} inh (lib : @library o) (F : FunLibExt inh lib) :=
  MkDepLibExt2
    {
      lib_ext2_lib1 :> @library o;
      lib_ext2_ext1 : lib_extends inh lib_ext2_lib1 lib;
      lib_ext2_lib2 : @library o;
      lib_ext2_ext2 : lib_extends inh lib_ext2_lib2 (F lib_ext2_lib1 lib_ext2_ext1);
      lib_ext2_extz : lib_extends inh lib_ext2_lib2 lib;
      lib_ext2_lib3 : @library o;
      lib_ext2_ext3 : lib_extends inh lib_ext2_lib3 lib_ext2_lib2;
    }.
Arguments MkDepLibExt2  [o] [inh] [lib] [F] _ _ _ _ _.
Arguments lib_ext2_lib1 [o] [inh] [lib] [F] _.
Arguments lib_ext2_ext1 [o] [inh] [lib] [F] _.
Arguments lib_ext2_lib2 [o] [inh] [lib] [F] _.
Arguments lib_ext2_ext2 [o] [inh] [lib] [F] _.
Arguments lib_ext2_extz [o] [inh] [lib] [F] _.
Arguments lib_ext2_lib3 [o] [inh] [lib] [F] _.
Arguments lib_ext2_ext3 [o] [inh] [lib] [F] _.

Lemma in_open_data_open_choice {o} :
  forall inh (lib  : @library o)
         (Flib : FunLibExt inh lib)
         (F : FunLibExtProp2 Flib)
         (G : FunLibExtProp1 Flib),
    in_ext_ext
      inh lib
      (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
         in_ext_ext
           inh
           (Flib lib1 ext1)
           (fun lib2 (ext2 : lib_extends inh lib2 (Flib lib1 ext1)) =>
              forall (z : lib_extends inh lib2 lib),
                in_open_bar_ext inh lib2 (F lib1 ext1 lib2 ext2 z)
                # G lib1 ext1 lib2 ext2 z))
    -> exists (Flib2 : FunLibExt2 Flib),
      in_ext_ext
        inh lib
        (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
           in_ext_ext
             inh (Flib lib1 ext1)
             (fun lib2 (ext2 : lib_extends inh lib2 (Flib lib1 ext1)) =>
                forall (z : lib_extends inh lib2 lib),
                  in_ext_ext
                    inh lib2
                    (fun lib' (x : lib_extends inh lib' lib2) =>
                       in_ext_ext
                         inh (Flib2 lib1 ext1 lib2 ext2 z lib' x)
                         (fun lib0 x0 =>
                            forall (w : lib_extends inh lib0 lib2),
                              F lib1 ext1 lib2 ext2 z lib0 w))
                  # G lib1 ext1 lib2 ext2 z)).
Proof.
  introv h.

  pose proof (DependentFunctionalChoice_on
                (DepLibExt2 inh lib Flib)
                (fun d => LibExt inh (lib_ext2_lib3 d))
                (fun d e =>
                   in_ext_ext
                     inh e
                     (fun lib0 x0 =>
                        forall (z : lib_extends inh lib0 (lib_ext2_lib2 d)),
                          F (lib_ext2_lib1 d)
                            (lib_ext2_ext1 d)
                            (lib_ext2_lib2 d)
                            (lib_ext2_ext2 d)
                            (lib_ext2_extz d)
                            lib0 z))) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x as [lib1 ext1 lib2 ext2 extz lib3 ext3]; simpl in *.
    pose proof (h lib1 ext1 lib2 ext2 extz) as h; exrepnd.
    pose proof (h0 lib3 ext3) as h0; exrepnd.
    exists (MkLibExt lib'' y); auto. }

  exrepnd.
  exists (fun lib1 ext1 lib2 ext2 z lib3 ext3 => f (MkDepLibExt2 lib1 ext1 lib2 ext2 z lib3 ext3)).
  repeat introv.
  pose proof (h lib' e lib'0 e0 z) as w; simpl in *; repnd; dands; auto.
  introv.
  apply (C0 (MkDepLibExt2 lib' e lib'0 e0 z lib'1 e1)).
Qed.

Definition lib_fun_dep_eqa {o}
           {inh}
           {lib   : @library o}
           {Flib  : FunLibExt inh lib}
           (Feqa  : FunDepEqa Flib)
           (Flib2 : FunLibExt2 Flib)
  : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) t1 t2 =>
            {lib1 : library
            , {ext1 : lib_extends inh lib1 lib
            , {lib2 : library
            , {ext2 : lib_extends inh lib2 (Flib lib1 ext1)
            , {extz : lib_extends inh lib2 lib
            , {lib3 : library
            , {ext3 : lib_extends inh lib3 lib2
            , {lib4 : library
            , {ext4 : lib_extends inh lib4 (Flib2 lib1 ext1 lib2 ext2 extz lib3 ext3)
            , {z : lib_extends inh lib' lib2
            , {w : lib_extends inh lib' lib4
            , Feqa lib1 ext1 lib2 ext2 extz lib' z t1 t2 }}}}}}}}}}} ).
  introv; tcsp.
Defined.

Lemma lib_extends_Flib {o} :
  forall inh lib lib' (Flib : @FunLibExt o inh lib) (ext : lib_extends inh lib' lib),
    lib_extends inh (Flib lib' ext) lib'.
Proof.
  introv.
  apply (lib_ext_ext (Flib lib' ext)).
Qed.
Hint Resolve lib_extends_Flib : slow.

Lemma lib_extends_Flib2 {o} :
  forall inh lib (Flib : @FunLibExt o inh lib) (Flib2 : FunLibExt2 Flib)
         lib1 ext1 lib2 ext2 extz lib3 ext3,
    lib_extends inh (Flib2 lib1 ext1 lib2 ext2 extz lib3 ext3) lib3.
Proof.
  introv.
  apply (lib_ext_ext (Flib2 lib1 ext1 lib2 ext2 extz lib3 ext3)).
Qed.
Hint Resolve lib_extends_Flib2 : slow.

Lemma eq_per_bar_eq_lib_fun_dep_eqa_part1 {o} :
  forall inh (ts : cts(o)) T T' lib (eqa : lib-per(inh,lib, o))
         (Flib  : FunLibExt inh lib)
         (Feqa  : FunDepEqa Flib)
         (Flib2 : FunLibExt2 Flib)
         t1 t2,
    in_ext_ext
      inh lib
      (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
         in_ext_ext
           inh (Flib lib1 ext1)
           (fun lib2 (ext2 : lib_extends inh lib2 (Flib lib1 ext1)) =>
              forall (z : lib_extends inh lib2 lib),
                in_ext_ext
                  inh lib2
                  (fun lib' (x : lib_extends inh lib' lib2) =>
                     in_ext_ext
                       inh (Flib2 lib1 ext1 lib2 ext2 z lib' x)
                       (fun lib0 (_ : lib_extends inh lib0 (Flib2 lib1 ext1 lib2 ext2 z lib' x)) =>
                          forall w : lib_extends inh lib0 lib2,
                            ts lib0 T T' ((Feqa lib1 ext1 lib2 ext2 z) lib0 w)))
                  # (eqa lib2 z) <=2=> (per_bar_eq inh lib2 (Feqa lib1 ext1 lib2 ext2 z))))
    -> per_bar_eq inh lib eqa t1 t2
    -> per_bar_eq inh lib (lib_fun_dep_eqa Feqa Flib2) t1 t2.
Proof.
  introv imp h ext.
  unfold per_bar_eq in *.
  pose proof (imp _ ext) as imp; simpl in *.
  pose proof (h (Flib lib' ext) (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)) as h; exrepnd; simpl in *.
  apply in_ext_ext_implies in h1.
  pose proof (h1 (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))) as h1.
  pose proof (imp _ y (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))) as imp; simpl in *; repnd.
  apply imp in h1.
  pose proof (h1 _ (lib_ext_ext
                      (Flib2
                         lib' ext lib'' y
                         (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
                         lib''
                         (lib_extends_refl inh lib'')))) as h1.
  exrepnd.

  exists lib''0 (lib_extends_trans
                   y0
                   (lib_extends_trans
                      (lib_ext_ext
                         (Flib2
                            lib' ext lib'' y
                            (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
                            lib''
                            (lib_extends_refl inh lib'')))
                      (lib_extends_trans y (lib_ext_ext (Flib lib' ext))))).
  introv xta xtb.
  exists lib' ext lib'' y
         (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
         lib''
         (lib_extends_refl inh lib'')
         (Flib2
            lib' ext lib'' y
            (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
            lib''
            (lib_extends_refl inh lib''))
         (lib_extends_refl
            inh
            (Flib2
               lib' ext lib'' y
               (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
               lib''
               (lib_extends_refl inh lib''))).
  exists (lib_extends_trans
            xta
            (lib_extends_trans
               y0
               (lib_ext_ext
                  (Flib2
                     lib' ext lib'' y
                     (lib_extends_trans y (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext))
                     lib''
                     (lib_extends_refl inh lib''))))).
  exists (lib_extends_trans xta y0).
  introv.
  apply h1; eauto 2 with slow.
Qed.

Lemma eq_per_bar_eq_lib_fun_dep_eqa {o} :
  forall inh (ts : cts(o)) T T' lib (eqa : lib-per(inh,lib, o))
         (Flib  : FunLibExt inh lib)
         (Feqa  : FunDepEqa Flib)
         (Flib2 : FunLibExt2 Flib),
    uniquely_valued ts
    -> in_ext_ext
         inh lib
         (fun lib1 (ext1 : lib_extends inh lib1 lib) =>
            in_ext_ext
              inh (Flib lib1 ext1)
              (fun lib2 (ext2 : lib_extends inh lib2 (Flib lib1 ext1)) =>
                 forall (z : lib_extends inh lib2 lib),
                   in_ext_ext
                     inh lib2
                     (fun lib' (x : lib_extends inh lib' lib2) =>
                        in_ext_ext
                          inh (Flib2 lib1 ext1 lib2 ext2 z lib' x)
                          (fun lib0 (_ : lib_extends inh lib0 (Flib2 lib1 ext1 lib2 ext2 z lib' x)) =>
                             forall w : lib_extends inh lib0 lib2,
                               ts lib0 T T' ((Feqa lib1 ext1 lib2 ext2 z) lib0 w)))
                     # (eqa lib2 z) <=2=> (per_bar_eq inh lib2 (Feqa lib1 ext1 lib2 ext2 z))))
    -> (per_bar_eq inh lib eqa) <=2=> (per_bar_eq inh lib (lib_fun_dep_eqa Feqa Flib2)).
Proof.
  introv unival imp; repeat introv; split; intro h.

  { eapply eq_per_bar_eq_lib_fun_dep_eqa_part1; eauto. }

  unfold per_bar_eq in *.
  introv ext; simpl in *.

  pose proof (h (Flib lib' ext)) as h; exrepnd; simpl in *.
  autodimp h hyp; eauto 3 with slow;[]; exrepnd.

  assert (lib_extends inh lib'' lib') as xta by eauto 3 with slow.
  exists lib'' xta; introv xtb; introv.

  assert (lib_extends inh lib'' lib) as xtc by eauto 3 with slow.
  pose proof (imp _ ext lib'0 (lib_extends_trans xtb y) z) as imp'; simpl in *; repnd.
  apply imp'; clear imp'.
  introv xtd.

  exists (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd).
  exists (lib_ext_ext (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd)).
  introv xte; introv.

  pose proof (h1 lib'2) as h1; simpl in *.
  repeat (autodimp h1 hyp); eauto 3 with slow.
  exrepnd.

  pose proof (imp'0 lib'1 xtd _ xte z0) as imp'0; simpl in *.

  pose proof (imp lib1 ext1 lib2 ext2 extz) as imp; simpl in *; repnd; clear imp.
  pose proof (imp0 lib3 ext3 lib'2 (lib_extends_trans w ext4) z1) as imp0; simpl in *.
  eapply unival in imp0; autodimp imp0 hyp; try exact imp'0.
  apply imp0; auto.
Qed.

Lemma local_per_bar {o} :
  forall inh (ts : cts(o)),
    type_extensionality ts
    -> uniquely_valued ts
    -> local_ts inh (per_bar inh ts).
Proof.
  introv text uv eqiff alla.
  unfold per_bar in *.

  apply in_open_bar_ext_choice in alla; exrepnd.
  apply in_open_bar_eqa_choice in alla0; exrepnd.
  apply in_open_data_open_choice in alla1; exrepnd.
  exists (lib_fun_dep_eqa Feqa Flib2).
  dands;
    [|eapply eq_term_equals_trans;[exact eqiff|];clear eqiff;
      eapply eq_per_bar_eq_lib_fun_dep_eqa; eauto];[].

  introv ext.
  pose proof (alla0 _ ext) as alla1; simpl in *.
  apply in_ext_ext_implies in alla1.
  pose proof (alla1 (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)) as alla1; repnd.
  pose proof (alla2 _ (lib_extends_refl _ _)) as alla2; simpl in *.

  assert (lib_extends
            _
            (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                   (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                   (lib_extends_refl _ (Flib lib' ext))) lib') as xta by eauto 3 with slow.

  exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                (lib_extends_refl _ (Flib lib' ext))) xta.
  introv xtb xtc.
  assert (lib_extends inh lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
  pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

  eapply text;[eauto|].

  introv; split; introv w.

  { exists lib' ext (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext))
           (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
           (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext)).
    exists lib'0 xtb.
    exists xtd (lib_extends_refl inh lib'0); auto. }

  exrepnd.

  pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
  assert (lib_extends inh lib4 lib2) as xte by eauto 3 with slow.
  pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.
  eapply uv in xx0; autodimp xx0 hyp;[exact alla2|].
  apply xx0; auto.
Qed.
Hint Resolve local_per_bar : slow.

(*Lemma local_per_bar2 {o} :
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

    assert (lib_extends inh lib'0 lib1) as xt1 by eauto 4 with slow.
    assert (lib_extends inh lib'0 lib2) as xt2 by eauto 3 with slow.

    pose proof (alla0 lib1 br lib2 ext0 x0) as allb.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b1.

    assert (lib_extends inh lib'0 lib1) as x1 by eauto 4 with slow.

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
Qed.*)

Lemma ccequivc_ext_uni_uni_implies {o} :
  forall inh (lib : @library o) i j,
    ccequivc_ext inh lib (mkc_uni i) (mkc_uni j) -> i = j.
Proof.
  introv ceq; pose proof (ceq _ (lib_extends_refl _ _)) as ceq; simpl in ceq; spcast.
  apply cequivc_uni_right_iscvalue in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma uniquely_valued_univi {o} :
  forall inh uni i, @uniquely_valued o (univi i inh uni).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd.
  spcast; computes_to_eqval_ext.
  apply ccequivc_ext_uni_uni_implies in ceq; subst; GC.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve uniquely_valued_univi : slow.

Lemma uniquely_valued_univi_ex {o} inh uni : @uniquely_valued o (univi_ex inh uni).
Proof.
  introv u v.
  unfold univi_ex in *; exrepnd.

  eapply uni_in_higher_univ in u0.
  eapply uni_in_higher_univ_r in v0.
  eapply uniquely_valued_univi in v0; autodimp v0 hyp;[exact u0|].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve uniquely_valued_univi_ex : slow.

Lemma uniquely_valued_univi_ex_bar {o} inh uni : @uniquely_valued o (univi_ex_bar inh uni).
Proof.
  introv u v.
  unfold univi_ex_bar in *; exrepnd.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[exact u0|]; clear u0.
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;exact v0]; clear v0.
  clear dependent eq.
  clear dependent eq'.

  introv; split; intro h; introv ext; unfold per_bar_eq in *.

  { pose proof (u1 _ ext) as u1; exrepnd.
    pose proof (v1 _ (lib_extends_trans y ext)) as v1; exrepnd.
    pose proof (h _ (lib_extends_trans y0 (lib_extends_trans y ext))) as h; exrepnd.
    exists lib''1 (lib_extends_trans y1 (lib_extends_trans y0 y)).
    introv xt; introv.
    pose proof (h1 _ xt z) as h1; simpl in h1.
    pose proof (v1 _ (lib_extends_trans xt y1) z) as v1; simpl in v1.
    pose proof (u1 _ (lib_extends_trans xt (lib_extends_trans y1 y0)) z) as u1; simpl in u1.
    eapply uniquely_valued_univi_ex;[exact v1|exact u1|]; auto. }

  { pose proof (u1 _ ext) as u1; exrepnd.
    pose proof (v1 _ (lib_extends_trans y ext)) as v1; exrepnd.
    pose proof (h _ (lib_extends_trans y0 (lib_extends_trans y ext))) as h; exrepnd.
    exists lib''1 (lib_extends_trans y1 (lib_extends_trans y0 y)).
    introv xt; introv.
    pose proof (h1 _ xt z) as h1; simpl in h1.
    pose proof (v1 _ (lib_extends_trans xt y1) z) as v1; simpl in v1.
    pose proof (u1 _ (lib_extends_trans xt (lib_extends_trans y1 y0)) z) as u1; simpl in u1.
    eapply uniquely_valued_univi_ex;[exact u1|exact v1|]; auto. }
Qed.
Hint Resolve uniquely_valued_univi_ex_bar : slow.

(*Lemma local_univi_bar {o} :
  forall inh uni i, @local_ts o inh (univi_bar i inh uni).
Proof.
  introv eqiff alla.
  eapply local_per_bar in alla; eauto 3 with slow.
Qed.
Hint Resolve local_univi_bar : slow.
*)

Lemma type_extensionality_univi_ex {o} :
  forall inh uni, @type_extensionality o (univi_ex inh uni).
Proof.
  introv h q.
  unfold univi_ex in *; exrepnd; exists i.
  allrw @univi_exists_iff; exrepnd.
  exists j; dands; tcsp.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve type_extensionality_univi_ex : slow.

Lemma local_univ {o} : @local_ts o nuprla_ex_inh univ.
Proof.
  introv eqiff alla.
  eapply local_per_bar; eauto; eauto 3 with slow.
Qed.
Hint Resolve local_univ : slow.
