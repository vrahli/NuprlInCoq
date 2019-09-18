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


Require Export substc_more.
Require Export sequents_tacs.
Require Export per_props_product.
Require Export per_props_function.
Require Export per_props_squash.
Require Export per_props_equality.
Require Export per_props_nat2.
Require Export lsubstc_vars.



Hint Resolve nat_in_nat : slow.

Lemma implies_ccequivc_ext_apply2 {o} :
  forall lib (f g a b c d : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib c d
    -> ccequivc_ext lib (mkc_apply2 f a c) (mkc_apply2 g b d).
Proof.
  introv ceqa ceqb ceqc x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  pose proof (ceqc _ x) as ceqc.
  simpl in *; spcast.
  apply implies_cequivc_apply2; auto.
Qed.
Hint Resolve implies_ccequivc_ext_apply2 : slow.

Definition at_open_bar {o} (lib : @library o) F :=
  forall lib',
    lib_extends lib' lib
    -> exists (lib'' : library) (xt : lib_extends lib'' lib'), F lib''.

Lemma in_open_bar_implies_at_open_bar {o} :
  forall (lib : @library o) F,
    in_open_bar lib F
    -> at_open_bar lib F.
Proof.
  introv h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' xt; apply h1; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_inhabited_type_bar {o} :
  forall {lib lib'} (x : lib_extends lib' lib) (T : @CTerm o),
    inhabited_type_bar lib T
    -> inhabited_type_bar lib' T.
Proof.
  introv x inh.
  unfold inhabited_type_bar in *; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_inhabited_type_bar : slow.

Definition FunLib {o} (lib : @library o) :=
  forall (lib' : @library o), LibExt lib'.

Definition FunLibProp {o} (lib : @library o) :=
  forall (lib' : @library o), Prop.

Definition NatFunLib {o} (lib : @library o) :=
  forall (n : nat) (lib' : @library o), LibExt lib'.

Definition NatFunLibProp {o} (lib : @library o) :=
  forall (n : nat) (lib' : @library o), Prop.

Definition NatFunLibExt {o} (lib : @library o) :=
  forall (n : nat) lib' (x : lib_extends lib' lib), LibExt lib'.

Definition NatFunLibExtProp {o} (lib : @library o) :=
  forall (n : nat) lib' (x : lib_extends lib' lib), Prop.

Lemma in_open_bar_choice {o} :
  forall (lib : @library o) (F : FunLibProp lib),
    in_open_bar lib F
    -> exists (Flib : FunLibExt lib),
      in_ext_ext
        lib
        (fun lib' x =>
           in_ext_ext (Flib lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F lib0)).
Proof.
  introv h.
  apply in_open_bar_implies_in_open_bar_ext in h.
  apply in_open_bar_ext_choice in h; auto.
Qed.

Lemma nat_in_open_bar_ext_choice {o} :
  forall (lib : @library o) (F : NatFunLibExtProp lib),
    (forall (k : nat), in_open_bar_ext lib (F k))
    -> exists (Flib : NatFunLibExt lib),
      forall (k : nat),
        in_ext_ext
          lib
          (fun lib' x =>
             in_ext_ext (Flib k lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0 z)).
Proof.
  introv h.

  assert (forall (k : nat),
             exists (Flib : FunLibExt lib),
               in_ext_ext
                 lib
                 (fun lib' x =>
                    in_ext_ext (Flib lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0 z))) as q.
  {
    introv.
    pose proof (h k) as h.
    apply in_open_bar_ext_choice in h; auto.
  }
  clear h.

  pose proof (FunctionalChoice_on
                nat
                (FunLibExt lib)
                (fun k Flib =>
                   in_ext_ext
                     lib
                     (fun lib1 ext1 =>
                        in_ext_ext
                          (Flib lib1 ext1)
                          (fun lib2 ext2 =>
                             forall z : lib_extends lib2 lib,
                               F k lib2 z)))) as C.
  simpl in C.
  repeat (autodimp C hyp).
Qed.

Lemma nat_in_open_bar_choice {o} :
  forall (lib : @library o) (F : NatFunLibProp lib),
    (forall (k : nat), in_open_bar lib (F k))
    -> exists (Flib : NatFunLibExt lib),
      forall (k : nat),
        in_ext_ext
          lib
          (fun lib' x =>
             in_ext_ext (Flib k lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0)).
Proof.
  introv h.
  apply nat_in_open_bar_ext_choice.
  introv.
  apply in_open_bar_implies_in_open_bar_ext; auto.
Qed.

Definition NatFunLibExtNat {o}
           {lib  : @library o}
           (Flib : NatFunLibExt lib) :=
  forall (n : nat)
         lib1 (ext1 : lib_extends lib1 lib)
         lib2 (ext2 : lib_extends lib2 (Flib n lib1 ext1))
         (z : lib_extends lib2 lib),
    nat.

Definition NatFunLibExtNatProp {o}
           {lib  : @library o}
           (Flib : NatFunLibExt lib) :=
  forall (n : nat)
         lib1 (ext1 : lib_extends lib1 lib)
         lib2 (ext2 : lib_extends lib2 (Flib n lib1 ext1))
         (z : lib_extends lib2 lib)
         (n : nat),
    Prop.

Record NatDepLibExt {o} (lib : @library o) (F : NatFunLibExt lib) :=
  MkNatDepLibExt
    {
      nat_dep_lib_ext_nat  : nat;
      nat_dep_lib_ext_lib1 : @library o;
      nat_dep_lib_ext_ext1 : lib_extends nat_dep_lib_ext_lib1 lib;
      nat_dep_lib_ext_lib2 : @library o;
      nat_dep_lib_ext_ext2 : lib_extends nat_dep_lib_ext_lib2 (F nat_dep_lib_ext_nat nat_dep_lib_ext_lib1 nat_dep_lib_ext_ext1);
      nat_dep_lib_ext_extz : lib_extends nat_dep_lib_ext_lib2 lib;
    }.
Arguments MkNatDepLibExt [o] [lib] [F] _ _ _ _ _.
Arguments nat_dep_lib_ext_nat  [o] [lib] [F] _.
Arguments nat_dep_lib_ext_lib1 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_ext1 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_lib2 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_ext2 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_extz [o] [lib] [F] _.

Lemma nat_in_open_bar_choice_nat {o} :
  forall (lib  : @library o)
         (Flib : NatFunLibExt lib)
         (P    : NatFunLibExtNatProp Flib),
    (forall k : nat,
        in_ext_ext
          lib
          (fun lib1 ext1 =>
             in_ext_ext
               (Flib k lib1 ext1)
               (fun lib2 ext2 =>
                  forall (z : lib_extends lib2 lib),
                    exists (j : nat), P k lib1 ext1 lib2 ext2 z j)))
    -> exists (Fnat : NatFunLibExtNat Flib),
    forall k : nat,
      in_ext_ext
        lib
        (fun lib1 ext1 =>
           in_ext_ext
             (Flib k lib1 ext1)
             (fun lib2 ext2 =>
                forall (z : lib_extends lib2 lib),
                P k lib1 ext1 lib2 ext2 z (Fnat k lib1 ext1 lib2 ext2 z))).
Proof.
  introv h.

  pose proof (FunctionalChoice_on
                (NatDepLibExt lib Flib)
                nat
                (fun x n =>
                   P (nat_dep_lib_ext_nat  x)
                     (nat_dep_lib_ext_lib1 x)
                     (nat_dep_lib_ext_ext1 x)
                     (nat_dep_lib_ext_lib2 x)
                     (nat_dep_lib_ext_ext2 x)
                     (nat_dep_lib_ext_extz x)
                     n)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv.
    destruct a as [k lib1 ext1 lib2 ext2 extz]; simpl in *.
    apply h. }
  exrepnd.
  exists (fun k lib1 ext1 lib2 ext2 extz => f (MkNatDepLibExt k lib1 ext1 lib2 ext2 extz)); simpl.
  repeat introv.
  apply (C0 (MkNatDepLibExt k lib' e lib'0 e0 z)).
Qed.

Hint Rewrite @mkcv_apply_substc : slow.
Hint Rewrite @substc2_apply : slow.

Definition lam_ax {o} := @mkc_lam o nvarx (mkcv_axiom nvarx).


(*

   forall m : nat, squash (exists n : nat, P(m,n))

   implies

   squash (exists f : nat -> nat, forall m : nat, squash (P (m, f m)))

 *)
Lemma axiom_of_choice_00 {o} :
  forall lib f m n (P : @CTerm o),
    n <> m
    -> f <> m
    -> (forall a b,
          member lib a mkc_tnat
          -> member lib b mkc_tnat
          -> type lib (mkc_apply2 P a b))
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            m
            (mkcv_squash
               [m]
               (mkcv_exists
                  [m]
                  (mkcv_tnat [m])
                  n
                  (mkcv_apply2 [n,m]
                               (mk_cv [n,m] P)
                               (mk_cv_app_l [n] [m] (mkc_var m))
                               (mk_cv_app_r [m] [n] (mkc_var n))))))
    -> inhabited_type_bar
         lib
         (mkc_exists
            nat2nat
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               m
               (mkcv_squash
                  [m,f]
                  (mkcv_apply2 [m,f]
                               (mk_cv [m,f] P)
                               (mk_cv_app_r [f] [m] (mkc_var m))
                               (mkcv_apply [m,f]
                                           (mk_cv_app_l [m] [f] (mkc_var f))
                                           (mk_cv_app_r [f] [m] (mkc_var m))))))).
Proof.
  introv d1 d2 impp inh.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> inhabited_type_bar
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] k)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 _ (lib_extends_refl _) k k) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_tnat_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  introv ext.

  assert (forall (k : nat),
             in_open_bar
               lib'
               (fun lib =>
                  exists (j : nat),
                    inhabited_type lib (mkc_apply2 P (mkc_nat k) (mkc_nat j)))) as xx.
  {
    introv.
    pose proof (q (mkc_nat k)) as q; autodimp q hyp; eauto 3 with slow;[].
    eapply lib_extends_preserves_inhabited_type_bar in q; eauto.
    clear dependent lib.
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; eauto; clear q; introv ext q.
    apply inhabited_exists in q; repnd; exrepnd.
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; try exact q2; clear q2; introv xta q2; exrepnd.
    apply member_tnat_iff in q4.
    eapply in_open_bar_pres; try exact q4; clear q4; introv xtb q4; exrepnd.
    exists k0.
    autorewrite with slow in *; eauto 3 with slow.
    eapply member_monotone in q2; eauto.
    eapply member_respects_cequivc_type in q2;
      [|apply implies_ccequivc_ext_apply2;
        [apply ccequivc_ext_refl|apply ccequivc_ext_refl|];
        apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto].
    eauto 2 with slow.
  }

(*
  assert (forall (k : nat),
             at_open_bar
               lib'
               (fun lib =>
                  exists (j : nat),
                    inhabited_type lib (mkc_apply2 P (mkc_nat k) (mkc_nat j)))) as yy.
  { introv; apply in_open_bar_implies_at_open_bar; eauto. }
  unfold at_open_bar in yy.

  assert (forall (k : nat),
             exists (j     : nat)
                    (lib'' : library)
                    (ext   : lib_extends lib'' lib'),
               inhabited_type lib'' (mkc_apply2 P (mkc_nat k) (mkc_nat j))) as zz.
  { introv; pose proof (yy k _ (lib_extends_refl _)) as h; exrepnd; eauto. }
*)

  pose proof (fresh_choice_seq_name_in_library lib') as w; exrepnd.
  apply @nat_in_open_bar_choice in xx; exrepnd.
  apply nat_in_open_bar_choice_nat in xx0; exrepnd.

  (* WARNING *)
  Parameter xxxxx : False.
  (* We need other kinds of choice sequence restriction
     without default values *)

  remember (lib_cs
              name
              (MkChoiceSeqEntry
                 o
                 []
                 (csc_type
                    (fun i => mkc_zero)
                    (fun i t =>
                       exists (lib1 : library)
                              (ext1 : lib_extends lib1 lib')
                              (lib2 : library)
                              (ext2 : lib_extends lib2 (Flib i lib1 ext1))
                              (extz : lib_extends lib2 lib'),
                         t = mkc_nat (Fnat i lib1 ext1 lib2 ext2 extz))
                    (fun i => match xxxxx with end)))) as entry.
  hide_hyp Heqentry.

  exists (entry :: lib').

  (* WARNING *)
  assert (lib_extends (entry :: lib') lib') as xta.
  { apply implies_lib_extends_cons_left; eauto 3 with slow.
    { admit. }
    { admit. } }
  exists xta.

  introv xtb.
  apply inhabited_exists; dands; eauto 3 with slow.
  { admit. }

  exists (@mkc_pair o (mkc_choice_seq name) lam_ax).
  apply in_ext_implies_in_open_bar; introv xtc.
  exists (@mkc_choice_seq o name) (@lam_ax o).
  dands; eauto 3 with slow.

  { (* ?? *) admit. }

  unfold mkcv_forall.
  repeat (rw @substc_mkcv_function; auto).
  autorewrite with slow.
  apply equality_in_function3; dands; eauto 3 with slow;[].

  introv xtd eqn.
  dands.

  { admit. }

  allrw @substcv_as_substc2.
  autorewrite with slow.
  repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
  autorewrite with slow.
  apply equality_in_tnat in eqn.
  unfold equality_of_nat_bar in eqn.
  apply all_in_ex_bar_equality_implies_equality.
  eapply in_open_bar_pres; try exact eqn; clear eqn; introv xte eqn.
  unfold equality_of_nat in eqn; exrepnd.
  apply equality_in_mkc_squash.
  dands; eauto 3 with slow.

  { admit. }
  { admit. }

  pose proof (xx1 k) as xx1.
  introv xtf.
  assert (lib_extends lib'4 lib') as xtg by admit.
  pose proof (xx1 _ xtg) as xx1; simpl in xx1.
  assert (lib_extends (Flib k lib'4 xtg) lib'4) as xth by eauto 3 with slow.
  (* We have to get [S(k)] choices *)
  exists (Flib k lib'4 xtg) xth.
  introv xti.
  assert (lib_extends lib'5 lib') as xtj by admit.
  pose proof (xx1 _ xti xtj) as xx1; simpl in xx1.

XXXXXXXXXX

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> {j : CTerm
                , member lib j mkc_tnat
                # inhabited_type_bar lib (mkc_apply2 P k j)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

  (* First use FunctionalChoice_on to get an existential (a Coq function from terms to terms) *)

  pose proof (FunctionalChoice_on
                {k : CTerm & member lib k mkc_tnat}
                (@CTerm o)
                (fun k j => member lib j mkc_tnat # inhabited_type lib (mkc_apply2 P (projT1 k) j)))
    as fc.
  simphyps.
  autodimp fc hyp; tcsp;[].
  exrepnd.
  clear h.
  rename fc0 into fc.

  assert {c : nat -> nat
          & forall a : CTerm,
              member lib a mkc_tnat
              -> (member lib (mkc_eapply (mkc_nseq c) a) mkc_tnat
                  # inhabited_type lib (mkc_apply2 P a (mkc_eapply (mkc_nseq c) a)))} as fs.
  { exists (fun n =>
              match member_tnat_implies_computes
                      lib
                      (f1 (existT _ (mkc_nat n) (nat_in_nat lib n)))
                      (fst (fc (existT _ (mkc_nat n) (nat_in_nat lib n)))) with
                | existT _ k _ => k
              end).
    introv mem.
    dands.

    - apply member_tnat_iff in mem; exrepnd.
      allrw @computes_to_valc_iff_reduces_toc; repnd.
      eapply member_respects_reduces_toc;[apply reduces_toc_eapply_nseq;exact mem1|].

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as mt.
      exrepnd.

      apply (member_respects_reduces_toc _ _ (mkc_nat k0)).

      + unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; allsimpl; dcwf h; simpl.
        boolvar; try omega.
        rw @Znat.Nat2Z.id.
        rewrite <- Heqmt; auto.

      + apply member_tnat_iff.
        exists k0.
        apply computes_to_valc_refl; eauto 3 with slow.

    - apply member_tnat_iff in mem; exrepnd.
      pose proof (nat_in_nat lib k) as mk.

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as q.
      exrepnd.
      remember (fc exI(mkc_nat k, nat_in_nat lib k)) as fck.
      exrepnd.
      allsimpl.

      allunfold @inhabited_type; exrepnd.
      exists t.
      allsimpl.

      eapply member_respects_cequivc_type;[|exact fck1].
      apply implies_cequivc_apply2; auto.

      + apply cequivc_sym.
        apply computes_to_valc_implies_cequivc; auto.

      + apply cequivc_sym.
        allrw @computes_to_valc_iff_reduces_toc; repnd.
        eapply cequivc_trans;
          [apply reduces_toc_implies_cequivc;
            apply reduces_toc_eapply_nseq;exact mem1
          |].

        eapply cequivc_trans;
          [|apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;
             exact q0].
        apply reduces_toc_implies_cequivc.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl.
        boolvar; try omega.
        allrw @Znat.Nat2Z.id.
        allsimpl.
        rw <- Heqfck; simpl.
        rw <- Heqq; auto.
  }
  clear f1 fc.
  exrepnd.

  (* then "convert" the Coq function into a Nuprl function *)

  apply inhabited_product.

  dands.

  { apply type_nat2nat. }

  { introv eqf.
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    apply tequality_function.
    dands.
    { apply tnat_type. }

    introv eqn.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_squash.
    apply type_respects_cequivc_left.

    { apply implies_cequivc_apply2; auto.
      { apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
    }

    { apply impp; eauto 3 with slow.
      { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_sym in eqf; apply equality_refl in eqf; auto. }
    }
  }

  { exists (@mkc_nseq o c).
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkc_var_substc.

    dands.

    { apply member_nseq_nat2nat. }

    { apply inhabited_function; dands; eauto 3 with slow.

      - introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        apply tequality_mkc_squash.
        apply type_respects_cequivc_left.

        { apply implies_cequivc_apply2; auto.
          { apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
          { apply implies_cequivc_apply; auto.
            apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
        }

        { apply impp; eauto 3 with slow.
          { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
          { pose proof (member_nseq_nat2nat lib c) as eqf.
            eapply equality_nat2nat_apply in eqf;[|exact eqn].
            apply equality_sym in eqf; apply equality_refl in eqf; auto. }
        }

      - exists (@mkc_lam o nvarx (mkcv_axiom nvarx)).
        introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        applydup @equality_int_nat_implies_cequivc in eqn.
        apply equality_refl in eqn.
        eapply equality_respects_cequivc_right;
          [apply implies_cequivc_apply;
            [apply cequivc_refl
            |exact eqn0]
          |].
        rw @member_eq.

        eapply member_respects_cequivc;
          [apply cequivc_sym;
            apply cequivc_beta
          |].
        rw @substc_mkcv_axiom.

        apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow).

        pose proof (fs0 a eqn) as q; repnd.

        eapply inhabited_type_cequivc;[|exact q].
        apply implies_cequivc_apply2; auto.
        apply cequivc_sym.
        apply reduces_toc_implies_cequivc.
        destruct_cterms.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl; auto.
    }
  }
Qed.
*)


Definition rule_AC00 {o}
           (P e : @NTerm o)
           (f m n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_squash (mk_exists (mk_nat2nat) f (mk_forall mk_tnat n (mk_squash (mk_apply2 P (mk_var n) (mk_apply (mk_var f) (mk_var n)))))))))
      [ mk_baresequent H (mk_concl (mk_forall mk_tnat n (mk_squash (mk_exists mk_tnat m (mk_apply2 P (mk_var n) (mk_var m))))) e),
        mk_baresequent H (mk_conclax (mk_member P (mk_fun mk_tnat (mk_fun mk_tnat (mk_uni i))))) ]
      [].

Lemma rule_AC00_true {p} :
  forall lib
         (P e : NTerm)
         (f m n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true lib (rule_AC00 P e f m n H i).
Proof.
  unfold rule_AC00, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 _ ext s1 s2 eqh sim) as hh; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 _ ext s1 s2 eqh sim) as qq; exrepnd; clear hyp2.

  allunfold @mk_forall.
  allunfold @mk_exists.
  allunfold @mk_nat2nat.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in qq0; auto;[].
  allrw @tequality_mkc_member_sp; repnd.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.

  dands.

  - apply tequality_mkc_squash.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    apply tequality_product; dands.
    { apply type_nat2nat. }

    introv ext' eqf.
    repeat lsubstc_vars_as_mkcv.
    repeat (rw @substc_mkcv_function; auto;[]).
    autorewrite with slow.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_apply.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto;[]).
    repeat (rw @substc2_mk_cv_app_l; auto;[]).
    allrw @mkc_var_substc.

    apply tequality_function; dands; eauto 3 with slow.
    { apply tnat_type. }

    introv ext'' eqn.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @mkcv_apply_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_squash.
    apply equality_in_fun in qq0; repnd.
    applydup qq0 in eqn; eauto 3 with slow;[].
    lsubst_tac.
    apply equality_in_fun in eqn0; repnd.
    pose proof (eqn0 _ (lib_extends_refl _) (mkc_apply a a0) (mkc_apply a' a'0)) as q.
    allrw @lsubstc_mkc_tnat.
    autodimp q hyp.
    { apply equality_nat2nat_apply; eauto 3 with slow. }
    allrw <- @mkc_apply2_eq.
    apply equality_in_uni in q; auto.

  - apply equality_in_mkc_squash; dands; spcast; eauto 3 with slow.

    SearchAbout equality mkc_squash.

    pose proof (axiom_of_choice_00 lib f n m (lsubstc P wt s1 ct1)) as ac.
    repeat (autodimp ac hyp).

    + (* from qq1 *)
      introv m1 m2.
      apply equality_in_fun in qq1; repnd.
      pose proof (qq1 a a) as h.
      autodimp h hyp.
      lsubst_tac.
      allrw @lsubstc_mkc_tnat.
      apply equality_in_fun in h; repnd.
      pose proof (h b b) as q.
      autodimp q hyp.
      apply equality_in_uni in q; auto.
      allrw <- @mkc_apply2_eq; auto.

    + (* from hh1 *)
      apply equality_refl in hh1.
      exists (lsubstc e wfce1 s1 pt0).

      repeat lsubstc_vars_as_mkcv.
      auto.

    + repeat lsubstc_vars_as_mkcv.

      dands;
        [|allunfold @mkc_exists; allunfold @mkcv_forall;
          eapply inhabited_type_respects_alphaeqc;[|exact ac];
          apply alphaeqc_mkc_product1;
          apply alphaeqc_sym; apply lsubstc_mk_nat2nat].
Qed.


(*

   forall f : nat -> nat, squash exists n : nat, P(f,n)

   implies

   squash exists F : (nat -> nat) -> nat, forall f : nat -> nat, P (f, F f)

 *)
Lemma axiom_of_choice_10 {o} :
  forall lib F f n (P : @CTerm o),
    n <> f
    -> inhabited_type
         lib
         (mkc_forall
            nat2nat
            f
            (mkcv_squash
               [f]
               (mkcv_exists
                  [f]
                  (mkcv_tnat [f])
                  n
                  (mkcv_apply2 [n,f]
                               (mk_cv [n,f] P)
                               (mk_cv_app_l [n] [f] (mkc_var f))
                               (mk_cv_app_r [f] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_squash
            (mkc_exists
               (mkc_fun nat2nat mkc_tnat)
               F
               (mkcv_forall
                  [F]
                  (mk_cv [F] nat2nat)
                  f
                  (mkcv_apply2 [f,F]
                               (mk_cv [f,F] P)
                               (mk_cv_app_r [F] [f] (mkc_var f))
                               (mkcv_apply [f,F]
                                           (mk_cv_app_l [f] [F] (mkc_var F))
                                           (mk_cv_app_r [F] [f] (mkc_var f))))))).
Proof.
  introv d1 inh.
  apply inhabited_squash.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall f : CTerm,
            member lib f nat2nat
            -> inhabited_type
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] f)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 f1 f1) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_tnat_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  assert (forall f : CTerm,
            member lib f nat2nat
            -> {k : CTerm
                , member lib k mkc_tnat
                # inhabited_type lib (mkc_apply2 P f k)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

Abort.
