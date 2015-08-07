(*

  Copyright 2014 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import continuity.
Require Import continuity2.
Require Import continuity3.
Require Export continuity_defs2.


(* !! MOVE to opid *)
Definition fresh_atom (o : POpid) : FreshFun (get_patom_set o) :=
  dsetFresh (patom o).

Definition uexcc {o} (a : get_patom_set o) :=
  mkc_nexception (Some a) mkc_axiom.

Definition get_utokensc {o} (t : @CTerm o) : list (get_patom_set o) :=
  get_utokens (get_cterm t).

Lemma comp_force_int_app_F_c {o} :
  forall lib (F f : @CTerm o) x z,
    reduces_toc
      lib
      (force_int_F_c x F f)
      (mkc_integer z)
    -> {b : nat
        & forall (e : CTerm) b',
            b <= b'
            -> reduces_toc
                 lib
                 (force_int_bound_F_c x b' F f e)
                 (mkc_integer z)}.
Proof.
  introv r.
  unfold reduces_toc in r.
  rw @get_cterm_force_int_F_c in r.
  simpl in r.
  apply comp_force_int_app_F in r; exrepnd.
  exists b.
  introv l.
  pose proof (r0 (get_cterm e) b') as h.
  repeat (autodimp h hyp).
  { rw @free_vars_cterm; sp. }
  unfold reduces_toc.
  rw @get_cterm_force_int_bound_F_c; auto.
Qed.

Lemma comp_force_int_app_F3_c {o} :
  forall lib a (F f g : @CTerm o) x z b,
    !LIn a (get_utokensc F)
    -> !LIn a (get_utokensc f)
    -> !LIn a (get_utokensc g)
    -> agree_upto_bc lib b f g
    -> reduces_toc
         lib
         (force_int_bound_F_c x b F f (uexcc a))
         (mkc_integer z)
    -> reduces_toc
         lib
         (force_int_bound_F_c x b F g (uexcc a))
         (mkc_integer z).
Proof.
  introv ni1 ni2 ni3 agree r.
  allunfold @reduces_toc.
  allrw @get_cterm_force_int_bound_F_c.
  allsimpl.
  apply (comp_force_int_app_F3 lib a (get_cterm F) (get_cterm f) (get_cterm g)); auto;
  allrw @free_vars_cterm; allsimpl; tcsp; eauto with slow.
Qed.

Lemma comp_force_int_app_F2_c {o} :
  forall lib a (F g : @CTerm o) x z b,
    !LIn a (get_utokensc F)
    -> !LIn a (get_utokensc g)
    -> reduces_toc
         lib
         (force_int_bound_F_c x b F g (uexcc a))
         (mkc_integer z)
    -> reduces_toc
         lib
         (force_int_F_c x F g)
         (mkc_integer z).
Proof.
  introv ni1 ni2 r.
  allunfold @reduces_toc.
  allrw @get_cterm_force_int_bound_F_c.
  allrw @get_cterm_force_int_F_c.
  allsimpl.
  apply (comp_force_int_app_F2 lib a (get_cterm F) (get_cterm g) x z b); auto;
  allrw @free_vars_cterm; allsimpl; tcsp; eauto with slow.
Qed.

(*

  F f -> z
  => (* by typing *)
  F (\x.let x:=(x + 0) in f(x)) -> z
  => (* by comp_force_int_app_F *)
  exists b. forall e.
    F (\x.let x:=(let x:=x in if |x|<b then x else e) in f(x)) -> z
    => (* if e cannot get caught, because the 2 functions agree upto b *)
    F (\x.let x:=(let x:=x in if |x|<b then x else e) in g(x)) -> z
    => (* comp_force_int_app_F2 *)
    F (\x.let x:=(x + 0) in g(x)) -> z
    => (* by typing *)
    F g -> z

*)
Lemma continuity_axiom {o} :
  forall lib (F : @CTerm o),
    member lib F (mkc_fun (mkc_fun mkc_int mkc_int) mkc_int)
    -> continuous lib F.
Proof.
  introv mT mt.

  assert (member lib (mkc_apply F f) mkc_int) as ma.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  (* by typing *)
  assert (equality lib f (force_int_f_c nvarx f) (mkc_fun mkc_int mkc_int))
    as ea by (apply equality_force_int_f_c; auto).

  assert (equality lib  (mkc_apply F f) (mkc_apply F (force_int_f_c nvarx f)) mkc_int) as mb.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  apply equality_in_int in mb.
  apply equality_of_int_imp_tt in mb.
  unfold equality_of_int_tt in mb; exrepnd; GC.

  (* 1st step *)
  pose proof (comp_force_int_app_F_c lib F f nvarx k) as step1.
  autodimp step1 hyp.
  { rw @computes_to_valc_iff_reduces_toc in mb0; repnd; auto. }
  destruct step1 as [b step1].

  exists b.
  introv mg agree.
  (* now pick a fresh atom to instantiate h0 with the right exception,
   to then use comp_force_int_app_F3. *)

  pose proof (fresh_atom o (get_utokensc F ++ get_utokensc f ++ get_utokensc g)) as fr.
  destruct fr as [a ni].
  allrw in_app_iff; allrw not_over_or; repnd.
  pose proof (step1 (uexcc a) b) as r1.
  autodimp r1 hyp.

  (* 2nd step *)
  pose proof (comp_force_int_app_F3_c lib a F f g nvarx k b) as step2.
  repeat (autodimp step2 hyp).
  { apply agree_upto_c_iff; auto. }

  (* 3rd step *)
  pose proof (comp_force_int_app_F2_c lib a F g nvarx k b) as step3.
  repeat (autodimp step3 hyp).

  (* by typing *)
  assert (equality lib g (force_int_f_c nvarx g) (mkc_fun mkc_int mkc_int))
    as eb by (apply equality_force_int_f_c; auto).

  assert (equality lib (mkc_apply F g) (mkc_apply F (force_int_f_c nvarx g)) mkc_int) as mc.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  apply equality_in_int in mc.
  apply equality_of_int_imp_tt in mc.
  unfold equality_of_int_tt in mc; exrepnd; GC.

  assert (computes_to_valc lib (force_int_F_c nvarx F g) (mkc_integer k)) as c.
  { rw @computes_to_valc_iff_reduces_toc; dands; eauto with slow. }

  repeat computes_to_eqval.

  exists k0; dands; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
