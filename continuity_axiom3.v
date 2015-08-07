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


Require Export nat_defs.
Require Export continuity_defs2.
Require Export per_props3.
Require Export per_props_subtype_rel.


Definition continuous_T {o} lib (T F : @CTerm o) :=
  forall f,
    member lib f T
    -> {b : nat
        & forall g,
            member lib g T
            -> agree_upto_red_bc lib b f g
            -> equality_of_int_tt lib (mkc_apply F f) (mkc_apply F g)}.

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
  forall lib (T F : @CTerm o),
    inhabited_type lib (mkc_subtype_rel T int2int_c)
    -> member lib F (mkc_fun T mkc_int)
    -> continuous_T lib T F.
Proof.
  introv inh mT mt.

  rw @inhabited_subtype_rel in inh; repnd.
  clear inh0 inh1.

  pose proof (inh f f mt) as fi.

  assert (member lib (mkc_apply F f) mkc_int) as ma.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto. }

  (* by typing *)
  assert (equality lib f (force_int_f_c nvarx f) int2int_c)
    as ea by (apply equality_force_int_f_c; auto).

  assert (equality lib (mkc_apply F f) (mkc_apply F (force_int_f_c nvarx f)) mkc_int) as mb.
  { rw @equality_in_fun in mT; repnd.
    apply mT; auto.

Lemma equality_force_int_f_c_T {o} :
  forall lib (T f : @CTerm o),
    subtype_rel lib T int2int_c
    -> member lib f T
    -> equality lib f (force_int_f_c nvarx f) T.
Proof.
  introv sr m.
  pose proof (sr f f m) as ef.
  allrw @equality_in_fun; repnd; dands; auto.
  clear ef0 ef1.

Qed.

  }

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

  (* 2nd step *)
  pose proof (comp_force_int_app_F3_c lib F f g nvarx k b) as step2.
  repeat (autodimp step2 hyp).
  { apply agree_upto_c_iff; auto. }

  (* 3rd step *)
  pose proof (comp_force_int_app_F2_c lib F g nvarx k b) as step3.
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
