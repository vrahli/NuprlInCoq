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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms2.


Lemma deq_nterm {p} :
  dec_consts p
  -> forall x y : @NTerm p,
       assert (no_seq x)
       -> {x = y} + {x <> y}.
Proof.
  introv dc.
  nterm_ind1 x as [v1 | o1 lbt1 Hind] Case; introv ns.

  - Case "vterm".
    destruct y as [v2 | o lbt2]; [  | right; intro Hc; inverts Hc].
    destruct (deq_nvar v1 v2); subst;
    [ left; auto; fail
    | right; intro Hc; inverts Hc; sp
    ].

  - Case "oterm".
    destruct y as [v2 | o2 lbt2]; [ right; intro Hc; inverts Hc | ].
    allsimpl.
    allrw assert_of_andb; repnd.
    destruct (opid_dec dc o1 o2); auto; subst; [  | right; intro Hc; inverts Hc;sp].
    assert ((lbt1=lbt2) + (lbt1 <> lbt2)) as Hbt.
    Focus 2.
    dorn Hbt; subst; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    revert lbt2.
    induction lbt1.
    destruct lbt2; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    destruct lbt2;  [ right; intro Hc; inverts Hc; fail | ].
    destruct a as [lv1 nt1]. destruct b as [lv2 nt2].
    lapply (IHlbt1);
      [ | introv Hin; apply Hind with (lv:=lv); eauto; right; auto].
    introv bdec.
    allsimpl.
    allrw assert_of_andb; repnd.
    autodimp bdec hyp.
    destruct (bdec lbt2); subst; [  | right; intro Hc; inverts Hc;sp;fail ].
    destruct (list_eq_dec deq_nvar lv1 lv2);
      subst; [ | right; intro Hc; inverts Hc;sp;fail ].
    destruct (Hind nt1 lv2 (injL(eq_refl _) ) nt2); auto; subst;
    [left; auto |  right; intro Hc; inverts Hc;sp ].
Defined.
Hint Immediate deq_nterm.

(*
Lemma map_removevars {p} :
  forall dc : dec_consts p,
  forall lvi lvr,
    map (@vterm p) (remove_nvars lvi lvr)
    = diff (deq_nterm dc) (map vterm lvi) (map vterm lvr).
Proof.
  intros. apply map_diff_commute.
  introv Hc. inverts Hc. auto.
Qed.
*)

(*
Lemma deq_bterm {p} : dec_consts p -> Deq (@BTerm p).
Proof.
  intros dc btx bty. destruct btx as [lvx ntx].
  destruct bty as [lvy nty].
  destruct (deq_nterm dc ntx nty);
  destruct (deq_list deq_nvar lvx lvy); subst;sp;
  right; introv Heq;
  inverts Heq; cpx.
Qed.
Hint Resolve deq_bterm.
*)
