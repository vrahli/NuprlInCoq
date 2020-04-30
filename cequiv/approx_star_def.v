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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export computation_swap.
Require Export approx_props1.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(* begin hide *)

Definition LNTrel {o} := @plibrary o -> @NTerm o -> @NTerm o -> [univ].

Definition not_swap {o} (op : @Opid o) :=
  match op with
  | NSwapCs2 _ => False
  | _ => True
  end.

Definition not_swap_or_fresh {o} (op : @Opid o) :=
  match op with
  | NSwapCs2 _ => False
  | NCan NFresh => False
  | _ => True
  end.

Definition blift_sub {o}
           (op : @Opid o)
           (R : LNTrel)
           (lib : plibrary)
           (b1 b2: @BTerm o) : [univ] :=
  {lv : list NVar
   $ {nt1,nt2 : NTerm
   $ (
      (op <> NCan NFresh (*not_swap_or_fresh op*) # R lib nt1 nt2)
      [+]
      {sub : Sub
       & op = NCan NFresh
       # R lib (lsubst nt1 sub) (lsubst nt2 sub)
       # nrut_sub (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2) sub
       # lv = dom_sub sub}
(*      [+]
      {sw : cs_swap
       & op = NSwapCs2 sw
       # R (swap_cs_plib sw lib) (swap_cs_term sw nt1) (swap_cs_term sw nt2)}*)
     )
   # alpha_eq_bterm b1 (bterm lv nt1)
   # alpha_eq_bterm b2 (bterm lv nt2) }}.

Definition lblift_sub {o}
           (op : Opid)
           (R : LNTrel)
           (lib : plibrary)
           (tls trs: list (@BTerm o)) : [univ] :=
  length tls = length trs
  # forall n : nat, n < length tls -> blift_sub op R lib (tls{[n]}) (trs{[n]}).

(* end hide *)

(** %\noindent% To prove that [approx] is a cogruence, Howe defined a
    relation
    [approx_star] that contains [approx_open] and is a congruence by
    definition. The main challenge then is to prove that [approx_star]
    implies [approx_open], and hence they are equivalent.
    Howe reduced this
    property to a set of conditions(called extensionality) on
    each non-canonical [Opid] in the computation system.
    We managed to mechanize this reduction in Coq and also
    proved that all the [Opid]s of Nuprl satisfy his extensionality
    condition.

    We begin by defining his [approx_star] relation. It is a relation
    on well formed (possibly open) [NTerm]s. So we need not use [olift]
    before applying [lblift] in the [apso] constructor. %\\*%

 *)

(*
 A reader who is not intersted in these details might
    want to just look at the statement of the theorem [approx_congruence]
    toward the end of this section move to the next sections. *)

Inductive approx_star {p} :
  @plibrary p -> @NTerm p -> @NTerm p -> [univ] :=
| apsv:
    forall lib v t2,
      approx_open lib (vterm v) t2
      -> approx_star lib (vterm v) t2
| apso:
    forall lib
           (op : Opid)
           (t2: NTerm)
           (lbt1 lbt1' : list BTerm),
      length lbt1 = length lbt1'
      -> lblift_sub op approx_star lib lbt1 lbt1'
      -> approx_open lib (oterm op lbt1') t2
      -> approx_star lib (oterm op lbt1) t2.
Hint Constructors approx_star : slow.

Definition approx_star_bterm {o} (op : @Opid o) := blift_sub op approx_star.
Definition approx_starbts {o} (op : @Opid o) := lblift_sub op approx_star.
