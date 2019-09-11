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


Require Export approx_props1.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(* begin hide *)

Definition blift_sub {o}
           lib
           (op : @Opid o)
           (R : NTrel)
           (b1 b2: @BTerm o) : [univ] :=
  {lv : list NVar
   $ {nt1,nt2 : NTerm
   $ (
      (op <> NCan NFresh # R nt1 nt2)
      [+]
      {sub : Sub
       & op = NCan NFresh
       # R (lsubst nt1 sub) (lsubst nt2 sub)
       # nrut_sub (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2) sub
       # lv = dom_sub sub}
     )
   # alpha_eq_bterm b1 (bterm lv nt1)
   # alpha_eq_bterm b2 (bterm lv nt2) }}.

Definition lblift_sub {o}
           lib
           (op : Opid)
           (R : NTrel)
           (tls trs: list (@BTerm o)) : [univ] :=
  length tls = length trs
  # forall n : nat, n < length tls -> blift_sub lib op R (tls{[n]}) (trs{[n]}).

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
  @library p -> @NTerm p -> @NTerm p -> [univ] :=
| apsv: forall lib v t2,
          (approx_open lib (vterm v) t2)
          -> (approx_star lib (vterm v) t2)
| apso: forall lib
               (op : Opid)
               (t2: NTerm)
               (lbt1 lbt1' : list BTerm),
          length lbt1 = length lbt1'
          -> lblift_sub lib op (approx_star lib) lbt1 lbt1'
          -> approx_open lib (oterm op lbt1') t2
          -> approx_star lib (oterm op lbt1) t2.
Hint Constructors approx_star : slow.

Definition approx_star_bterm {o} (lib : @library o) op :=
  blift_sub lib op (approx_star lib).
Definition approx_starbts {o} (lib : @library o) op :=
  lblift_sub lib op (approx_star lib).
