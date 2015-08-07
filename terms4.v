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


Require Export computation2.

Definition has_name {o} a (t : @NTerm o) : Type :=
  match t with
    | oterm (Can (NUTok a')) _ => if get_patom_deq o a a' then True else False
    | _ => False
  end.

Definition computes_to_name {o} lib a (t : @NTerm o) : Type :=
  {v : NTerm & computes_to_value lib t v # has_name a v}.

Definition isnexc {o} lib a (t : @NTerm o) : Type :=
  match t with
    | oterm Exc (bterm [] u :: _) => computes_to_name lib a u
    | _ => False
  end.

Lemma isnexc_implies {o} :
  forall lib a (t : @NTerm o),
    isnexc lib a t
    -> {l : list BTerm
        & {u : NTerm
        & {v : NTerm
        & t = oterm Exc (bterm [] u :: l)
        # computes_to_value lib u v
        # has_name a v }}}.
Proof.
  introv i.
  destruct t as [v|f|op bs]; allsimpl; tcsp.
  destruct op; allsimpl; tcsp.
  destruct bs; allsimpl; tcsp.
  destruct b; allsimpl; tcsp.
  destruct l; allsimpl; tcsp.
  unfold computes_to_name in i; exrepnd.
  eexists; eexists; eexists; eauto.
Qed.

Definition ispnexc {p} lib a (t : @NTerm p) := isnexc lib a t # isprogram t.

Lemma computes_to_name_utoken {o} :
  forall lib (a : get_patom_set o),
    computes_to_name lib a (mk_utoken a).
Proof.
  introv; exists (mk_utoken a); simpl; boolvar; dands; auto;
  apply computes_to_value_isvalue_refl; apply isvalue_utoken.
Qed.
Hint Resolve computes_to_name_utoken : slow.
