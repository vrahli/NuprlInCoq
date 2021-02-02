(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export per.
Require Export continuity_defs_ceq.
Require Export csubst_fresh.
Require Export cequiv_fresh2.


Definition is_spcan_not_atom {o} lib (t : @CTerm o) a : Type :=
  {op : Opid
   & computes_to_can lib (get_cterm t) (oterm op [])
   # !LIn a (get_utokens_o op)}.

Definition noc_bterms {o} (t : @CTerm o) :=
  get_bterms (get_cterm t) = [].

Definition isccancn {o} (t : @CNTerm o) := isccan (get_cnterm t).

Definition cis_spcan_not_atom {o} lib (t : @CTerm o) a :=
  {x : CTerm
   , ccomputes_to_valc lib t x
   # isccanc x
   # noc_bterms x
   # !LIn a (getc_utokens x)}.

Lemma cequivc_fresh_subst1 {o} :
  forall lib v (t : @CVTerm o [v]) a,
    !LIn a (getcv_utokens [v] t)
    -> is_spcan_not_atom lib (substc (mkc_utoken a) v t) a
    -> cequivc lib (mkc_fresh v t) (substc (mkc_utoken a) v t).
Proof.
  introv nia ispc.
  destruct_cterms; allsimpl.
  unfold cequivc; simpl.
  unfold getcv_utokens in nia; allsimpl.
  unfold is_spcan_not_atom in ispc; exrepnd; allsimpl.
  allunfold @computes_to_can; repnd.
  allapply @iscan_implies; repndors; exrepnd; ginv.
  apply (cequiv_fresh_subst1 lib (Can c)); simpl; allrw app_nil_r; auto; tcsp.
  unfold iscan_op; eexists; eauto.
Qed.

Lemma cequivc_fresh_subst2 {o} :
  forall lib v (t : @CVTerm o [v]) a,
    !LIn a (getcv_utokens [v] t)
    -> cis_spcan_not_atom lib (substc (mkc_utoken a) v t) a
    -> ccequivc lib (mkc_fresh v t) (substc (mkc_utoken a) v t).
Proof.
  introv nia ispc.
  unfold cis_spcan_not_atom in ispc; exrepnd; spcast.
  apply cequivc_fresh_subst1; auto.
  destruct_cterms; allsimpl.
  allunfold @computes_to_valc; allsimpl.
  allunfold @noc_bterms; allsimpl.
  allunfold @computes_to_value; repnd.
  allunfold @getc_utokens; allsimpl.
  allapply @isvalue_implies; repnd.
  allapply @iscan_implies; repndors; exrepnd; subst; allsimpl; subst; allsimpl; GC.
  { allrw app_nil_r.
    unfold is_spcan_not_atom; simpl.
    exists (Can c); dands; simpl; tcsp.
    unfold computes_to_can; dands; simpl; auto. }
  { allunfold @isccanc; allsimpl; tcsp. }
Qed.
