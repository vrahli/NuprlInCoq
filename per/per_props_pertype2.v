(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export per_props_pertype.
Require Export per_props_erase.
Require Export sequents_tacs.
Require Export cequiv_tacs.
Require Export subst_tacs.


Lemma is_per_type_sqper_rel_change_subst {o} :
  forall lib v1 v2 R s1 s2 w c1 c2,
    (forall x y : @CTerm o,
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s1 c1) x y)
       <=>
       inhabited_type lib (mkc_apply2 (lsubstc (sqper_rel v1 v2 R) w s2 c2) x y))
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s1 c1)
    -> is_per_type lib (lsubstc (sqper_rel v1 v2 R) w s2 c2).
Proof.
  introv iff isper.
  allunfold @is_per_type.
  destruct isper as [sym trans].
  allunfold @sqper_rel; lsubst_tac.
  dands.

  - clear trans.
    allunfold @sym_type; introv inh.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (sym x y); clear sym; intro sym.
    autodimp sym hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y x); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

  - clear sym.
    allunfold @trans_type; introv inh1 inh2.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (trans x y z); clear trans; intro trans.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x y); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    autodimp trans hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff y z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i1.
    autodimp i2 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.

    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    generalize (iff x z); clear iff; intro iff.
    destruct iff as [i1 i2]; clear i2.
    autodimp i1 hyp.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
    repeat (betared; repeat substc_lsubstc_vars3; lsubst_tac).
    allrw @inhabited_type_erasec; auto.
Qed.
