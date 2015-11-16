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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export sequents_tacs.


(*
   H, x : halts(bottom), J |- False

     bottomDiverges

 *)

Definition rule_bottom_diverges_concl {o} x (H J : @bhyps o) :=
  mk_baresequent (snoc H (mk_hyp x (mk_halts mk_bottom)) ++ J)
                 (mk_concl mk_false mk_bottom).

Definition rule_bottom_diverges {o} x (H J : @bhyps o) :=
  mk_rule (rule_bottom_diverges_concl x H J) [] [].


Lemma rule_bottom_diverges_true {o} :
  forall lib x (H J : @bhyps o),
    rule_true lib (rule_bottom_diverges x H J).
Proof.
  unfold rule_bottom_diverges, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  exists (subvars_nil_l (nh_vars_hyps (snoc H (mk_hyp x (mk_halts mk_bottom)) ++ J))).
  vr_seq_true.
  lsubst_tac.
  allrw @lsubstc_mk_false.
  dands.
  - apply tequality_false.
  - apply similarity_app in sim; exrepnd; subst; allrw length_snoc.
    apply similarity_snoc in sim5; exrepnd; subst; allrw length_snoc; cpx.
    allsimpl; lsubst_tac.
    apply equality_in_halts in sim2; repnd; spcast.
    unfold hasvaluec in sim0; allsimpl.
    apply not_hasvalue_bot in sim0; sp.
Qed.

Lemma rule_bottom_diverges_true2 {o} :
  forall lib x (H J : @bhyps o),
    rule_true2 lib (rule_bottom_diverges x H J).
Proof.
  introv.
  apply rule_true_iff_rule_true2.
  apply rule_bottom_diverges_true.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)

