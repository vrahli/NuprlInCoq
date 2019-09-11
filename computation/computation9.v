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


Require Export computation8.

Lemma hasvaluec_computes_to_valc_implies {o} :
  forall lib (a : @CTerm o),
    hasvaluec lib a -> {b : CTerm & computes_to_valc lib a b}.
Proof.
  introv hv; destruct_cterms; unfold hasvaluec in hv; allsimpl.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  applydup @isvalue_implies in hv0; repnd.
  allrw @isprogram_eq.
  exists (mk_ct t' hv2).
  unfold computes_to_valc, computes_to_value; simpl; dands; auto.
Qed.
