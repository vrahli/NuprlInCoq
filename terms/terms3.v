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

Lemma isprogram_equality_implies {o} :
  forall (bterms : list (@BTerm o)),
    isprogram (oterm (Can NEquality) bterms) ->
    {t1 : NTerm $ {t2 : NTerm $ {t3 : NTerm $
     bterms = [bterm [] t1, bterm [] t2, bterm [] t3]
     # isprogram t1
     # isprogram t2
     # isprogram t3}}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b; allsimpl; cpx.
  destruct l; allsimpl; cpx.
  destruct b0; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  destruct b1; allsimpl; cpx.
  repeat (destruct l; allsimpl; cpx).
  generalize (isp (bterm [] n)) (isp (bterm [] n0)) (isp (bterm [] n1)); intros isp1 isp2 isp3.
  repeat (autodimp isp1 hyp).
  repeat (autodimp isp2 hyp).
  repeat (autodimp isp3 hyp).
  apply isprogram_bt_nobnd in isp1.
  apply isprogram_bt_nobnd in isp2.
  apply isprogram_bt_nobnd in isp3.
  exists n n0 n1; sp.
Qed.
