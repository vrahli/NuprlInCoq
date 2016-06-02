(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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

  Authors: Vincent Rahli

*)

Require Export cequiv.

Lemma bcequiv_refl {o} :
  forall lib (b : @BTerm o),
    wf_bterm b
    -> bcequiv lib b b.
Proof.
  introv wf.
  destruct b as [l t].
  allrw @wf_bterm_iff.
  apply blift_approx_cequiv.
  - unfold approx_open_bterm, blift.
    exists l t t; dands; eauto 3 with slow.
  - unfold approx_open_bterm, blift.
    exists l t t; dands; eauto 3 with slow.
Qed.

Lemma bcequiv_nobnd {o} :
  forall lib (t u : @NTerm o),
    wf_term t
    -> wf_term u
    -> cequiv lib t u
    -> bcequiv lib (nobnd t) (nobnd u).
Proof.
  introv wft wfu ceq.
  applydup @cequiv_sym in ceq.
  apply cequiv_le_approx in ceq.
  apply cequiv_le_approx in ceq0.
  apply blift_approx_cequiv.
  - unfold approx_open_bterm, blift.
    exists ([] : list NVar) t u; dands; eauto 3 with slow.
    apply approx_implies_approx_open; auto.
  - unfold approx_open_bterm, blift.
    exists ([] : list NVar) u t; dands; eauto 3 with slow.
    apply approx_implies_approx_open; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
