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


Require Import approx_star0.


Lemma extensional_ldepth {p} : extensional_op (@NCan p NLDepth).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_ldepth_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_ldepth_implies in Hprt'; exrepnd; subst; cpx.

  apply computes_to_val_like_in_max_k_steps_S in Hcv; exrepnd.
  csunf Hcv1; simpl in *; ginv.
  apply computes_to_val_like_in_max_k_steps_if_isvalue_like in Hcv0; eauto 2 with slow; subst.
  eapply approx_star_open_trans;
    [|apply reduces_to_implies_approx_open1;[|apply reduces_to_if_step;csunf;simpl;auto] ];
    eauto 2 with slow.
Qed.
