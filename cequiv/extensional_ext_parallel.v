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


Require Import approx_ext_star0.



Lemma extensional_ext_parallel {p} : extensional_op_ext (@NCan p NParallel).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  apply computes_to_val_like_in_max_k_steps_parallel_implies2 in Hcv; exrepnd; ginv.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  destruct lbt'; allsimpl; cpx.
  pose proof (Has 0) as h; autodimp h hyp; try omega.
  unfold selectbt in h; allsimpl.
  unfold blift_sub in h; exrepnd; destruct h1 as [h1|h1]; exrepnd; ginv.
  allapply @alpha_eq_bterm_nobnd; exrepnd; allunfold @nobnd; ginv.
  destruct b as [l t].
  apply alpha_eq_bterm_sym in h0; allapply @alpha_eq_bterm_nobnd; exrepnd; allunfold @nobnd; ginv.
  apply isprogram_parallel_implies in Hprt; exrepnd; ginv; allsimpl; cpx.
  apply isprogram_parallel_implies in Hprt'; exrepnd; ginv.

  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv3; auto.
  applydup @alphaeq_preserves_program in h2 as isp1.
  applydup @alphaeq_preserves_program in h4 as isp2.
  applydup isp1 in Hprt'2.
  applydup isp2 in Hprt2.

  pose proof (Hi a0 x nt2) as q.
  repeat (autodimp q hyp).
  { eauto 3 with slow. }

  assert (approx_ext_star lib x a1) as apr by eauto 3 with slow.

  repndors; exrepnd; subst; allsimpl.

  - apply howe_lemma2 in apr; auto; exrepnd.
    apply approx_ext_open_implies_approx_ext_star.
    apply approx_ext_implies_approx_ext_open.
    apply reduces_to_implies_approx_ext_eauto; prove_isprogram.
    apply (reduces_to_trans _ _ (mk_parallel (oterm (Can c) lbt') b0)).
    { apply reduces_to_prinarg; auto; destruct apr0; auto. }
    { apply reduces_to_if_step; reflexivity. }

  - apply isexc_implies in Hcv2; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in apr; auto; exrepnd.
    apply (approx_ext_star_open_trans _ _ (mk_exception a' e')).
    { apply approx_ext_star_exception; auto. }
    apply approx_ext_implies_approx_ext_open.
    apply reduces_to_implies_approx_ext_eauto; prove_isprogram.
    apply (reduces_to_trans _ _ (mk_parallel (mk_exception a' e') b0)).
    { apply reduces_to_prinarg; auto. }
    { apply reduces_to_if_step; reflexivity. }
Qed.
