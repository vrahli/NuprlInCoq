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


Require Export cequiv.


(* !!MOVE *)
Lemma not_value_like_approx_bot {o} :
  forall lib (a : @NTerm o),
    hasvalue_like lib a -> !approx lib a mk_bot.
Proof.
  introv hv ap.
  inversion ap as [cc]; subst.
  unfold close_comput in cc; repnd.
  unfold hasvalue_like, isvalue_like in hv; exrepnd.
  repndors.

  - apply iscan_implies in hv0; repndors; exrepnd; subst.

    + pose proof (cc2 c bterms) as h.
      autodimp h hyp.
      { split; auto.
        apply isvalue_iff; dands; auto.
        apply reduces_to_preserves_program in hv1; auto. }
      exrepnd.
      unfold computes_to_value in h1; repnd.
      apply not_bot_reduces_to_is_value_like in h2; eauto 3 with slow.

  - apply isexc_implies2 in hv0; exrepnd; subst.
    applydup @reduces_to_preserves_program in hv1; auto.
    apply isprogram_exception_implies in hv0; exrepnd; subst; fold_terms.

    pose proof (cc3 a0 t) as h.
    autodimp h hyp.
    exrepnd.
    apply not_bot_reduces_to_is_value_like in h0; eauto 3 with slow.
Qed.

Lemma not_value_like_approxc_bot {o} :
  forall lib (a : @CTerm o),
    hasvalue_likec lib a -> !approxc lib a mkc_bot.
Proof.
  unfold approxc, hasvalue_likec; introv; destruct_cterms; simpl.
  apply not_value_like_approx_bot.
Qed.

Lemma approxc_alphaeqc_r {o} :
  forall lib (a b c : @CTerm o),
    approxc lib a b
    -> alphaeqc b c
    -> approxc lib a c.
Proof.
  introv apr aeq.
  destruct_cterms; allunfold @approxc; allunfold @alphaeqc; allsimpl.
  eapply approx_alpha_rw_r_aux;[|exact apr]; auto.
Qed.

Lemma approxc_alphaeqc_l {o} :
  forall lib (a b c : @CTerm o),
    alphaeqc a b
    -> approxc lib b c
    -> approxc lib a c.
Proof.
  introv aeq apr.
  destruct_cterms; allunfold @approxc; allunfold @alphaeqc; allsimpl.
  eapply approx_alpha_rw_l_aux;[|exact apr]; eauto 3 with slow.
Qed.

Lemma hasvalue_like_exc {o} :
  forall lib (a b : @NTerm o),
    hasvalue_like lib (mk_exception a b).
Proof.
  introv.
  unfold hasvalue_like.
  exists (mk_exception a b); dands; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_like_exc : slow.

Lemma hasvalue_likec_exc {o} :
  forall lib (a b : @CTerm o),
    hasvalue_likec lib (mkc_exception a b).
Proof.
  introv; destruct_cterms; unfold hasvalue_likec; simpl; eauto 3 with slow.
Qed.
Hint Resolve hasvalue_likec_exc : slow.

Lemma approxc_decomp_axiom0 {o} :
  forall lib (a : @CTerm o),
    approxc lib mkc_axiom a
    <=> computes_to_valc lib a mkc_axiom.
Proof.
  introv; destruct_cterms; unfold approxc, computes_to_valc; simpl.
  rw @approx_decomp_axiom0.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_exception {o} :
  forall lib (a e v : @CTerm o),
    computes_to_valc lib (mkc_exception a e) v -> False.
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in comp; allsimpl.
  apply computes_to_value_exception in comp; sp.
Qed.

(* !!MOVE *)
Lemma approxc_exc_implies_ex {o} :
  forall lib (n e t : @CTerm o),
    approxc lib (mkc_exception n e) t
    -> {a : CTerm
        & {b : CTerm
        & reduces_toc lib t (mkc_exception a b)}}.
Proof.
  introv apr.
  destruct_cterms.
  unfold approxc in apr; allsimpl.
  inversion apr as [cl]; clear apr.
  unfold close_comput in cl; repnd.
  pose proof (cl3 x1 x0) as h.
  autodimp h hyp.
  { apply reduces_to_symm. }
  exrepnd.
  applydup @reduces_to_preserves_program in h0; eauto 3 with slow.
  allrw @isprogram_exception_iff; repnd.
  exists (mk_cterm a' h4) (mk_cterm e' h3).
  unfold reduces_toc; simpl; auto.
Qed.

Lemma cover_vars_exception {o} :
  forall (t u : @NTerm o) s,
    cover_vars (mk_exception t u) s <=> (cover_vars t s # cover_vars u s).
Proof.
  introv.
  allrw @cover_vars_eq.
  simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.
