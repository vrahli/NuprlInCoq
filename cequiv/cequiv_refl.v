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

  Authors: Vincent Rahli

*)


Require Export cequiv.


Lemma mkc_refl_eq {p} :
  forall a b : @CTerm p,
    mkc_refl a = mkc_refl b
    -> a = b.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  eauto with pi.
Qed.

Lemma cequiv_mk_refl {o} :
  forall lib (t t' a : @NTerm o),
    computes_to_value lib t (mk_refl a)
    -> cequiv lib t t'
    -> {b : NTerm
        & computes_to_value lib t' (mk_refl b)
        # cequiv lib a b}.
Proof.
  prove_cequiv_mk.
Qed.

Lemma cequivc_mkc_refl {o} :
  forall lib (t t' a : @CTerm o),
    computes_to_valc lib t (mkc_refl a)
    -> cequivc lib t t'
    -> {b : CTerm
        & computes_to_valc lib t' (mkc_refl b)
        # cequivc lib a b}.
Proof.
  unfold computes_to_valc, cequivc; intros; destruct_cterms; allsimpl.
  generalize (cequiv_mk_refl lib x1 x0 x); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  rw @isprogram_refl in isp.
  exists (mk_cterm b isp); simpl; sp.
Qed.

Lemma lsubstc_mk_refl {o} :
  forall (t1  : @NTerm o)
         (sub : CSub)
         (w1  : wf_term t1)
         (w   : wf_term (mk_refl t1))
         (c1  : cover_vars t1 sub)
         (c   : cover_vars (mk_refl t1) sub),
    lsubstc (mk_refl t1) w sub c
    = mkc_refl (lsubstc t1 w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp.
Qed.

Lemma cover_vars_refl {o} :
  forall (a : @NTerm o) sub,
    cover_vars (mk_refl a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  autorewrite with slow in *; tcsp.
Qed.

Lemma covered_refl {o} :
  forall (a : @NTerm o) l,
    covered (mk_refl a ) l
    <=> covered a l.
Proof.
  unfold covered; simpl; introv.
  autorewrite with slow in *; tcsp.
Qed.

Lemma lsubstc_mk_refl_ex {o} :
  forall (t1  : @NTerm o)
         (sub : CSub)
         (w   : wf_term (mk_refl t1))
         (c   : cover_vars (mk_refl t1) sub),
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
     & lsubstc (mk_refl t1) w sub c
       = mkc_refl (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_refl in w; sp.

  duplicate c.
  rw @cover_vars_refl in c; sp.

  exists w c.
  apply lsubstc_mk_refl.
Qed.
