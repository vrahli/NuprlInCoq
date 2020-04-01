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

  Authors: Vincent Rahli

*)


Require Export sequents.


Lemma hyps_functionality_ext_snoc {o} :
  forall uk lib (H : @bhyps o) h s t,
    in_ext lib (fun lib => forall t' s' w c c',
       equality uk lib t t' (lsubstc (htyp h) w s c)
       -> similarity uk lib s s' H
       -> eqtypes uk lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> hyps_functionality_ext uk lib s H
    -> hyps_functionality_ext uk lib (snoc s (hvar h, t)) (snoc H h).
Proof.
  introv imp hf ext sim.
  rw @similarity_snoc in sim; exrepnd; subst; cpx.
  rw @eq_hyps_snoc; simpl.

  assert (cover_vars (htyp h) s2a)
    as c
      by (clear sim1;
          allrw @cover_vars_covered; allapply @similarity_dom; exrepnd; allrw; sp;
          rw <- sim0; sp).

  exists s1a s2a t1 t2 w p c; sp; eauto 3 with slow.
  apply hf; auto.
Qed.

Lemma hyps_functionality_ext_snoc2 {o} :
  forall uk lib (H : @bhyps o) h s t v,
    in_ext lib (fun lib => forall t' s' w c c',
       equality uk lib t t' (lsubstc (htyp h) w s c)
       -> similarity uk lib s s' H
       -> eqtypes uk lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> hyps_functionality_ext uk lib s H
    -> v = hvar h
    -> hyps_functionality_ext uk lib (snoc s (v, t)) (snoc H h).
Proof.
  intros; subst.
  apply hyps_functionality_ext_snoc; sp.
Qed.

Lemma similarity_cover_vars2 {o} :
  forall uk lib (hs : @bhyps o) (s1 s2 s3 s4 : CSub) (t : NTerm),
    similarity uk lib s1 s2 hs
    -> similarity uk lib s3 s4 hs
    -> cover_vars t s1
    -> (cover_vars t s2 # cover_vars t s3 # cover_vars t s4).
Proof.
  introv sim1 sim2 cov.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim3 in cov; sp.
Qed.

Lemma similarity_cover_vars_upto2 {o} :
  forall uk lib (hs : @bhyps o) (s1 s2 s3 s4 : CSub) vs (t : NTerm),
    similarity uk lib s1 s2 hs
    -> similarity uk lib s3 s4 hs
    -> cover_vars_upto t (csub_filter s1 vs) vs
    -> (cover_vars_upto t (csub_filter s2 vs) vs
        # cover_vars_upto t (csub_filter s3 vs) vs
        # cover_vars_upto t (csub_filter s4 vs) vs).
Proof.
  introv sim1 sim2 cov.
  allapply @similarity_dom; repnd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  allrw.
  rw sim3 in cov; sp.
Qed.

Lemma cl_lsubst_var_snoc_not_in {o} :
  forall (v w : NVar) (u : @NTerm o) (s : Sub),
    cl_sub s
    -> closed u
    -> v <> w
    -> lsubst (mk_var v) (snoc s (w, u)) = lsubst (mk_var v) s.
Proof.
  introv cls clu d.
  repeat unflsubst; simpl.
  rw @sub_find_snoc.
  remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; auto.
  boolvar; tcsp.
Qed.
