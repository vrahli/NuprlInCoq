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

Require Export cvterm.
Require Export continuity_defs.
(*Require Export per_props3.*)
Require Export per_props_nat.


Definition force_int_f_c {o} v (f : @CTerm o) :=
  mkc_lam v (mkcv_cbv
               [v]
               (force_int_cv [v] (mkc_var v))
               v
               (mkcv_apply [v,v] (mk_cv [v,v] f) (mk_cv_app_r [v] [v] (mkc_var v)))).

Definition force_int_F_c {o} v (F f : @CTerm o) :=
  mkc_apply F (force_int_f_c v f).

Definition absolute_value_cv {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  mkcv_less vs t (mkcv_zero vs) (mkcv_minus vs t) t.

Definition less_bound_cv {o} vs b (t e : @CVTerm o vs) : CVTerm vs :=
  mkcv_less vs (absolute_value_cv vs t) (mkcv_nat vs b) t e.

Definition force_int_bound_cv {o} vs v b (t e : @CVTerm o vs) : CVTerm vs :=
  mkcv_cbv
    vs t v
    (less_bound_cv
       (v :: vs)
       b
       (mk_cv_app_r vs [v] (mkc_var v))
       (mk_cv_app_l [v] vs e)).

Definition force_int_bound_f_c {o} v b (f e : @CTerm o) :=
  mkc_lam v (mkcv_cbv
               [v]
               (force_int_bound_cv [v] v b (mkc_var v) (mk_cv [v] e))
               v
               (mkcv_apply
                  [v,v]
                  (mk_cv [v,v] f)
                  (mk_cv_app_r [v] [v] (mkc_var v)))).

Definition force_int_bound_F_c {o} v b (F f e : @CTerm o) :=
  mkc_apply F (force_int_bound_f_c v b f e).

Lemma get_cterm_force_int_f_c {o} :
  forall x (f : @CTerm o),
    get_cterm (force_int_f_c x f)
    = force_int_f x (get_cterm f).
Proof.
  introv; destruct_cterms; simpl; auto.
Qed.

Lemma get_cterm_force_int_F_c {o} :
  forall x (F f : @CTerm o),
    get_cterm (force_int_F_c x F f)
    = force_int_F x (get_cterm F) (get_cterm f).
Proof.
  introv; destruct_cterms; simpl; auto.
Qed.

Lemma get_cterm_force_int_bound_F_c {o} :
  forall x b (F f e : @CTerm o),
    get_cterm (force_int_bound_F_c x b F f e)
    = force_int_bound_F x b (get_cterm F) (get_cterm f) (get_cterm e).
Proof.
  introv; destruct_cterms; simpl; auto.
Qed.

Definition agree_upto_bc {o} lib b (f g : @CTerm o) :=
  forall (i : Z),
    Z.abs_nat i < b
    -> equality_of_int_tt
         lib
         (mkc_apply f (mkc_integer i))
         (mkc_apply g (mkc_integer i)).

Lemma get_cterm_apply {o} :
  forall (a b : @CTerm o),
    get_cterm (mkc_apply a b) = mk_apply (get_cterm a) (get_cterm b).
Proof.
  introv; destruct_cterms; sp.
Qed.

Lemma agree_upto_b_get_cterm {o} :
  forall lib b (f g : @CTerm o),
    agree_upto_bc lib b f g
    -> agree_upto_b lib b (get_cterm f) (get_cterm g).
Proof.
  introv agree l.
  pose proof (agree i l) as h.
  unfold equality_of_int_tt in h; exrepnd.
  allunfold @computes_to_valc; allsimpl.
  allrw @get_cterm_apply; allsimpl.
  allunfold @computes_to_value; repnd.
  exists k; dands; auto.
Qed.
Hint Resolve agree_upto_b_get_cterm : slow.

(* Assume [agree_upto_red_bc] and prove that it implies [agree_upto_bc] *)

Definition agree_upto_red_bc {o} lib b (f g : @CTerm o) :=
  forall (t1 t2 : CTerm) (i : Z),
    reduces_toc lib t1 (mkc_integer i)
    -> reduces_toc lib t2 (mkc_integer i)
    -> Z.abs_nat i < b
    -> equality_of_int_tt lib (mkc_apply f t1) (mkc_apply g t2).

Definition continuous {o} lib (F : @CTerm o) :=
  forall f,
    member lib f (mkc_fun mkc_int mkc_int)
    -> {b : nat
        & forall g,
            member lib g (mkc_fun mkc_int mkc_int)
            -> agree_upto_red_bc lib b f g
            -> equality_of_int_tt lib (mkc_apply F f) (mkc_apply F g)}.

Lemma reduces_toc_refl {o} :
  forall lib (t : @CTerm o),
    reduces_toc lib t t.
Proof.
  introv; unfold reduces_toc; simpl; eauto with slow.
Qed.
Hint Resolve reduces_toc_refl : slow.

Lemma equality_force_int_f_c {o} :
  forall lib (f : @CTerm o),
    member lib f (mkc_fun mkc_int mkc_int)
    -> equality lib f (force_int_f_c nvarx f) (mkc_fun mkc_int mkc_int).
Proof.
  introv m.
  allrw @equality_in_fun; repnd; dands; auto.
  introv e.
  pose proof (m a a' e) as h.
  eapply equality_trans;[exact h|].

  allrw @equality_in_int.
  allunfold @equality_of_int.
  exrepnd.
  exists k0; dands; spcast; auto.

  unfold computes_to_valc.
  rw @get_cterm_apply.
  rw @get_cterm_force_int_f_c.
  simpl.

  unfold computes_to_value; dands; eauto with slow.
  unfold force_int_f.

  apply (reduces_to_if_split2
           _ _ (mk_cbv
                  (force_int (get_cterm a'))
                  nvarx
                  (mk_apply (get_cterm f) (mk_var nvarx)))).

  { csunf; simpl; unfold apply_bterm, lsubst; simpl; boolvar;
    allrw @free_vars_cterm; allsimpl; tcsp;
    allrw @lsubst_aux_nil; tcsp;
    try (complete (provefalse; sp)). }

  pose proof (reduces_to_prinarg
                lib NCbv (force_int (get_cterm a')) (mk_integer k)
                [bterm [nvarx] (mk_apply (get_cterm f) (mk_var nvarx))]) as h.
  autodimp h hyp; fold_terms.
  { allunfold @computes_to_valc; allsimpl.
    allunfold @computes_to_value; sp.
    pose proof (reduces_to_prinarg
                  lib (NArithOp ArithOpAdd) (get_cterm a') (mk_integer k)
                  [bterm [] mk_zero]) as h.
    autodimp h hyp; fold_terms.
    eapply reduces_to_trans;[exact h|clear h].
    apply reduces_to_if_step; csunf; simpl.
    dcwf h; allsimpl.
    rw <- Zplus_0_r_reverse; auto.
  }

  eapply reduces_to_trans;[exact h|clear h].

  apply (reduces_to_if_split2
           _ _ (mk_apply (get_cterm f) (mk_integer k))).

  { csunf; simpl; unfold apply_bterm, lsubst; simpl; boolvar; tcsp;
    try (complete (provefalse; sp)).
    rw @lsubst_aux_trivial_cl_term2; eauto with slow. }

  pose proof (m a' (mkc_integer k)) as q.
  autodimp q hyp.

  { apply equality_in_int.
    unfold equality_of_int.
    exists k; dands; spcast; eauto with slow. }

  apply equality_in_int in q.
  apply equality_of_int_imp_tt in q.
  unfold equality_of_int_tt in q; exrepnd.
  unfold computes_to_valc in q0; allsimpl.
  unfold computes_to_value in q0; repnd.
  allrw @get_cterm_apply; allsimpl.
  repeat computes_to_eqval; auto.
Qed.

Lemma agree_upto_c_iff {o} :
  forall lib b (f g : @CTerm o),
    member lib f (mkc_fun mkc_int mkc_int)
    -> member lib g (mkc_fun mkc_int mkc_int)
    -> (agree_upto_red_bc lib b f g
        <=> agree_upto_bc lib b f g).
Proof.
  introv mf mg.

  rw @equality_in_fun in mf.
  rw @equality_in_fun in mg.
  repnd.
  clear mf0 mg0 mf1 mg1.

  split; intro agree.

  - unfold agree_upto_bc; introv l.
    unfold agree_upto_red_bc in agree.
    pose proof (agree (mkc_integer i) (mkc_integer i) i) as h.
    repeat (autodimp h hyp); unfold reduces_toc; eauto with slow.

  - unfold agree_upto_red_bc; introv r1 r2 l.
    unfold agree_upto_bc in agree.
    pose proof (agree i l) as h; exrepnd.

    pose proof (mf t1 (mkc_integer i)) as k1.
    autodimp k1 hyp.
    { apply equality_in_int.
      unfold equality_of_int.
      exists i; dands; spcast;
      apply computes_to_valc_iff_reduces_toc;
      dands; eauto with slow. }

    pose proof (mg t2 (mkc_integer i)) as k2.
    autodimp k2 hyp.
    { apply equality_in_int.
      unfold equality_of_int.
      exists i; dands; spcast;
      apply computes_to_valc_iff_reduces_toc;
      dands; eauto with slow. }

    allrw @equality_in_int.
    allapply @equality_of_int_imp_tt.
    allunfold @equality_of_int_tt; exrepnd.
    repeat computes_to_eqval.

    eexists; eauto.
Qed.
