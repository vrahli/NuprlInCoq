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


Require Import sequents_tacs.
Require Export per_props_equality.


Lemma subtype_equality {o} :
  forall lib (t1 t2 : @CTerm o) T U s s' wt wu ct cu H x wc,
    !LIn x (vars_hyps H)
    -> !LIn x (free_vars U)
    -> cover_vars U s
    -> cover_vars T s
    -> similarity lib s s' H
    -> hyps_functionality lib (snoc s (x, t1)) (snoc H (mk_hyp x T))
    -> equality lib t1 t2 (lsubstc T wt s ct)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent (snoc H (mk_hyp x T))
                           (mk_conclax (mk_member (mk_var x) U)))
            wc)
    -> equality lib t1 t2 (lsubstc U wu s cu).
Proof.
  
  introv nixh nixu cvu cvt sim hf eq seqt.
  vr_seq_true in seqt.

  generalize (seqt (snoc s (x, t1)) (snoc s' (x, t2))); intro i.
  repeat (autodimp i hyp); exrepnd.
  assert (similarity lib (snoc s (hvar (mk_hyp x T), t1))
                     (snoc s' (hvar (mk_hyp x T), t2))
                     (snoc H (mk_hyp x T))); try (complete (allsimpl; sp)).

  apply sim_cons with (w := wt) (p := ct); sp.

  ai_lsubst_tac.

  rw @member_eq in i1.
  rw <- @member_member_iff in i1.
  allrw <- @fold_mkc_member.
  unfold member in i1.

  apply @equality_commutes3 with (a3 := t2) (a4 := t2) (U := lsubstc U wu s' c) in i1; sp.
Qed.

Lemma subtype_tequality {o} :
  forall lib (s1 s2 : @CSub o) H T U x t t' wt wu ct1 cu1 cu2 wc,
    !LIn x (vars_hyps H)
    -> !LIn x (free_vars U)
    -> equality lib t t' (lsubstc T wt s1 ct1)
    -> hyps_functionality lib (snoc s1 (x, t)) (snoc H (mk_hyp x T))
    -> similarity lib s1 s2 H
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent (snoc H (mk_hyp x T))
                           (mk_conclax (mk_member (mk_var x) U)))
            wc)
    -> tequality lib (lsubstc U wu s1 cu1) (lsubstc U wu s2 cu2).
Proof.
  introv nixh nixu eqt hf sim seqt.

  vr_seq_true in seqt.

  generalize (seqt (snoc s1 (x, t)) (snoc s2 (x, t'))); clear seqt; intro seqt.
  repeat (autodimp seqt hyp); exrepnd.

  rw @similarity_snoc; simpl.
  exists s1 s2 t t' wt ct1; sp.

  ai_lsubst_tac.
  rw @tequality_mkc_member in seqt0; sp.
Qed.

Lemma hyps_functionality_widening {o} :
  forall lib (s1 s2 : @CSub o) x y z t t' T U H w c wc,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !(x = y)
    -> !LIn x (free_vars U)
    -> !LIn y (free_vars U)
    -> equality lib t t' (lsubstc T w s1 c)
    -> hyps_functionality lib (snoc s1 (x, t)) (snoc H (mk_hyp x T))
    -> similarity lib s1 s2 H
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent (snoc H (mk_hyp x T))
                           (mk_conclax (mk_member (mk_var x) U)))
            wc)
    -> hyps_functionality lib (snoc (snoc (snoc s1 (x, t)) (y, t)) (z, mkc_axiom))
                          (snoc (snoc (snoc H (mk_hyp x T)) (mk_hyp y U))
                                (mk_hyp z (mk_equality (mk_var x) (mk_var y) U))).
Proof.
  introv nixh niyh nxy nixu niyu eqt hf simh seqt.
  introv sim.

  rw @similarity_snoc in sim; exrepnd; allsimpl; cpx.
  rw @similarity_snoc in sim3; exrepnd; allsimpl; cpx.

  generalize (hf s2a0); intro i.
  autodimp i h.

  assert (cover_vars (mk_equality (mk_var x) (mk_var y) U) (snoc s2a0 (y, t0)))
    as c2
      by (apply @cover_vars_dom_csub_eq with (s1 := snoc (snoc s1 (x, t1)) (y, t1)); sp;
          allrw @dom_csub_snoc; simpl;
          allapply @similarity_dom; repd; allrw; sp;
          allrw @vars_hyps_snoc; simpl; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc (snoc s1 (x, t1)) (y, t1)) (snoc s2a0 (y, t0))
         (@mkc_axiom o) t2
         w0 p c2; sp.

  assert (cover_vars U s2a0)
    as c3
      by (apply @cover_vars_dom_csub_eq with (s1 := snoc s1 (x, t1)); sp;
          allrw @dom_csub_snoc; simpl;
          allapply @similarity_dom; repd; allrw; sp;
          allrw @vars_hyps_snoc; simpl; sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1 (x, t1)) s2a0 t1 t0 w1 p0 c3; sp.

  rw @eq_hyps_snoc in i; exrepnd; allsimpl; cpx.
  ai_lsubst_tac.

  generalize (subtype_tequality lib s1a s2a H T U x t3 t' w w1 c c4 c5 wc); intro i.
  repeat (autodimp i hyp).

  allrw @similarity_snoc; exrepnd; allsimpl; cpx.
  allrw @similarity_snoc; exrepnd; simphyps; cpx; clear_irr.

  lsubst_tac.

  generalize (subtype_equality lib t3 t4 T U s1a s2a w w1 c c6 H x wc); intro j;
  repeat (autodimp j hyp).

  generalize (subtype_tequality lib s1a s2a H T U x t3 t' w w1 c c6 c9 wc); intro k;
  repeat (autodimp k hyp).
  revert k. revert j. revert sim2. generalize (lsubstc U w1 s1a c6). generalize (lsubstc U w1 s2a c9).
  intros.

  apply tequality_mkc_equality;  sp; split; sp.
  - apply @equality_refl with (t2 := t3); sp; apply equality_sym; auto.
  - apply @equality_refl with (t2 := t4); sp; apply equality_sym; auto.
  - apply @equality_refl with (t2 := t3); sp; apply equality_sym; auto.
  - apply @equality_refl with (t2 := t4); sp; apply equality_sym; auto.
 
Qed.

Lemma similarity_widening {o} :
  forall lib (s1 s2 : @CSub o) x y z t t1 t2 T U H wt wu ct cu,
    !LIn x (free_vars U)
    -> !LIn y (free_vars U)
    -> !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !(x = y)
    -> equality lib t t1 (lsubstc T wt s1 ct)
    -> equality lib t t2 (lsubstc U wu s1 cu)
    -> similarity lib s1 s2 H
    -> similarity lib (snoc (snoc (snoc s1 (x, t)) (y, t)) (z, mkc_axiom))
                  (snoc (snoc (snoc s2 (x, t1)) (y, t2)) (z, mkc_axiom))
                  (snoc (snoc (snoc H (mk_hyp x T)) (mk_hyp y U))
                        (mk_hyp z (mk_equality (mk_var x) (mk_var y) U))).
Proof.
  introv nixu niyu nixh niyh nxy eqt equ sim.

  assert (wf_term (mk_equality (mk_var x) (mk_var y) U))
    as wfe by (rw <- @wf_equality_iff; sp).

  assert (cover_vars (mk_equality (mk_var x) (mk_var y) U)
                     (snoc (snoc s1 (x, t)) (y, t)))
    as cvu1.
  rw @cover_vars_equality; sp.
  apply cover_vars_snoc_weak; apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp.
  apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp.
  apply cover_vars_snoc_weak; apply cover_vars_snoc_weak; sp.

  rw @similarity_snoc; simpl.
  exists (snoc (snoc s1 (x, t)) (y, t))
         (snoc (snoc s2 (x, t1)) (y, t2))
         (@mkc_axiom o)
         (@mkc_axiom o)
         wfe cvu1; sp.

  assert (cover_vars U (snoc s1 (x, t)))
    as cvu2 by (apply cover_vars_snoc_weak; sp).

  rw @similarity_snoc; simpl.
  exists (snoc s1 (x, t)) (snoc s2 (x, t1)) t t2 wu cvu2; sp.

  rw @similarity_snoc; simpl.
  exists s1 s2 t t1 wt ct; sp.

  ai_lsubst_tac; sp.

  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.
  apply equality_refl in equ; sp.
Qed.

Lemma strong_subtype_equality {o} :
  forall lib (s1 s2 : @CSub o) t t1 t2 T U wt wu ct1 cu1 ct2 H x y z ws1 ws2 ,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !x = y
    -> !LIn x (free_vars T)
    -> !LIn x (free_vars U)
    -> !LIn y (free_vars T)
    -> !LIn y (free_vars U)
    -> !LIn z (free_vars T)
    -> !LIn z (free_vars U)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent (snoc H (mk_hyp x T))
                           (mk_conclax (mk_member (mk_var x) U)))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x T)) (mk_hyp y U))
                     (mk_hyp z (mk_equality (mk_var x) (mk_var y) U)))
               (mk_conclax (mk_equality (mk_var x) (mk_var y) T)))
            ws2)
    -> equality lib t t1 (lsubstc T wt s1 ct1)
    -> equality lib t t2 (lsubstc U wu s1 cu1)
    -> hyps_functionality lib (snoc s1 (x, t)) (snoc H (mk_hyp x T))
    -> similarity lib s1 s2 H
    -> tequality lib (mkc_equality t t (lsubstc T wt s1 ct1))
                 (mkc_equality t1 t2 (lsubstc T wt s2 ct2))
       # member lib t (lsubstc T wt s1 ct1).
Proof.
  introv nixh niyh nxy nixt nixu niyt niyu nizt nizu.
  introv seqt1 seqt2 eqt equ hf sim.

  vr_seq_true in seqt2.

  generalize (seqt2 (snoc (snoc (snoc s1 (x,t)) (y, t)) (z, mkc_axiom))
                    (snoc (snoc (snoc s2 (x,t1)) (y, t2)) (z, mkc_axiom)));
    clear seqt2; intro seqt2.
  autodimp seqt2 hyp.

  generalize (hyps_functionality_widening lib s1 s2 x y z t t1 T U H wt ct1 ws1);
    intro h; repeat (autodimp h hyp).

  autodimp seqt2 hyp.

  generalize (similarity_widening lib s1 s2 x y z t t1 t2 T U H wt wu ct1 cu1);
    intro h; repeat (autodimp h hyp).

  exrepnd.

  lsubst_tac.

  rw @member_eq in seqt2.
  rw <- @member_equality_iff in seqt2.
  rw @member_eq in seqt2.
  sp.
Qed.


(** This is saying that if the sequent
 *        H, x : Base, y : Base |- (R x y) in Type(i)
 * is true, then
 *        (R[s1] x0 y0 in Type(i)) = (R[s2] x0 y0 in Type(i))
 * and
 *        (R[s1] x0 y0 in Type(i)
 *)
Lemma membership_apply2 {o} :
  forall lib (H : @bhyps o) R x y i s1 s2 w c1 c2 ws,
    sequent_true lib
      (mk_wcseq
         (mk_baresequent
            (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
            (mk_conclax (mk_member (mk_apply2 R (mk_var x) (mk_var y)) (mk_uni i))))
         ws)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> !LIn x (free_vars R)
    -> !LIn y (free_vars R)
    -> !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !(x = y)
    -> forall x0 y0,
         tequality lib
           (mkc_member (mkc_apply2 (lsubstc R w s1 c1) x0 y0) (mkc_uni i))
           (mkc_member (mkc_apply2 (lsubstc R w s2 c2) x0 y0) (mkc_uni i))
         # member lib (mkc_apply2 (lsubstc R w s1 c1) x0 y0) (mkc_uni i).
Proof.
  introv seqt hf sim nixr niyr nixh niyh nxy.
  introv.

  assert (!LIn y (dom_csub s1))
    as niys1 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn y (dom_csub s2))
    as niys2 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn x (dom_csub s1))
    as nixs1 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn x (dom_csub s2))
    as nixs2 by (allapply @similarity_dom; repnd; allrw; sp).

  vr_seq_true in seqt.
  generalize (seqt (snoc (snoc s1 (x, x0)) (y, y0))
                   (snoc (snoc s2 (x, x0)) (y, y0))); clear seqt; intro seqt.
  repeat (autodimp seqt hyp); exrepnd.
  (* hyps_functionality *)
  generalize (hyps_functionality_snoc lib
                (snoc H (mk_hyp x mk_base))
                (mk_hyp y mk_base)
                (snoc s1 (x, x0))
                y0); simpl; intro p.
  apply p; try (complete sp).
  introv eq s; lift_lsubst; sp; try (apply tequality_base).
  generalize (hyps_functionality_snoc lib H (mk_hyp x mk_base) s1 x0); simpl; intro q.
  apply q; try (complete sp).
  introv eq s; lift_lsubst; sp; try (apply tequality_base).
  (* similarity *)
  apply similarity_snoc; simpl.
  exists (snoc s1 (x, x0)) (snoc s2 (x, x0)) y0 y0 (@wf_base o)
         (cover_vars_base (snoc s1 (x, x0))); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).
  apply similarity_snoc; simpl.
  exists s1 s2 x0 x0 (@wf_base o) (cover_vars_base s1); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  lsubst_tac.
  rw @member_eq in seqt1.
  rw <- @member_member_iff in seqt1; sp.
Qed.

Lemma implies_inhabited_apply2_all {o} :
  forall lib (H : @bhyps o) x y z R1 R2 i e s1 s2 w1 w2 c1 c2 ws1 ws2,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn x (free_vars R1)
    -> !LIn y (free_vars R1)
    -> !LIn z (free_vars R1)
    -> !LIn x (free_vars R2)
    -> !LIn y (free_vars R2)
    -> !LIn z (free_vars R2)
    -> !(x = y)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R1 (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R2 (mk_var x) (mk_var y)) e))
            ws2)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> forall x0 y0,
         inhabited_type lib (mkc_apply2 (lsubstc R1 w1 s1 c1) x0 y0)
         -> inhabited_type lib (mkc_apply2 (lsubstc R2 w2 s1 c2) x0 y0).
Proof.
  introv nixh niyh nixr1 niyr1 nizr1 nixr2 niyr2 nizr2 nxy.
  introv seqt1 seqt2 hf sim inh.

  vr_seq_true in seqt2.

  unfold inhabited_type in inh; exrepnd.

  generalize (seqt2 (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, t))
                    (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (z, t)));
    clear seqt2; intro seqt2.
  repeat (autodimp seqt2 hyp); exrepnd.

  (* hyps_functionality *)
  generalize (hyps_functionality_snoc lib
                (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
                (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y)))
                (snoc (snoc s1 (x, x0)) (y, y0))
                t); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lift_lsubst; lift_lsubst in eq.
  rw @similarity_snoc in s; simpl in s; exrepnd; cpx.
  rw @similarity_snoc in s5; simpl in s5; exrepnd; cpx.

  lsubst_tac.
  allrw @equality_in_base_iff.

  generalize (membership_apply2 lib H R1 x y i s1a s2a0 w1 c1 c11 ws1);
    intro q; repeat (destimp q hyp).
  generalize (q t0 t1); clear q; intro q; repnd.

  spcast.
  generalize (implies_cequivc_apply2 lib
                (lsubstc R1 w1 s2a0 c11)
                (lsubstc R1 w1 s2a0 c11)
                t3 t2 t0 t1);
    intro ceq; repeat (autodimp ceq hyp); try (complete (apply cequivc_sym; auto)).

  apply tequality_in_uni_implies_tequality in q0; sp.
  pose proof (tequality_in_uni_implies_tequality lib).
  spcast; apply tequality_respects_cequivc_right with (T2 := mkc_apply2 (lsubstc R1 w1 s2a0 c11) t0 t1); sp.
  apply cequivc_sym; sp.
  
  generalize (hyps_functionality_snoc lib
                (snoc H (mk_hyp x mk_base))
                (mk_hyp y mk_base)
                (snoc s1 (x, x0))
                y0); simpl; intro p.
  apply p; try (complete sp).
  introv eq; lift_lsubst; sp; try (apply tequality_base).
  generalize (hyps_functionality_snoc lib H (mk_hyp x mk_base) s1 x0); simpl; intro q.
  apply q; try (complete sp).
  introv eq; lift_lsubst; sp; try (apply tequality_base).

  (* similarity *)

  assert (wf_term (mk_apply2 R1 (mk_var x) (mk_var y)))
    as wfap by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R1 (mk_var x) (mk_var y))
                     (snoc (snoc s1 (x, x0)) (y, y0)))
    as cvap
      by (apply @cover_vars_apply2; sp;
          try (apply @cover_vars_var);
          repeat (apply @cover_vars_snoc_weak); sp;
          repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  apply similarity_snoc; simpl.
  exists (snoc (snoc s1 (x, x0)) (y, y0))
         (snoc (snoc s2 (x, x0)) (y, y0))
         t t
         wfap cvap; sp.
  apply similarity_snoc; simpl.
  exists (snoc s1 (x, x0)) (snoc s2 (x, x0)) y0 y0 (@wf_base o)
         (cover_vars_base (snoc s1 (x, x0))); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).
  apply similarity_snoc; simpl.
  exists s1 s2 x0 x0 (@wf_base o) (cover_vars_base s1); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  lsubst_tac.
  rw @member_eq; sp.

  lsubst_tac.
  apply inhabited_type_if_equality in seqt2; sp.
Qed.

Lemma implies_inhabited_apply2 {o} :
  forall lib (H : @bhyps o) x y z x0 y0 R1 R2 i e s1 s2 w1 w2 c1 c2 ws1 ws2,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn x (free_vars R1)
    -> !LIn y (free_vars R1)
    -> !LIn z (free_vars R1)
    -> !LIn x (free_vars R2)
    -> !LIn y (free_vars R2)
    -> !LIn z (free_vars R2)
    -> !(x = y)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R1 (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R2 (mk_var x) (mk_var y)) e))
            ws2)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> inhabited_type lib (mkc_apply2 (lsubstc R1 w1 s1 c1) x0 y0)
    -> inhabited_type lib (mkc_apply2 (lsubstc R2 w2 s1 c2) x0 y0).
Proof.
  intros.
  generalize (implies_inhabited_apply2_all lib
                H x y z R1 R2 i e s1 s2 w1 w2 c1 c2 ws1 ws2); sp.
Qed.

Lemma implies_sym_type {o} :
  forall lib (H : @bhyps o) x y z R1 R2 i e1 e2 s1 s2 w1 w2 c1 c2 ws1 ws2 ws3 ws4,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn x (free_vars R1)
    -> !LIn y (free_vars R1)
    -> !LIn z (free_vars R1)
    -> !LIn x (free_vars R2)
    -> !LIn y (free_vars R2)
    -> !LIn z (free_vars R2)
    -> !(x = y)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R1 (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R2 (mk_var x) (mk_var y)) (mk_uni i))))
            ws2)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R2 (mk_var x) (mk_var y)) e1))
            ws3)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R2 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R1 (mk_var x) (mk_var y)) e2))
            ws4)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> sym_type lib (lsubstc R1 w1 s1 c1)
    -> sym_type lib (lsubstc R2 w2 s1 c2).
Proof.
  introv nixh niyh nixr1 niyr1 nizr1 nixr2 niyr2 nizr2 nxy.
  introv seqt1 seqt2 seqt3 seqt4 hf sim sym.
  allunfold @sym_type.
  introv inh.
  generalize (implies_inhabited_apply2_all lib
                H x y z R2 R1 i e2 s1 s2 w2 w1 c2 c1 ws2 ws4
                nixh niyh nixr2 niyr2 nizr2 nixr1 niyr1 nizr1 nxy
                seqt2 seqt4 hf sim
                x0 y0 inh).
  intro inh2.
  apply sym in inh2.
  generalize (implies_inhabited_apply2_all lib
                H x y z R1 R2 i e1 s1 s2 w1 w2 c1 c2 ws1 ws3
                nixh niyh nixr1 niyr1 nizr1 nixr2 niyr2 nizr2 nxy
                seqt1 seqt3 hf sim
                y0 x0 inh2); sp.
Qed.

Lemma implies_trans_type {o} :
  forall lib (H : @bhyps o) x y z R1 R2 i e1 e2 s1 s2 w1 w2 c1 c2 ws1 ws2 ws3 ws4,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn x (free_vars R1)
    -> !LIn y (free_vars R1)
    -> !LIn z (free_vars R1)
    -> !LIn x (free_vars R2)
    -> !LIn y (free_vars R2)
    -> !LIn z (free_vars R2)
    -> !(x = y)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R1 (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R2 (mk_var x) (mk_var y)) (mk_uni i))))
            ws2)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R2 (mk_var x) (mk_var y)) e1))
            ws3)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R2 (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R1 (mk_var x) (mk_var y)) e2))
            ws4)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> trans_type lib (lsubstc R1 w1 s1 c1)
    -> trans_type lib (lsubstc R2 w2 s1 c2).
Proof.
  introv nixh niyh nixr1 niyr1 nizr1 nixr2 niyr2 nizr2 nxy.
  introv seqt1 seqt2 seqt3 seqt4 hf sim trans.
  allunfold @trans_type.
  introv inh1 inh2.
  generalize (implies_inhabited_apply2_all lib
                H x y z R2 R1 i e2 s1 s2 w2 w1 c2 c1 ws2 ws4
                nixh niyh nixr2 niyr2 nizr2 nixr1 niyr1 nizr1 nxy
                seqt2 seqt4 hf sim
                x0 y0 inh1).
  intro inh1'.
  generalize (implies_inhabited_apply2_all lib
                H x y z R2 R1 i e2 s1 s2 w2 w1 c2 c1 ws2 ws4
                nixh niyh nixr2 niyr2 nizr2 nixr1 niyr1 nizr1 nxy
                seqt2 seqt4 hf sim
                y0 z0 inh2).
  intro inh2'.
  generalize (trans x0 y0 z0 inh1' inh2'); intro inh.
  generalize (implies_inhabited_apply2_all lib
                H x y z R1 R2 i e1 s1 s2 w1 w2 c1 c2 ws1 ws3
                nixh niyh nixr1 niyr1 nizr1 nixr2 niyr2 nizr2 nxy
                seqt1 seqt3 hf sim
                x0 z0 inh); sp.
Qed.

Lemma is_sym_type {o} :
  forall lib R (H : @bhyps o) i x y z e s1 s2 w c ws1 ws2,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn x (free_vars R)
    -> !LIn y (free_vars R)
    -> !LIn z (free_vars R)
    -> !(x = y)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc (snoc H (mk_hyp x mk_base))
                           (mk_hyp y mk_base))
                     (mk_hyp z (mk_apply2 R (mk_var x) (mk_var y))))
               (mk_concl (mk_apply2 R (mk_var y) (mk_var x)) e))
            ws2)
    -> similarity lib s1 s2 H
    -> hyps_functionality lib s1 H
    -> sym_type lib (lsubstc R w s1 c).
Proof.
  introv nixh niyh nixr niyr nizr nxy.
  introv seqt1 seqt2 sim hf inh.

  unfold inhabited_type in inh; exrepnd.

  vr_seq_true in seqt2.

  generalize (seqt2 (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, t))
                    (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (z, t)));
    clear seqt2; intro seqt2.
  repeat (autodimp seqt2 hyp); exrepnd.

  (* hyps_functionality *)

  generalize (hyps_functionality_snoc lib
                (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
                (mk_hyp z (mk_apply2 R (mk_var x) (mk_var y)))
                (snoc (snoc s1 (x, x0)) (y, y0))
                t); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lift_lsubst; lift_lsubst in eq.
  rw @similarity_snoc in s; simpl in s; exrepnd; cpx.
  rw @similarity_snoc in s5; simpl in s5; exrepnd; cpx.

  lsubst_tac.
  allrw @equality_in_base_iff.

  generalize (membership_apply2 lib H R x y i s1a s2a0 w c c10 ws1);
    intro q; repeat (destimp q hyp).
  generalize (q t0 t1); clear q; intro q; repnd.

  spcast.
  generalize (implies_cequivc_apply2 lib
                (lsubstc R w s2a0 c10)
                (lsubstc R w s2a0 c10)
                t3 t2 t0 t1);
    intro ceq; repeat (autodimp ceq hyp); try (complete (apply cequivc_sym; auto)).

  lsubst_tac.
  apply tequality_in_uni_implies_tequality in q0; sp.
  apply tequality_respects_cequivc_right with (T2 := mkc_apply2 (lsubstc R w s2a0 c10) t0 t1); sp.
  apply cequivc_sym; sp.

  generalize (hyps_functionality_snoc lib
                (snoc H (mk_hyp x mk_base))
                (mk_hyp y mk_base)
                (snoc s1 (x, x0))
                y0); simpl; intro p.
  apply p; try (complete sp).
  introv eq; lift_lsubst; sp; try (apply tequality_base).
  generalize (hyps_functionality_snoc lib H (mk_hyp x mk_base) s1 x0); simpl; intro q.
  apply q; try (complete sp).
  introv eq; lift_lsubst; sp; try (apply tequality_base).

  (* similarity *)

  assert (wf_term (mk_apply2 R (mk_var x) (mk_var y)))
    as wfap by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var y))
                     (snoc (snoc s1 (x, x0)) (y, y0)))
    as cvap
      by (apply @cover_vars_apply2; sp;
          try (apply @cover_vars_var);
          repeat (apply @cover_vars_snoc_weak); sp;
          repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  apply similarity_snoc; simpl.
  exists (snoc (snoc s1 (x, x0)) (y, y0))
         (snoc (snoc s2 (x, x0)) (y, y0))
         t t
         wfap cvap; sp.
  apply similarity_snoc; simpl.
  exists (snoc s1 (x, x0)) (snoc s2 (x, x0)) y0 y0 (@wf_base o)
         (cover_vars_base (snoc s1 (x, x0))); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).
  apply similarity_snoc; simpl.
  exists s1 s2 x0 x0 (@wf_base o) (cover_vars_base s1); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  lsubst_tac.
  rw @member_eq; sp.

  (* conclusion *)

  lsubst_tac.
  apply inhabited_type_if_equality in seqt2; sp.
Qed.

Lemma is_trans_type {o} :
  forall lib R (H : @bhyps o) i x y z u v e s1 s2 w c ws1 ws2,
    !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !LIn z (vars_hyps H)
    -> !LIn x (free_vars R)
    -> !LIn y (free_vars R)
    -> !LIn z (free_vars R)
    -> !LIn u (free_vars R)
    -> !LIn v (free_vars R)
    -> !(x = y)
    -> !(x = z)
    -> !(y = z)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
               (mk_conclax (mk_member (mk_apply2 R (mk_var x) (mk_var y)) (mk_uni i))))
            ws1)
    -> sequent_true lib
         (mk_wcseq
            (mk_baresequent
               (snoc
                  (snoc
                     (snoc
                        (snoc (snoc H (mk_hyp x mk_base))
                              (mk_hyp y mk_base))
                        (mk_hyp z mk_base))
                     (mk_hyp u (mk_apply2 R (mk_var x) (mk_var y))))
                  (mk_hyp v (mk_apply2 R (mk_var y) (mk_var z))))
                 (mk_concl (mk_apply2 R (mk_var x) (mk_var z)) e))
            ws2)
    -> similarity lib s1 s2 H
    -> hyps_functionality lib s1 H
    -> trans_type lib (lsubstc R w s1 c).
Proof.
  introv nixh niyh nizh nixr niyr nizr niur nivr.
  introv nxy nxz nyz.
  introv seqt1 seqt2 sim hf inh1 inh2.

  unfold inhabited_type in inh1, inh2; exrepnd.

  vr_seq_true in seqt2.

  generalize (seqt2 (snoc (snoc (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0)) (u, t0)) (v, t))
                    (snoc (snoc (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (z, z0)) (u, t0)) (v, t)));
    clear seqt2; intro seqt2.
  repeat (autodimp seqt2 hyp); exrepnd.

  (* hyps_functionality *)

  (* v *)
  generalize (hyps_functionality_snoc lib
                (snoc (snoc (snoc (snoc H (mk_hyp x mk_base))
                                  (mk_hyp y mk_base))
                            (mk_hyp z mk_base))
                      (mk_hyp u (mk_apply2 R (mk_var x) (mk_var y))))
                (mk_hyp v (mk_apply2 R (mk_var y) (mk_var z)))
                (snoc (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0)) (u, t0))
                t); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lift_lsubst; lift_lsubst in eq.
  rw @similarity_snoc in s; simpl in s; exrepnd; cpx.
  rw @similarity_snoc in s5; simpl in s5; exrepnd; cpx.
  rw @similarity_snoc in s6; simpl in s6; exrepnd; cpx.
  rw @similarity_snoc in s7; simpl in s7; exrepnd; cpx.

  lsubst_tac.
  allrw @equality_in_base_iff.

  generalize (membership_apply2 lib H R x y i s1a s2a0 w c c15 ws1);
    intro q; repeat (destimp q hyp).
  generalize (q t4 t0); clear q; intro q; repnd.

  spcast.
  generalize (implies_cequivc_apply2 lib
                (lsubstc R w s2a0 c15)
                (lsubstc R w s2a0 c15)
                t5 t3 t4 t0);
    intro ceq; repeat (autodimp ceq hyp); try (complete (apply cequivc_sym; auto)).
  apply tequality_in_uni_implies_tequality in q0; sp.
  apply tequality_respects_cequivc_right with (T2 := mkc_apply2 (lsubstc R w s2a0 c15) t4 t0); sp.
  apply cequivc_sym; sp.

  (* u *)
  generalize (hyps_functionality_snoc lib
                (snoc (snoc (snoc H (mk_hyp x mk_base))
                            (mk_hyp y mk_base))
                      (mk_hyp z mk_base))
                (mk_hyp u (mk_apply2 R (mk_var x) (mk_var y)))
                (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0))
                t0); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lift_lsubst; lift_lsubst in eq.
  rw @similarity_snoc in s; simpl in s; exrepnd; cpx.
  rw @similarity_snoc in s5; simpl in s5; exrepnd; cpx.
  rw @similarity_snoc in s6; simpl in s6; exrepnd; cpx.

  lsubst_tac.
  allrw @equality_in_base_iff.

  generalize (membership_apply2 lib H R x y i s1a s2a w c c14 ws1);
    intro q; repeat (destimp q hyp).
  generalize (q t5 t3); clear q; intro q; repnd.

  spcast.
  generalize (implies_cequivc_apply2 lib
                (lsubstc R w s2a c14)
                (lsubstc R w s2a c14)
                t6 t4 t5 t3);
    intro ceq; repeat (autodimp ceq hyp); try (complete (apply cequivc_sym; auto)).
  apply tequality_in_uni_implies_tequality in q0; sp.
  apply tequality_respects_cequivc_right with (T2 := mkc_apply2 (lsubstc R w s2a c14) t5 t3); sp.
  apply cequivc_sym; sp.

  (* z *)
  generalize (hyps_functionality_snoc lib
                (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
                (mk_hyp z mk_base)
                (snoc (snoc s1 (x, x0)) (y, y0))
                z0); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lsubst_tac; try (apply tequality_base).

  (* y *)
  generalize (hyps_functionality_snoc lib
                (snoc H (mk_hyp x mk_base))
                (mk_hyp y mk_base)
                (snoc s1 (x, x0))
                y0); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lsubst_tac; try (apply tequality_base).

  (* x *)
  generalize (hyps_functionality_snoc lib H (mk_hyp x mk_base) s1 x0); simpl; intro p.
  apply p; clear p; try (complete sp).
  introv eq s; lsubst_tac; try (apply tequality_base).

  (* similarity *)

  assert (wf_term (mk_apply2 R (mk_var x) (mk_var y)))
    as wfap1 by (apply wf_apply2; sp).

  assert (wf_term (mk_apply2 R (mk_var y) (mk_var z)))
    as wfap2 by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var y))
                     (snoc (snoc s1 (x, x0)) (y, y0)))
    as cvap1
      by (apply @cover_vars_apply2; sp;
          try (apply @cover_vars_var);
          repeat (apply @cover_vars_snoc_weak); sp;
          repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  assert (cover_vars (mk_apply2 R (mk_var y) (mk_var z))
                     (snoc (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0)) (u, t0)))
         as cvap2
         by (apply @cover_vars_apply2; sp;
             try (apply @cover_vars_var);
             repeat (apply @cover_vars_snoc_weak); sp;
             repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var y))
                     (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0)))
         as cvap3
         by (apply @cover_vars_apply2; sp;
             try (apply @cover_vars_var);
             repeat (apply @cover_vars_snoc_weak); sp;
             repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  (* v *)
  apply similarity_snoc; simpl.
  exists (snoc (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0)) (u, t0))
         (snoc (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (z, z0)) (u, t0))
         t t
         wfap2 cvap2; sp;
  try (complete (lsubst_tac; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  (* u *)
  apply similarity_snoc; simpl.
  exists (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (z, z0))
         (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (z, z0))
         t0 t0
         wfap1 cvap3; sp;
  try (complete (lsubst_tac; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  (* z *)
  apply similarity_snoc; simpl.
  exists (snoc (snoc s1 (x, x0)) (y, y0))
         (snoc (snoc s2 (x, x0)) (y, y0))
         z0 z0
         (@wf_base o) (cover_vars_base (snoc (snoc s1 (x, x0)) (y, y0))); sp;
  try (complete (lsubst_tac; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  (* y *)
  apply similarity_snoc; simpl.
  exists (snoc s1 (x, x0)) (snoc s2 (x, x0)) y0 y0 (@wf_base o)
         (cover_vars_base (snoc s1 (x, x0))); sp;
  try (complete (lsubst_tac; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  (* x *)
  apply similarity_snoc; simpl.
  exists s1 s2 x0 x0 (@wf_base o) (cover_vars_base s1); sp;
  try (complete (lsubst_tac; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  lsubst_tac; rw @member_eq; sp.

  lsubst_tac; rw @member_eq; sp.

  (* conclusion *)

  lsubst_tac.
  apply inhabited_type_if_equality in seqt2; sp.
Qed.


(** This is saying that if the sequent
 *        H, x : Base, y : Base |- (R1 x y) = (R2 x y) in Type(i)
 * is true, then
 *        (R1[s1] x0 y0 = R2[s1] x0 y0 in Type(i)) = (R1[s2] x0 y0 = R2[s2] x0 y0 in Type(i))
 * and
 *        (R1[s1] x0 y0 = R1[s1] x0 y0 in Type(i)
 *)
Lemma membership_apply2_eq {o} :
  forall lib (H : @bhyps o) R1 R2 x y i s1 s2 w1 w2 c11 c12 c21 c22 ws,
    sequent_true lib
      (mk_wcseq
         (mk_baresequent
            (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
            (mk_conclax (mk_equality (mk_apply2 R1 (mk_var x) (mk_var y))
                                     (mk_apply2 R2 (mk_var x) (mk_var y))
                                     (mk_uni i))))
         ws)
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> !LIn x (free_vars R1)
    -> !LIn y (free_vars R1)
    -> !LIn x (free_vars R2)
    -> !LIn y (free_vars R2)
    -> !LIn x (vars_hyps H)
    -> !LIn y (vars_hyps H)
    -> !(x = y)
    -> (forall x0 y0,
          tequality lib
            (mkc_equality
               (mkc_apply2 (lsubstc R1 w1 s1 c11) x0 y0)
               (mkc_apply2 (lsubstc R2 w2 s1 c21) x0 y0)
               (mkc_uni i))
            (mkc_equality
               (mkc_apply2 (lsubstc R1 w1 s2 c12) x0 y0)
               (mkc_apply2 (lsubstc R2 w2 s2 c22) x0 y0)
               (mkc_uni i))
          # equality lib
               (mkc_apply2 (lsubstc R1 w1 s1 c11) x0 y0)
               (mkc_apply2 (lsubstc R2 w2 s1 c21) x0 y0)
               (mkc_uni i)).
Proof.
  introv seqt hf sim nixr1 niyr1 nixr2 niyr2 nixh niyh nxy.
  introv.

  assert (!LIn y (dom_csub s1))
    as niys1 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn y (dom_csub s2))
    as niys2 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn x (dom_csub s1))
    as nixs1 by (allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn x (dom_csub s2))
    as nixs2 by (allapply @similarity_dom; repnd; allrw; sp).

  vr_seq_true in seqt.
  generalize (seqt (snoc (snoc s1 (x, x0)) (y, y0))
                   (snoc (snoc s2 (x, x0)) (y, y0))); clear seqt; intro seqt.
  repeat (autodimp seqt hyp); exrepnd.

  (* hyps_functionality *)
  apply hyps_functionality_snoc2; simpl; auto.
  introv e sim'; lsubst_tac; try (apply tequality_base).
  apply hyps_functionality_snoc2; simpl; auto.
  introv e sim'; lsubst_tac; try (apply tequality_base).

  (* similarity *)
  apply similarity_snoc; simpl.
  exists (snoc s1 (x, x0)) (snoc s2 (x, x0)) y0 y0 (@wf_base o)
         (cover_vars_base (snoc s1 (x, x0))); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).
  apply similarity_snoc; simpl.
  exists s1 s2 x0 x0 (@wf_base o) (cover_vars_base s1); sp;
  try (complete (lift_lsubst; rw @equality_in_base_iff; spcast; apply cequivc_refl)).

  lsubst_tac.
  rw @member_eq in seqt1.
  rw <- @member_equality_iff in seqt1; sp.
Qed.

Lemma sequent_equality_implies_member {o} :
  forall lib (H : @bhyps o) a b T wc,
    sequent_true lib (mk_wcseq (mk_bseq H (mk_conclax (mk_equality a b T))) wc)
    -> {wc' : wf_csequent (mk_bseq H (mk_conclax (mk_member a T)))
        $ sequent_true lib (mk_wcseq (mk_bseq H (mk_conclax (mk_member a T))) wc')}.
Proof.
  introv seq.

  assert (wf_csequent (mk_bseq H (mk_conclax (mk_member a T)))) as wc' by (clear seq; wfseq).
  exists wc'.

  vr_seq_true in seq.
  vr_seq_true.
  generalize (seq s1 s2 eqh sim); clear seq; intro seq; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  rw <- @member_member_iff.
  rw <- @member_equality_iff in seq1.
  dands; try (complete (apply equality_refl in seq1; auto)).
  revert seq0. revert seq1.
  generalize (lsubstc a w1 s1 c1) as a1.
  generalize (lsubstc b w2 s1 c2) as b1.
  generalize (lsubstc T wT s1 cT) as T1.
  generalize (lsubstc a w1 s2 c0) as a2.
  generalize (lsubstc b w2 s2 c3) as b2.
  generalize (lsubstc T wT s2 cT0) as T2.
  intros.
  apply (tequality_mkc_equality_implies) in seq0. repnd.
  rw @tequality_mkc_member.
  dands; auto.
  split; intro.
  apply seq3 in seq1.
  apply equality_refl in seq1; auto.
  apply equality_refl in seq1; auto.
  
Qed.
