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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.


Lemma per_approx_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_approx_bar ts).
Proof.
  unfold uniquely_valued, per_approx_bar, eq_term_equals; sp.
  computes_to_eqbars.
  allrw; sp.
Qed.

Lemma per_approx_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_approx_bar ts).
Proof.
  unfold type_extensionality, per_approx_bar, eq_term_equals; sp.
  exists a b c d; sp; allrw <-; sp.
  exists bar; dands; tcsp.
Qed.

Lemma per_approx_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_approx_bar ts).
Proof.
  introv per.
  unfold per_approx_bar in *; exrepnd.
  exists c d a b; sp.
  { exists bar; dands; tcsp.
    introv i j; symm; eapply per2; eauto. }
  introv; rw per1; clear per1.

  split; intro h; unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }
Qed.

Lemma per_approx_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_approx_bar ts).
Proof.
  introv per1 per2.
  unfold per_approx_bar in *; exrepnd.

  exists a0 b0 c d; sp; spcast; sp.
  exists (intersect_bars bar0 bar).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per5 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per6 lib1) as q; autodimp q hyp.
    pose proof (per3 lib2) as w; autodimp w hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; clear q.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; clear w.
    simpl in *.
    rw z.
    rw <- u.
    computes_to_eqbars; tcsp.
Qed.

(* !!MOVE *)
Lemma computes_to_value_implies_isprogram {o} :
  forall lib (t1 t2 : @NTerm o), (t1 =v>( lib) t2) -> isprogram t2.
Proof.
  introv comp.
  unfold computes_to_value in comp; repnd.
  apply isvalue_implies in comp; tcsp.
Qed.
Hint Resolve computes_to_value_implies_isprogram : slow.

(* !!MOVE *)
Lemma approx_sterm {o} :
  forall lib (t t' : @NTerm o) f,
    computes_to_value lib t (sterm f)
    -> approx lib t t'
    -> {f' : nat -> NTerm
        & computes_to_value lib t' (sterm f')
        # forall n, approx lib (f n) (f' n) }.
Proof.
  introv comp apr.
  invertsn apr.
  repnud apr.
  destruct comp as [comp isv].
  apply apr4 in comp; exrepnd.
  applydup @reduces_to_preserves_program in comp1; auto.

  exists f'; dands; auto.

  { split; auto. }

  { introv.
    pose proof (comp0 n) as q.
    repndors; tcsp; inversion q. }
Qed.

(* !!MOVE *)
Lemma cequiv_seq {o} :
  forall lib (t t' : @NTerm o) f,
    computes_to_value lib t (sterm f)
    -> cequiv lib t t'
    -> {f' : nat -> NTerm
        & computes_to_value lib t' (sterm f')
        # forall n, cequiv lib (f n) (f' n)}.
Proof.
  introv comp ceq.
  allunfold @cequiv; repnd.
  eapply approx_sterm in ceq0;[|eauto].
  exrepnd.
  exists f'; dands; auto.
  introv; dands; auto.
  eapply approx_sterm in ceq;[|eauto].
  exrepnd.
  eapply computes_to_value_eq in comp;[|eauto]; ginv; tcsp.
Qed.

(* !!MOVE *)
Lemma approx_open_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, approx_open lib (f1 n) (f2 n))
    -> nt_wf (sterm f1)
    -> nt_wf (sterm f2)
    -> approx_open lib (sterm f1) (sterm f2).
Proof.
  introv apr wf1 wf2.
  apply approx_star_implies_approx_open.
  econstructor;[| |introv;apply approx_star_iff_approx_open;apply apr|]; eauto 2 with slow.
Qed.

(* !!MOVE *)
Lemma approx_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, approx lib (f1 n) (f2 n))
    -> isprogram (sterm f1)
    -> isprogram (sterm f2)
    -> approx lib (sterm f1) (sterm f2).
Proof.
   introv apr isp1 isp2.
   apply approx_open_approx; auto.
   apply approx_open_sterm_congruence; eauto 2 with slow.
   introv; apply approx_implies_approx_open; auto.
Qed.

(* !!MOVE *)
Lemma cequiv_sterm_congruence {o} :
  forall lib (f1 f2 : nat -> @NTerm o),
    (forall n, cequiv lib (f1 n) (f2 n))
    -> isprogram (sterm f1)
    -> isprogram (sterm f2)
    -> cequiv lib (sterm f1) (sterm f2).
Proof.
  introv ceq isp1 isp2.
  split; apply approx_sterm_congruence; auto; introv;
    pose proof (ceq n) as q; destruct q; auto.
Qed.

(* !!MOVE *)
Lemma cequiv_value {o} :
  forall lib (t t' v : @NTerm o),
    t =v>(lib) v
    -> cequiv lib t t'
    -> {v' : NTerm & (t' =v>(lib) v') # cequiv lib v v'}.
Proof.
  introv comp ceq.
  unfold computes_to_value in comp; repnd.
  inversion comp as [? isp isv]; subst; clear comp.
  apply iscan_implies in isv; repndors; exrepnd; subst.

  - eapply cequiv_canonical_form in ceq;[|];
      [|split;[eauto|]; eauto 2 with slow].
    exrepnd.
    eexists; dands; eauto.
    apply cequiv_congruence; eauto 2 with slow.

  - eapply cequiv_seq in ceq;[|split;[eauto|];eauto 2 with slow].
    exrepnd.
    eexists; dands; eauto.
    apply cequiv_sterm_congruence; eauto 2 with slow.
Qed.

(* !!MOVE *)
Lemma cequivc_preserves_computes_to_valc {o} :
  forall lib (T T' U : @CTerm o),
    computes_to_valc lib T U
    -> cequivc lib T T'
    -> {U' : CTerm
        & computes_to_valc lib T' U'
        # cequivc lib U U'}.
Proof.
  introv comp ceq.
  unfold computes_to_valc in *.
  unfold cequivc in *.
  destruct_cterms; simpl in *.
  eapply cequiv_value in ceq;[|eauto].
  exrepnd.
  applydup @computes_to_value_implies_isprogram in ceq1.
  apply isprogram_eq in ceq2.
  exists (mk_ct v' ceq2); simpl; dands; auto.
Qed.

(*Lemma cequivc_exc_all_in_bar {o} :
  forall {lib} (bar : @BarLib o lib) T U T',
    all_in_bar bar (fun lib => T ===>(lib) U)
    -> ccequivc_ext lib T T'
    -> exists U',
        all_in_bar bar (fun lib => T' ===>(lib) U' /\ ccequivc lib U U').
Proof.
  introv ib eceq.

  pose proof (bar_non_empty bar) as h.
  destruct h as [lib' h].
  pose proof (ib lib') as q; autodimp q hyp.
  pose proof (q lib') as w; autodimp w hyp; eauto 2 with slow; simpl in w.
  pose proof (eceq lib') as z; autodimp z hyp; eauto 2 with slow; simpl in z.
  spcast.
  eapply cequivc_preserves_computes_to_valc in z;[|eauto].
  exrepnd.
  exists U'.

  introv i j.

  SearchAbout computes_to_valc cequivc.
  Locate cequivc_mkc_requality.
  exists U
Qed.*)

Lemma per_approx_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_approx_bar ts).
Proof.
  introv per eceq.
  unfold per_approx_bar in *; exrepnd.

  computes_to_eqbars.
  clear per2.

  pose proof (eceq lib') as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in ceq; spcast.
  dup u as comp.
  apply cequivc_mkc_approx with (t' := T') in comp; auto; exrepnd.
  exists a b a' b'; dands; auto.

  exists bar.
  dands; tcsp.

  (* We should at least weaken it to something like:


Definition type_value_respecting {p} (ts : cts(p)) :=
  forall lib T T' eq bar,
     ts lib T T eq
     -> all_in_bar bar (fun lib => ccequivc lib T T')
     -> ts lib T T' eq.

But if we weaken it like that, what about the types that are defined in terms
of all extensions of the current library, such as function types?  We wouldn't
be able to prove this property...


Will we also have to change the definition of [approx] so that it says
that the right-hand-side has to compute to the same term in all extensions
of the library?


Can't we simply use [computes_to_valc_preserves_lib_extends]?


In the definition of [per_eq_bar], shouldn't we say that either [a1] and [b1]
are equal in the bar or that squiggle equal in the bar?

*)


XXXXX

  apply @approxc_cequivc_trans with (b := b); auto.
  apply @cequivc_approxc_trans with (b := a); auto.
  apply cequivc_sym; auto.
  apply @approxc_cequivc_trans with (b := b'); auto.
  apply @cequivc_approxc_trans with (b := a'); auto.
  apply cequivc_sym; auto.
Qed.

Lemma per_approx_bar_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_approx_bar lib ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_approx_bar.
  introv cts i e.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_approx_bar_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_approx_bar lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_approx_bar.
  introv cts i e1 e2.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_approx_bar_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_approx_bar lib ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_approx_bar.
  introv i e c; exrepnd.
  ccomputes_to_eqval.
  allrw; discover; sp.
  spcast; apply @cequivc_axiom with (t' := t') in c; sp.
Qed.

Lemma per_approx_bar_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_approx_bar lib ts).
Proof.
  intros; unfold type_system; sp.
  try apply per_approx_bar_uniquely_valued; auto.
  try apply per_approx_bar_type_extensionality; auto.
  try apply per_approx_bar_type_symmetric; auto.
  try apply per_approx_bar_type_transitive; auto.
  try apply per_approx_bar_type_value_respecting; auto.
  try apply per_approx_bar_term_symmetric; auto.
  try apply per_approx_bar_term_transitive; auto.
  try apply per_approx_bar_term_value_respecting; auto.
Qed.


Lemma close_type_system_approx {p} :
  forall lib (ts : cts(p)),
  forall T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_approx_bar lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 per.

  dup per as ps; unfold per_approx_bar in ps; exrepnd; spcast.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_approx".
      assert (uniquely_valued (per_approx_bar lib (close lib ts)))
        as uv
          by (apply per_approx_bar_uniquely_valued).
      apply uv with (T := T) (T' := T'); auto.
      apply uniquely_valued_trans5 with (T2 := T3) (eq2 := eq); auto.
      apply per_approx_bar_type_extensionality.
      apply per_approx_bar_type_symmetric.
      apply per_approx_bar_type_transitive.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_approx; auto;
    assert (type_symmetric (per_approx_bar lib (close lib ts)))
      as tys
        by (apply per_approx_bar_type_symmetric);
    assert (type_extensionality (per_approx_bar lib (close lib ts)))
      as tye
        by (apply per_approx_bar_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_approx;
    assert (type_value_respecting lib (per_approx_bar lib (close lib ts)))
           as tvr
           by (apply per_approx_bar_type_value_respecting).

    apply tvr; auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_approx_bar_type_symmetric.
    apply per_approx_bar_type_transitive.

    apply tvr; auto.
    apply @type_system_type_mem1 with (T := T); auto.
    apply per_approx_bar_type_symmetric.
    apply per_approx_bar_type_transitive.

  + SCase "term_symmetric".
    assert (term_symmetric (per_approx_bar lib (close lib ts)))
      as tes
        by (apply per_approx_bar_term_symmetric).
    apply tes with (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    assert (term_transitive (per_approx_bar lib (close lib ts)))
      as tet
        by (apply per_approx_bar_term_transitive).
    apply tet with (T := T) (T' := T'); auto.

  + SCase "term_value_respecting".
    assert (term_value_respecting lib (per_approx_bar lib (close lib ts)))
      as tvr
        by (apply per_approx_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_approx_bar_type_symmetric.
    apply per_approx_bar_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    apply CL_approx; apply per_approx_bar_type_symmetric; auto.
    apply CL_approx; apply per_approx_bar_type_symmetric; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr.

    dands; apply CL_approx; try (complete sp).

    apply per_approx_bar_type_transitive with (T2 := T); auto.
    allunfold @per_approx_bar; sp.
    ccomputes_to_eqval.
    exists a2 b2 c1 d1; sp; spcast; sp.
    allrw; sp.

    apply per_approx_bar_type_transitive with (T2 := T); auto.
    allunfold @per_approx_bar; sp.
    ccomputes_to_eqval.
    exists a0 b0 a2 b2; sp; spcast; sp.
    allrw; sp.

    dands; apply CL_approx.

    apply per_approx_bar_type_transitive with (T2 := T'); auto.
    allunfold @per_approx_bar; sp.
    ccomputes_to_eqval.
    exists c2 d2 c1 d1; sp; spcast; sp.
    allrw; sp.

    apply per_approx_bar_type_transitive with (T2 := T'); auto.
    allunfold @per_approx_bar; sp.
    ccomputes_to_eqval.
    exists a0 b0 c2 d2; sp; spcast; sp.
    allrw; sp.
Qed.

