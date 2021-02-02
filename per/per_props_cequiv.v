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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


Lemma mkcn_cequiv_equality_in_uni {p} :
  forall lib (a b c d : @cterm p) i,
    equality lib (mkcn_cequiv a b) (mkcn_cequiv c d) (mkcn_uni i)
    <=>
    (ccequivcn lib a b <=> ccequivcn lib c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    allunfold @nuprl.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' : @cterm p => t ===>(lib) mkcn_axiom
                      # t' ===>(lib) mkcn_axiom
                      # ccequivcn lib a b).
    apply CL_cequiv; unfold per_cequiv.
    exists a b c d; sp; spcast; try computes_to_value_refl.
Qed.

Lemma mkcn_approx_equality_in_uni {p} :
  forall lib (a b c d : @cterm p) i,
    equality lib (mkcn_approx a b) (mkcn_approx c d) (mkcn_uni i)
    <=>
    (capproxcn lib a b <=> capproxcn lib c d).
Proof.
  sp; sp_iff Case; intro e.

  - Case "->".
    unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in e0; exrepnd.
    inversion e2; try not_univ.

  - Case "<-".
    exists (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp;
    spcast; try computes_to_value_refl.
    exists (fun t t' : @cterm p => t ===>(lib) mkcn_axiom
                      # t' ===>(lib) mkcn_axiom
                      # capproxcn lib a b).
    apply CL_approx; unfold per_approx.
    exists a b c d; sp; spcast; try computes_to_value_refl.
Qed.

Lemma member_approx_refl {p} :
  forall lib t, @member p lib mkcn_axiom (mkcn_approx t t).
Proof.
  intros.
  unfold member, equality.
  exists (fun (a b : @cterm p) => a ===>(lib) mkcn_axiom
                  # b ===>(lib) mkcn_axiom
                  # capproxcn lib t t).
  unfold nuprl; sp; spcast; try computes_to_value_refl.
  apply CL_approx.
  unfold per_approx.
  exists t t t t; sp; spcast; computes_to_value_refl.
  apply approxcn_refl; auto.
Qed.

Lemma member_cequiv_refl {p} :
  forall lib t, @member p lib mkcn_axiom (mkcn_cequiv t t).
Proof.
  intros.
  unfold member, equality.
  exists (fun (a b : @cterm p) => a ===>(lib) mkcn_axiom
                  # b ===>(lib) mkcn_axiom
                  # ccequivcn lib t t).
  unfold nuprl; sp; spcast; try computes_to_value_refl; eauto 2 with slow.
  apply CL_cequiv.
  unfold per_cequiv.
  exists t t t t; sp; spcast; try computes_to_value_refl.
Qed.

Lemma equal_approx {p} :
  forall lib t u,
    @tequality p lib (mkcn_approx t t) (mkcn_approx u u).
Proof.
  intros.
  unfold tequality.
  exists (fun (a b : @cterm p) => a ===>(lib) mkcn_axiom
                  # b ===>(lib) mkcn_axiom
                  # capproxcn lib t t).
  unfold nuprl.
  apply CL_approx.
  unfold per_approx.
  exists t t u u; sp; spcast; try computes_to_value_refl.
  split; sp; spcast; apply approxcn_refl; sp.
Qed.

Lemma equal_cequiv {p} :
  forall lib t u,
    @tequality p lib (mkcn_cequiv t t) (mkcn_cequiv u u).
Proof.
  intros.
  unfold tequality.
  exists (fun (a b : @cterm p) => a ===>(lib) mkcn_axiom
                  # b ===>(lib) mkcn_axiom
                  # ccequivcn lib t t).
  unfold nuprl.
  apply CL_cequiv.
  unfold per_cequiv.
  exists t t u u; sp; spcast; try computes_to_value_refl;
  try (split; sp; spcast; sp; eauto 2 with slow).
Qed.

Lemma member_base {p} :
  forall lib t, @member p lib t mkcn_base.
Proof.
  unfold member, equality; sp.
  exists (fun t t' => @ccequivcn p lib t t').
  unfold nuprl; sp; spcast; sp; eauto 2 with slow.
  apply CL_base.
  unfold per_base; sp; spcast; try computes_to_value_refl.
Qed.

Lemma member_cequiv {p} :
  forall lib t1 t2,
    @cequivcn p lib t1 t2
    -> member lib mkcn_axiom (mkcn_cequiv t1 t2).
Proof.
  unfold member, equality; sp.
  exists (fun (t t' : @cterm p) => t ===>(lib) mkcn_axiom
                      # t' ===>(lib) mkcn_axiom
                      # ccequivcn lib t1 t2);
    sp; spcast; try computes_to_value_refl; sp.
  apply CL_cequiv.
  unfold per_cequiv.
  exists t1 t2 t1 t2; sp; spcast; try computes_to_value_refl.
Qed.

Lemma member_approx {p} :
  forall lib t1 t2,
    @approxcn p lib t1 t2
    -> member lib mkcn_axiom (mkcn_approx t1 t2).
Proof.
  unfold member, equality; sp.
  exists (fun (t t' : @cterm p) => t ===>(lib) mkcn_axiom
                      # t' ===>(lib) mkcn_axiom
                      # capproxcn lib t1 t2);
    sp; spcast; try computes_to_value_refl; sp.
  apply CL_approx.
  unfold per_approx.
  exists t1 t2 t1 t2; sp; spcast; try computes_to_value_refl.
Qed.

Lemma member_approx_iff {p} :
  forall lib (t1 t2 : @cterm p),
    capproxcn lib t1 t2
    <=> member lib mkcn_axiom (mkcn_approx t1 t2).
Proof.
  sp; split; intro e.
  spcast; apply member_approx; sp.
  allunfold @member; allunfold @equality; allunfold @nuprl; exrepnd.
  inversion e1; subst; try not_univ.

  allunfold @per_approx; sp.
  uncast; computes_to_value_isvalue.
  discover; sp.
Qed.

Lemma member_halts_iff {p} :
  forall lib (t : @cterm p),
    chaltscn lib t
    <=> member lib mkcn_axiom (mkcn_halts t).
Proof.
  sp; rewrite <- fold_mkcn_halts.
  generalize (member_approx_iff lib mkcn_axiom (mkcn_cbv t nvarx (mkcvn_axiom nvarx))) as i; sp.
  rw <- i; clear i.
  destruct_cnterms; unfold hasvaluecn, approxcn, mkcn_cbv; simpl.

  sp_iff Case.

  - Case "->".
    intro hv.
    spcast; allunfold @approxcn; allunfold @hasvaluecn; allsimpl.
    allrw @isprog_eq.
    assert (isprogram x) as isp by eauto 2 with slow.
    generalize (hasvalue_as_approx lib x isp); intro e.
    allrw <-; sp.

  - Case "<-".
    intro a; spcast; allunfold @approxc; allunfold @hasvaluec; allsimpl.
    allrw @isprog_eq.
    assert (isprogram x) as isp by eauto 2 with slow.
    generalize (hasvalue_as_approx lib x isp); intro e.
    allrw; sp.
Qed.

Lemma equality_in_base {p} :
  forall lib (t1 t2 : @cterm p),
    equality lib t1 t2 mkcn_base -> ccequivcn lib t1 t2.
Proof.
  unfold equality, nuprl; introv e; exrepnd.
  inversion e1; subst; try not_univ.

  allunfold @per_base; sp.
  discover; sp.
Qed.

Lemma equality_in_base_iff {p} :
  forall lib (t1 t2 : @cterm p),
    equality lib t1 t2 mkcn_base <=> ccequivcn lib t1 t2.
Proof.
  intros; split; intro i; try (apply equality_in_base; sp).
  unfold equality, nuprl.
  exists (fun a b : @cterm p => ccequivcn lib a b); sp.
  apply CL_base; unfold per_base; sp;
  spcast; apply computes_to_value_isvalue_refl; repeat constructor; simpl; sp.
Qed.

Lemma tequality_base {p} :
  forall lib, @tequality p lib mkcn_base mkcn_base.
Proof.
  introv.
  unfold tequality.
  exists (fun a b : @cterm p => ccequivcn lib a b).
  unfold nuprl.
  apply CL_base.
  unfold per_base; sp; spcast; try (apply computes_to_valcn_refl); eauto 2 with slow.
Qed.
Hint Immediate tequality_base.

Lemma tequality_mkcn_approx {p} :
  forall lib (a b c d : @cterm p),
    tequality lib (mkcn_approx a b) (mkcn_approx c d)
    <=>
    (capproxcn lib a b <=> capproxcn lib c d).
Proof.
  unfold tequality, nuprl; sp; split; intro k; exrepnd.

  inversion k0; subst; try not_univ;
  try (inversion X; sp);
  try (computes_to_value_isvalue).

  exists (fun x y : @cterm p => x ===>(lib) mkcn_axiom
                     # y ===>(lib) mkcn_axiom
                     # capproxcn lib a b).
  apply CL_approx.
  unfold per_approx.
  exists a b c d; sp;
  spcast; apply computes_to_valcn_refl; eauto 3 with slow.
Qed.

Lemma chasvaluec_as_capproxcn {p} :
  forall lib (a : @cterm p),
    chaltscn lib a
    <=>
    capproxcn lib mkcn_axiom (mkcn_cbv a nvarx (mkcvn_axiom nvarx)).
Proof.
  introv; split; intro k; spcast.
  rw <- @hasvaluecn_as_approxcn; sp.
  allrw @hasvaluecn_as_approxcn; sp.
Qed.

Lemma tequality_mkcn_halts {p} :
  forall lib (a b : @cterm p),
    tequality lib (mkcn_halts a) (mkcn_halts b)
    <=>
    (chaltscn lib a <=> chaltscn lib b).
Proof.
  intros; repeat (rewrite <- fold_mkcn_halts).
  rw @tequality_mkcn_approx.
  allrw @chasvaluec_as_capproxcn; sp.
Qed.

(*
Lemma tequality_mkcn_halts :
  forall a b,
    tequality lib (mkcn_halts a) (mkcn_halts b)
    <->
    (hasvaluec a <-> hasvaluec b).
Proof.
  sp.
  repeat (rewrite <- fold_mkcn_halts).
  rewrite tequality_mkcn_approx.
  repeat (rewrite <- hasvaluec_as_approxc); sp.
Qed.
*)

Lemma member_approx_is_axiom {p} :
  forall lib (t t1 t2 : @cterm p),
    member lib t (mkcn_approx t1 t2)
    -> t ===>(lib) mkcn_axiom.
Proof.
  introv m.
  unfold member, equality, nuprl in m; exrepnd.
  inversion m1; subst; try not_univ.
  allunfold @per_approx; exrepnd.
  discover; sp.
Qed.

Lemma member_cequiv_iff {p} :
  forall lib (t1 t2 : @cterm p),
    ccequivcn lib t1 t2
    <=> member lib mkcn_axiom (mkcn_cequiv t1 t2).
Proof.
  sp; split; intro e.
  spcast; apply member_cequiv; sp.
  allunfold @member; allunfold @equality; allunfold @nuprl; exrepnd.
  inversion e1; subst; try not_univ.

  allunfold @per_cequiv; sp.
  uncast; computes_to_value_isvalue.
  discover; sp.
Qed.

Lemma tequality_mkcn_cequiv {p} :
  forall lib (a b c d : @cterm p),
    tequality lib (mkcn_cequiv a b) (mkcn_cequiv c d)
    <=>
    (ccequivcn lib a b <=> ccequivcn lib c d).
Proof.
  unfold tequality, nuprl; sp; split; intro k; exrepnd.

  inversion k0; subst; try not_univ.

(*
  inversion X; sp.
  computes_to_value_isvalue.
*)

  exists (fun x y : @cterm p => x ===>(lib) mkcn_axiom
                     # y ===>(lib) mkcn_axiom
                     # ccequivcn lib a b).
  apply CL_cequiv.
  unfold per_cequiv.
  exists a b c d; sp;
  spcast; apply computes_to_valcn_refl; eauto 3 with slow.
Qed.

Lemma equality_in_approx {p} :
  forall lib (a b t1 t2 : @cterm p),
    (capproxcn lib t1 t2 # a ===>(lib) mkcn_axiom # b ===>(lib) mkcn_axiom)
    <=> equality lib a b (mkcn_approx t1 t2).
Proof.
  sp; split; intro e.

  - unfold member, equality; sp.
    exists (fun t t' : @cterm p => t ===>(lib) mkcn_axiom
                                          # t' ===>(lib) mkcn_axiom
                                          # capproxcn lib t1 t2);
      sp; spcast; try computes_to_value_refl; sp.
    apply CL_approx.
    unfold per_approx.
    exists t1 t2 t1 t2; sp; spcast; try computes_to_value_refl.

  - unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_approx; exrepnd.
    uncast; computes_to_value_isvalue.
    discover; sp.
Qed.

Lemma equality_in_mkcn_cequiv {o} :
  forall lib a b (t1 t2 : @cterm o),
    equality lib a b (mkcn_cequiv t1 t2)
             <=> (a ===>(lib) mkcn_axiom
                    # b ===>(lib) mkcn_axiom
                    # ccequivcn lib t1 t2).
Proof.
  introv; split; intro h.

  - unfold equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ.
    match goal with
      | [ H : per_cequiv _ _ _ _ _ |- _ ] => rename H into p
    end.
    allunfold @per_cequiv; exrepnd; spcast.
    computes_to_value_isvalue.
    apply p1 in h0; clear p1; repnd; spcast.
    dands; spcast; auto.

  - unfold equality.
    exists (fun (t t' : cterm) => t ===>(lib) mkcn_axiom
                      # t' ===>(lib) mkcn_axiom
                      # ccequivcn lib t1 t2);
      sp; spcast; try computes_to_value_refl; sp.
    apply CL_cequiv.
    unfold per_cequiv.
    exists t1 t2 t1 t2; sp; spcast; try computes_to_value_refl.
Qed.

Lemma inhabited_cequiv {o} :
  forall lib (t1 t2 : @cterm o),
    inhabited_type lib (mkcn_cequiv t1 t2) <=> ccequivcn lib t1 t2.
Proof.
  unfold inhabited_type.
  introv; split; intro h; exrepnd.
  - rw @equality_in_mkcn_cequiv in h0; tcsp.
  - exists (@mkcn_axiom o).
    apply member_cequiv_iff; auto.
Qed.

Lemma inhabited_halts {p} :
  forall lib (t : @cterm p), chaltscn lib t <=> inhabited_type lib (mkcn_halts t).
Proof.
  introv; split; intro h.

  rw @member_halts_iff in h; exists (@mkcn_axiom p); auto.

  unfold inhabited_type in h; exrepnd.
  unfold member, equality in h0; exrepnd.
  rewrite <- fold_mkcn_halts in h0.
  inversion h0; subst; try not_univ.
  allunfold @per_approx; exrepnd.
  computes_to_value_isvalue.
  discover; repnd; spcast.
  destruct_cnterms; allsimpl.
  unfold hasvaluecn; simpl.
  allunfold @approxcn; allsimpl.
  assert (isprogram x0) as isp by eauto 2 with slow.
  generalize (hasvalue_as_approx lib x0 isp); intro e.
  apply e; auto.
Qed.

Lemma type_mkcn_halts {p} :
  forall lib (a : @cterm p), type lib (mkcn_halts a).
Proof.
  introv; rw @tequality_mkcn_halts; sp.
Qed.
Hint Immediate type_mkcn_halts.

Lemma equality_in_halts {p} :
  forall lib (a b t : @cterm p),
    (chaltscn lib t # a ===>(lib) mkcn_axiom # b ===>(lib) mkcn_axiom)
    <=> equality lib a b (mkcn_halts t).
Proof.
  introv; rewrite <- fold_mkcn_halts; rw <- @equality_in_approx;
  split; intro k; repnd; spcast; dands; spcast; auto;
  destruct_cnterms; allunfold @hasvaluecn; allunfold @approxcn; allsimpl;
  assert (isprogram x) as isp by eauto 2 with slow;
  generalize (hasvalue_as_approx lib x isp); intro e; apply e; auto.
Qed.

Lemma type_mkcn_unit {p} : forall lib, @type p lib mkcn_unit.
Proof.
  introv; rw @mkcn_unit_eq.
  apply equal_approx.
Qed.
Hint Immediate type_mkcn_unit.
Hint Resolve type_mkcn_unit : slow.

Lemma tequality_unit {o} :
  forall lib, @tequality o lib mkcn_unit mkcn_unit.
Proof.
  introv; allrw @mkcn_unit_eq.
  rw @tequality_mkcn_approx; sp.
Qed.

Lemma equality_in_unit {o} :
  forall lib (a b : @cterm o),
    equality lib a b mkcn_unit
    <=> (a ===>(lib) mkcn_axiom # b ===>(lib) mkcn_axiom).
Proof.
  introv.
  allrw @mkcn_unit_eq.
  rw <- @equality_in_approx; split; sp.
  spcast; sp.
  apply approxcn_refl.
Qed.

Lemma resp_cvc_approxc {p} :
  forall lib, respects2 (computes_to_valc lib) (@approxc p lib).
Proof.
  split; introv Hc Ha;
  apply computes_to_valc_implies_approxc in Hc; repnd;
  destruct_cterms; allunfold @approxc;
  eauto with slow.
Qed.
Hint Resolve resp_cvc_approxc : respects.

Lemma equality_in_uni_mkcn_halts {p} :
  forall lib i (a b : @cterm p),
    equality lib (mkcn_halts a) (mkcn_halts b) (mkcn_uni i)
    <=>
    (chaltscn lib a <=> chaltscn lib b).
Proof.
  intros; repeat (rewrite <- fold_mkcn_halts).
  rw @mkcn_approx_equality_in_uni.
  allrw @chasvaluec_as_capproxcn; sp.
Qed.

Lemma cequorsq_mkcn_halts_implies {p} :
  forall lib i (a b : @cterm p),
    equorsq lib (mkcn_halts a) (mkcn_halts b) (mkcn_uni i)
    -> (chaltscn lib a <=> chaltscn lib b).
Proof.
  unfold equorsq; intros; sp;
  allrw @equality_in_uni_mkcn_halts; sp.
  uncast; allrw @cequivcn_decomp_halts; sp;
    split; sp; spcast; discover; sp; eauto 3 with slow.
Qed.

Lemma cequorsq_mkcn_halts {p} :
  forall lib i (a b : @cterm p),
    equorsq lib (mkcn_halts a) (mkcn_halts b) (mkcn_uni i)
    <=>
    (chaltscn lib a <=> chaltscn lib b).
Proof.
  unfold equorsq; intros; split; sp; try right;
  allrw @equality_in_uni_mkcn_halts; sp; uncast;
  allrw @cequivcn_decomp_halts; try split; sp; spcast;
  discover; sp.
Abort.
(* This is not true in Prop with Cast around hasvalue *)
(*Qed.*)

Lemma member_in_base_iff {o} :
  forall lib (t : @cterm o), member lib t mkcn_base <=> True.
Proof.
  intros; split; intro; auto; apply member_base.
Qed.
