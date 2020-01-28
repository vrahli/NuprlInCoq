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


Require Export type_sys.


Ltac not_univ_p1 :=
  match goal with
  | [ H : _ (@close _ (@univ _)) _ _ _ _ |- _ ] =>
    inversion H; exrepd; subst;
    try (match goal with
         | [ H : type_family _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : type_family_ext _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         end)
  | [ H : _ (@close _ (@univi _ _)) _ _ _ _ |- _ ] =>
    inversion H; exrepd; subst;
    try (match goal with
         | [ H : type_family _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : type_family_ext _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
         end)
  end.

(* !!MOVE *)
Lemma iscvalue_mkc_uatom {p} : @iscvalue p mkc_uatom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_atom {p} : @iscvalue p mkc_atom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_free_from_atom {p} :
  forall a b c : @CTerm p, iscvalue (mkc_free_from_atom a b c).
Proof.
  introv; destruct_cterms; allsimpl; allsimpl.
  unfold iscvalue; simpl.
  constructor; simpl; auto.
  apply isprogram_free_from_atom; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_efree_from_atom {p} :
  forall a b c : @CTerm p, iscvalue (mkc_efree_from_atom a b c).
Proof.
  introv; destruct_cterms; allsimpl; allsimpl.
  unfold iscvalue; simpl.
  constructor; simpl; auto.
  apply isprogram_efree_from_atom; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_free_from_atoms {p} :
  forall a b : @CTerm p, iscvalue (mkc_free_from_atoms a b).
Proof.
  introv; destruct_cterms; allsimpl; allsimpl.
  unfold iscvalue; simpl.
  constructor; simpl; auto.
  apply isprogram_free_from_atoms; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_free_from_defs {p} :
  forall a b : @CTerm p, iscvalue (mkc_free_from_defs a b).
Proof.
  introv; destruct_cterms; allsimpl; allsimpl.
  unfold iscvalue; simpl.
  constructor; simpl; auto.
  apply isprogram_free_from_defs; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma iscvalue_mkc_requality {p} :
  forall t1 t2 T : @CTerm p, iscvalue (mkc_requality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_requality; allrw @isprog_eq; auto.
  apply isprogram_requality; sp.
Qed.
Hint Resolve iscvalue_mkc_requality : slow.

Ltac apply_iscvalue :=
  match goal with
    | [ |- iscvalue _ ] =>
      first [ apply iscvalue_mkc_cequiv
            | apply iscvalue_mkc_approx
            | apply iscvalue_mkc_sup
            | apply iscvalue_mkc_refl
            | apply iscvalue_mkc_equality
            | apply iscvalue_mkc_requality
            | apply iscvalue_mkc_tequality
            | apply iscvalue_mkc_base
            | apply iscvalue_mkc_uatom
            | apply iscvalue_mkc_atom
            | apply iscvalue_mkc_uni
            | apply iscvalue_mkc_int
            | apply iscvalue_mkc_nat
            | apply iscvalue_mkc_function
            | apply iscvalue_mkc_isect
            | apply iscvalue_mkc_eisect
            | apply iscvalue_mkc_disect
            | apply iscvalue_mkc_pertype
            | apply iscvalue_mkc_ipertype
            | apply iscvalue_mkc_spertype
            | apply iscvalue_mkc_partial
            | apply iscvalue_mkc_admiss
            | apply iscvalue_mkc_mono
            | apply iscvalue_mkc_free_from_atom
            | apply iscvalue_mkc_efree_from_atom
            | apply iscvalue_mkc_free_from_atoms
            | apply iscvalue_mkc_free_from_defs
            | apply iscvalue_mkc_w
            | apply iscvalue_mkc_m
            | apply iscvalue_mkc_pw
            | apply iscvalue_mkc_pm
            | apply iscvalue_mkc_texc
            | apply iscvalue_mkc_union
            | apply iscvalue_mkc_image
            | apply iscvalue_mkc_set
            | apply iscvalue_mkc_tunion
            | apply iscvalue_mkc_product
            | apply iscvalue_mkc_axiom
            | apply iscvalue_mkc_inl
            | apply iscvalue_mkc_inr
            ]
  end.

(*Lemma all_in_bar_computes_to_valc_iscvalue_eq {o} :
  forall {lib} (bar : @BarLib o lib) t v,
    all_in_bar bar (fun lib => t ===>(lib) v)
    -> iscvalue t
    -> t = v.
Proof.
  introv comp isv.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  spcast.
  apply computes_to_valc_isvalue_eq in comp; auto.
Qed.*)

Lemma cequivc_uni_implies {o} :
  forall lib i (a : @CTerm o),
    cequivc lib (mkc_uni i) a
    -> computes_to_valc lib a (mkc_uni i).
Proof.
  introv ceq.
  eapply cequivc_uni in ceq;[|apply computes_to_valc_refl; eauto 2 with slow]; auto.
Qed.

Hint Resolve iscvalue_mkc_approx : slow.
Hint Resolve iscvalue_mkc_cequiv : slow.
Hint Resolve iscvalue_mkc_equality : slow.
Hint Resolve iscvalue_mkc_union : slow.
Hint Resolve iscvalue_mkc_function : slow.
Hint Resolve iscvalue_mkc_product : slow.

(*Lemma uni_not_approx_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a b,
    (mkc_uni i) ==b==>(bar) (mkc_approx a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma uni_not_cequiv_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a b,
    (mkc_uni i) ==b==>(bar) (mkc_cequiv a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma uni_not_equality_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a b c,
    (mkc_uni i) ==b==>(bar) (mkc_equality a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma uni_not_function_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a v b,
    (mkc_uni i) ==b==>(bar) (mkc_function a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma uni_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a v b,
    (mkc_uni i) ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma uni_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) i a b,
    (mkc_uni i) ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst.
  apply cequivc_uni_implies in comp0.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.*)

Lemma cequivc_mkc_approx_implies {o} :
  forall lib (t a b : @CTerm o),
    cequivc lib (mkc_approx a b) t
    -> {a', b' : CTerm $ computes_to_valc lib t (mkc_approx a' b') # cequivc lib a a' # cequivc lib b b'}.
Proof.
  introv ceq.
  eapply cequivc_mkc_approx in ceq;[|apply computes_to_valc_refl;eauto 3 with slow];auto.
Qed.

(*Lemma approx_not_cequiv_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b,
    (mkc_approx u v) ==b==>(bar) (mkc_cequiv a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_approx_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma approx_not_equality_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b c,
    (mkc_approx u v) ==b==>(bar) (mkc_equality a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_approx_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma approx_not_function_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u w a v b,
    (mkc_approx u w) ==b==>(bar) (mkc_function a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_approx_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma approx_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u w a v b,
    (mkc_approx u w) ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_approx_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma approx_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b,
    (mkc_approx u v) ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_approx_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.*)

Lemma cequivc_mkc_cequiv_implies {o} :
  forall lib (t a b : @CTerm o),
    cequivc lib (mkc_cequiv a b) t
    -> {a', b' : CTerm $ computes_to_valc lib t (mkc_cequiv a' b') # cequivc lib a a' # cequivc lib b b'}.
Proof.
  introv ceq.
  eapply cequivc_mkc_cequiv in ceq;[|apply computes_to_valc_refl;eauto 3 with slow];auto.
Qed.

(*Lemma cequiv_not_approx_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b,
    (mkc_cequiv u v) ==b==>(bar) (mkc_approx a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_cequiv_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma cequiv_not_equality_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b c,
    (mkc_cequiv u v) ==b==>(bar) (mkc_equality a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_cequiv_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma cequiv_not_function_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u w a v b,
    (mkc_cequiv u w) ==b==>(bar) (mkc_function a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_cequiv_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma cequiv_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u w a v b,
    (mkc_cequiv u w) ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_cequiv_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.

Lemma cequiv_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u v a b,
    (mkc_cequiv u v) ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_cequiv_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow.
  eqconstr comp1.
Qed.*)

Lemma cequivc_mkc_base_implies {o} :
  forall lib (t : @CTerm o),
    cequivc lib mkc_base t
    -> computes_to_valc lib t mkc_base.
Proof.
  introv ceq.
  eapply cequivc_base in ceq;[|apply computes_to_valc_refl;eauto 3 with slow];auto.
Qed.

(*Lemma base_not_approx_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    mkc_base ==b==>(bar) (mkc_approx a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma base_not_cequiv_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    mkc_base ==b==>(bar) (mkc_cequiv a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma base_not_equality_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b c,
    mkc_base ==b==>(bar) (mkc_equality a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma base_not_function_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a v b,
    mkc_base ==b==>(bar) (mkc_function a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma base_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a v b,
    mkc_base ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma base_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b,
    mkc_base ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_base_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.*)

Lemma cequivc_mkc_function_implies {o} :
  forall lib (T A : @CTerm o) (v : NVar) (B : CVTerm [v]),
    cequivc lib (mkc_function A v B) T
    -> {A' : CTerm $ {v' : NVar $ {B' : CVTerm [v'] $
        computes_to_valc lib T (mkc_function A' v' B')
        # cequivc lib A A' # bcequivc lib [v] B [v'] B'}}}.
Proof.
  introv ceq.
  eapply cequivc_mkc_function in ceq;[|apply computes_to_valc_refl;eauto 3 with slow];auto.
Qed.

(*Lemma function_not_approx_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_function u x v) ==b==>(bar) (mkc_approx a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_function_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma function_not_cequiv_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_function u x v) ==b==>(bar) (mkc_cequiv a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_function_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma function_not_equality_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b c,
    (mkc_function u x v) ==b==>(bar) (mkc_equality a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_function_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma function_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x w a v b,
    (mkc_function u x w) ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_function_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma function_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_function u x v) ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_function_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.*)

Lemma cequivc_mkc_equality_implies {o} :
  forall lib (T a b c : @CTerm o),
    cequivc lib (mkc_equality a b c) T
    -> {a' : CTerm $ {b' : CTerm $ {c' : CTerm $
        computes_to_valc lib T (mkc_equality a' b' c')
        # cequivc lib a a'
        # cequivc lib b b'
        # cequivc lib c c'}}}.
Proof.
  introv ceq.
  eapply cequivc_mkc_equality in ceq;[|apply computes_to_valc_refl;eauto 3 with slow];auto.
Qed.

(*Lemma equality_not_approx_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_equality u x v) ==b==>(bar) (mkc_approx a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_equality_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma equality_not_cequiv_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_equality u x v) ==b==>(bar) (mkc_cequiv a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_equality_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma equality_not_function_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b c,
    (mkc_equality u x v) ==b==>(bar) (mkc_function a b c)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_equality_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma equality_not_product_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x w a v b,
    (mkc_equality u x w) ==b==>(bar) (mkc_product a v b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 2 with slow.
  apply cequivc_mkc_equality_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.

Lemma equality_not_union_ceq_bar {o} :
  forall {lib} (bar : @BarLib o lib) u x v a b,
    (mkc_equality u x v) ==b==>(bar) (mkc_union a b)
    -> False.
Proof.
  introv comp.
  pose proof (bar_non_empty bar) as ne; exrepnd.
  pose proof (comp lib' ne0 lib') as comp; autodimp comp hyp; eauto 2 with slow; simpl in *.
  exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in comp1; auto; subst; eauto 3 with slow.
  apply cequivc_mkc_equality_implies in comp0; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow.
  eqconstr comp0.
Qed.*)

Ltac one_computes_to_value_isvalue :=
  match goal with
    | [ H : computes_to_valc _ _ _ |- _ ] =>
      apply computes_to_valc_isvalue_eq in H;
      [ eqconstr H
      | complete (first [ apply_iscvalue | sp ])
      ]
(*    | [ H : all_in_bar _ (fun lib => ccomputes_to_valc _ _ _) |- _ ] =>
      apply all_in_bar_computes_to_valc_iscvalue_eq in H;
      [ eqconstr H
      | complete (first [ apply_iscvalue | sp ])
      ]*)
    | [ H : computes_to_value _ _ _ |- _ ] =>
      apply computes_to_value_isvalue_eq in H;
      [ auto
      | complete (apply isvalue_axiom)
      ]
  end.

Ltac computes_to_value_isvalue :=
  try uncast;
  repeat one_computes_to_value_isvalue;
  try (complete sp).

(*Ltac computes_to_valc_ceq_bar_false :=
  match goal with
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_approx _ _)     |- _ ] => apply uni_not_approx_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_cequiv _ _)     |- _ ] => apply uni_not_cequiv_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_equality _ _ _) |- _ ] => apply uni_not_equality_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_function _ _ _) |- _ ] => apply uni_not_function_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_product _ _ _)  |- _ ] => apply uni_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_uni _) (mkc_union _ _)      |- _ ] => apply uni_not_union_ceq_bar    in H; inversion H

  | [ H : computes_to_valc_ceq_bar _ (mkc_approx _ _) (mkc_cequiv _ _)     |- _ ] => apply approx_not_cequiv_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_approx _ _) (mkc_equality _ _ _) |- _ ] => apply approx_not_equality_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_approx _ _) (mkc_function _ _ _) |- _ ] => apply approx_not_function_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_approx _ _) (mkc_product _ _ _)  |- _ ] => apply approx_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_approx _ _) (mkc_union _ _)      |- _ ] => apply approx_not_union_ceq_bar    in H; inversion H

  | [ H : computes_to_valc_ceq_bar _ (mkc_cequiv _ _) (mkc_approx _ _)     |- _ ] => apply cequiv_not_approx_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_cequiv _ _) (mkc_equality _ _ _) |- _ ] => apply cequiv_not_equality_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_cequiv _ _) (mkc_function _ _ _) |- _ ] => apply cequiv_not_function_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_cequiv _ _) (mkc_product _ _ _)  |- _ ] => apply cequiv_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_cequiv _ _) (mkc_union _ _)      |- _ ] => apply cequiv_not_union_ceq_bar    in H; inversion H

  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_approx _ _)     |- _ ] => apply base_not_approx_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_cequiv _ _)     |- _ ] => apply base_not_cequiv_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_equality _ _ _) |- _ ] => apply base_not_equality_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_function _ _ _) |- _ ] => apply base_not_function_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_product _ _ _)  |- _ ] => apply base_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ mkc_base (mkc_union _ _)      |- _ ] => apply base_not_union_ceq_bar    in H; inversion H

  | [ H : computes_to_valc_ceq_bar _ (mkc_function _ _ _) (mkc_approx _ _)     |- _ ] => apply function_not_approx_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_function _ _ _) (mkc_cequiv _ _)     |- _ ] => apply function_not_cequiv_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_function _ _ _) (mkc_equality _ _ _) |- _ ] => apply function_not_equality_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_function _ _ _) (mkc_product _ _ _)  |- _ ] => apply function_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_function _ _ _) (mkc_union _ _)      |- _ ] => apply function_not_union_ceq_bar    in H; inversion H

  | [ H : computes_to_valc_ceq_bar _ (mkc_equality _ _ _) (mkc_approx _ _)     |- _ ] => apply equality_not_approx_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_equality _ _ _) (mkc_cequiv _ _)     |- _ ] => apply equality_not_cequiv_ceq_bar   in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_equality _ _ _) (mkc_function _ _ _) |- _ ] => apply equality_not_function_ceq_bar in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_equality _ _ _) (mkc_product _ _ _)  |- _ ] => apply equality_not_product_ceq_bar  in H; inversion H
  | [ H : computes_to_valc_ceq_bar _ (mkc_equality _ _ _) (mkc_union _ _)      |- _ ] => apply equality_not_union_ceq_bar    in H; inversion H
  end.*)

Ltac not_univ_p2 :=
  match goal with
    | [ H : computes_to_valc  _ _ _ |- _ ] => complete computes_to_value_isvalue
    | [ H : ccomputes_to_valc _ _ _ |- _ ] => complete computes_to_value_isvalue
    (*| [ H : all_in_bar _ (fun lib => ccomputes_to_valc _ _ _) |- _ ] => complete computes_to_value_isvalue*)
    (*| [ H : computes_to_valc_ceq_bar _ _ _ |- _ ] => complete computes_to_valc_ceq_bar_false*)
    (* univi cases *)
    | [ H : univi _ _ (mkc_equality _ _ _) _ _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_requality _ _ _) _ _          |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_tequality _ _) _ _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_approx _ _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_cequiv _ _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_function _ _ _) _ _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_isect _ _ _) _ _              |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_eisect _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_disect _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pertype _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_ipertype _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_spertype _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_partial _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_admiss _) _ _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_mono _) _ _                   |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_free_from_atom _ _ _) _ _     |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_efree_from_atom _ _ _) _ _    |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_free_from_atoms _ _) _ _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_free_from_defs _ _) _ _       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_w _ _ _) _ _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_m _ _ _) _ _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pw _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pm _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_texc _ _) _ _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_union _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_image _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_set _ _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_tunion _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_product _ _ _) _ _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
(*    | [ H : univi _ _ (mkc_esquash _) _ _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2*)
    | [ H : univi _ _ mkc_base _ _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_uatom _ _                      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_atom _ _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_int _ _                        |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    (* univ cases *)
    | [ H : univ _ (mkc_equality _ _ _) _ _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_requality _ _ _) _ _          |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_tequality _ _) _ _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_approx _ _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_cequiv _ _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_function _ _ _) _ _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_isect _ _ _) _ _              |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_eisect _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_disect _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pertype _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_ipertype _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_spertype _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_partial _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_admiss _) _ _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_mono _) _ _                   |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_free_from_atom _ _ _) _ _     |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_efree_from_atom _ _ _) _ _    |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_free_from_atoms _ _) _ _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_free_from_defs _ _) _ _       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_w _ _ _) _ _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_m _ _ _) _ _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pw _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pm _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_texc _ _) _ _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_union _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_image _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_set _ _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_tunion _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_product _ _ _) _ _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
(*    | [ H : univ _ (mkc_esquash _) _ _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2*)
    | [ H : univ _ mkc_base _ _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_uatom _ _                      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_atom _ _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_int _ _                        |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
  end.


(* This is like close_diff in per.v *)
Ltac not_univ := (try not_univ_p1); not_univ_p2.

Ltac computes_to_value_refl :=
  complete (apply computes_to_valc_refl;
            apply_iscvalue;
            auto).


Ltac duniv i h :=
  match goal with
    | [ H : univ _ _ _ _ |- _ ] => destruct H as [i h]
  end.
