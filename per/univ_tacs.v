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
    | [ H : _ _ _ (@close _ _ (@univ _ _)) _ _ _ |- _ ] =>
        inversion H; exrepd; subst;
      try (match goal with
             | [ H : type_family _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
             | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
             | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
           end)
    | [ H : _ _ _ (@close _ _ (@univi _ _ _)) _ _ _ |- _ ] =>
        inversion H; exrepd; subst;
      try (match goal with
             | [ H : type_family _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
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
Lemma iscvalue_mkc_requality {p} :
  forall t1 t2 T : @CTerm p, iscvalue (mkc_requality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_requality; allrw @isprog_eq; auto.
  apply isprogram_requality; sp.
Qed.
Hint Resolve iscvalue_mkc_requality : slow.

(* !!MOVE *)
Lemma iscvalue_mkc_equality {p} :
  forall t1 t2 T : @CTerm p, iscvalue (mkc_equality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_equality; allrw @isprog_eq; auto.
  apply isprogram_equality; sp.
Qed.
Hint Resolve iscvalue_mkc_equality : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_requality {p} :
  forall t1 t2 T : @CNTerm p, iscnvalue (mkcn_requality t1 t2 T).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_requality.
  apply isprogram_requality; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_requality : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_equality {p} :
  forall t1 t2 T : @CNTerm p, iscnvalue (mkcn_equality t1 t2 T).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_equality.
  apply isprogram_equality; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_equality : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_cequiv {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_cequiv t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_cequiv; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_cequiv : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_approx {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_approx t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_approx; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_approx : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_sup {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_sup t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_sup; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_sup : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_texc {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_texc t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_texc; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_texc : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_union {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_union t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_union; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_union : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_image {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_image t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_image; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_image : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_tequality {p} :
  forall t1 t2 : @CNTerm p, iscnvalue (mkcn_tequality t1 t2).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_tequality; eauto 3 with slow.
  apply isprogram_tequality; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_tequality : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_refl {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_refl t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_refl; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_refl : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_base {o} : @iscnvalue o mkcn_base.
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_base : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_atom {o} : @iscnvalue o mkcn_atom.
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscnvalue_mkcn_atom : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_axiom {o} : @iscnvalue o mkcn_axiom.
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_axiom : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_int {o} : @iscnvalue o mkcn_int.
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_int : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_uni {o} : forall i, @iscnvalue o (mkcn_uni i).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscnvalue_mkcn_uni : slow.

Lemma isprog_nout_vars_implies_subvars {o} :
  forall (t : @NTerm o) vs,
    isprog_nout_vars vs t -> subvars (free_vars t) vs.
Proof.
  introv isp.
  allrw @isprog_nout_vars_eq; tcsp.
Qed.
Hint Resolve isprog_nout_vars_implies_subvars : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_function {o} :
  forall a v b, @iscnvalue o (mkcn_function a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_function.
  apply isprogram_function; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_function : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_isect {o} :
  forall a v b, @iscnvalue o (mkcn_isect a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_isect.
  apply isprogram_isect; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_isect : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_disect {o} :
  forall a v b, @iscnvalue o (mkcn_disect a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_disect.
  apply isprogram_disect; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_disect : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_eisect {o} :
  forall a v b, @iscnvalue o (mkcn_eisect a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_eisect.
  apply isprogram_eisect; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_eisect : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_product {o} :
  forall a v b, @iscnvalue o (mkcn_product a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_product.
  apply isprogram_product; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_product : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_set {o} :
  forall a v b, @iscnvalue o (mkcn_set a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_set.
  apply isprogram_set; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_set : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_tunion {o} :
  forall a v b, @iscnvalue o (mkcn_tunion a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_tunion.
  apply isprogram_tunion; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_tunion : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_w {o} :
  forall a v b, @iscnvalue o (mkcn_w a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_w.
  apply isprogram_w; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_w : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_m {o} :
  forall a v b, @iscnvalue o (mkcn_m a v b).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_m.
  apply isprogram_m; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_m : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_pertype {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_pertype t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_pertype; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_pertype : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_ipertype {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_ipertype t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_ipertype; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_ipertype : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_spertype {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_spertype t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_spertype; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_spertype : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_partial {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_partial t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_partial; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_partial : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_mono {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_mono t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_mono; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_mono : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_admiss {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_admiss t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_admiss; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_admiss : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_inl {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_inl t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_inl; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_inl : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_inr {p} :
  forall t1 : @CNTerm p, iscnvalue (mkcn_inr t1).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_inr; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_inr : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_pw {o} :
  forall P ap A bp ba B cp ca cb C p, @iscnvalue o (mkcn_pw P ap A bp ba B cp ca cb C p).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_pw.
  apply isprogram_pw; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_pw : slow.

(* !!MOVE *)
Lemma iscnvalue_mkcn_pm {o} :
  forall P ap A bp ba B cp ca cb C p, @iscnvalue o (mkcn_pm P ap A bp ba B cp ca cb C p).
Proof.
  introv; destruct_cnterms; unfold iscnvalue; simpl; eauto 2 with slow.
  apply isvalue_pm.
  apply isprogram_pm; eauto 3 with slow.
Qed.
Hint Resolve iscnvalue_mkcn_pm : slow.

Lemma computes_to_valcn_isvalue_eq {p} :
  forall lib t v,
    @computes_to_valcn p lib t v
    -> iscnvalue t
    -> t = v.
Proof.
  unfold computes_to_valcn, computes_to_valc, iscvalue.
  introv comp isv; destruct_cnterms; allsimpl.
  apply cnterm_eq; simpl.
  apply computes_to_value_isvalue_eq in comp; sp.
Qed.

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

    | [ |- iscnvalue _ ] =>
      first [ apply iscnvalue_mkcn_cequiv
            | apply iscnvalue_mkcn_approx
            | apply iscnvalue_mkcn_sup
            | apply iscnvalue_mkcn_refl
            | apply iscnvalue_mkcn_equality
            | apply iscnvalue_mkcn_requality
            | apply iscnvalue_mkcn_tequality
            | apply iscnvalue_mkcn_base
(*            | apply iscnvalue_mkcn_uatom*)
            | apply iscnvalue_mkcn_atom
            | apply iscnvalue_mkcn_uni
            | apply iscnvalue_mkcn_int
(*            | apply iscnvalue_mkcn_nat*)
            | apply iscnvalue_mkcn_function
            | apply iscnvalue_mkcn_isect
            | apply iscnvalue_mkcn_eisect
            | apply iscnvalue_mkcn_disect
            | apply iscnvalue_mkcn_pertype
            | apply iscnvalue_mkcn_ipertype
            | apply iscnvalue_mkcn_spertype
            | apply iscnvalue_mkcn_partial
            | apply iscnvalue_mkcn_admiss
            | apply iscnvalue_mkcn_mono
(*            | apply iscnvalue_mkcn_free_from_atom
            | apply iscnvalue_mkcn_efree_from_atom
            | apply iscnvalue_mkcn_free_from_atoms*)
            | apply iscnvalue_mkcn_w
            | apply iscnvalue_mkcn_m
            | apply iscnvalue_mkcn_pw
            | apply iscnvalue_mkcn_pm
            | apply iscnvalue_mkcn_texc
            | apply iscnvalue_mkcn_union
            | apply iscnvalue_mkcn_image
            | apply iscnvalue_mkcn_set
            | apply iscnvalue_mkcn_tunion
            | apply iscnvalue_mkcn_product
            | apply iscnvalue_mkcn_axiom
            | apply iscnvalue_mkcn_inl
            | apply iscnvalue_mkcn_inr
            ]
  end.

Ltac one_computes_to_value_isvalue :=
  match goal with
    | [ H : computes_to_valc _ _ _ |- _ ] =>
      apply computes_to_valc_isvalue_eq in H;
        [ eqconstr H
        | complete (first [ apply_iscvalue | sp ])
        ]

    | [ H : computes_to_valcn _ _ _ |- _ ] =>
      apply computes_to_valcn_isvalue_eq in H;
        [ eqconstr H
        | complete (first [ apply_iscvalue | sp ])
        ]

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

Ltac not_univ_p2 :=
  match goal with
    | [ H : computes_to_valc  _ _ _ |- _ ] => complete computes_to_value_isvalue
    | [ H : ccomputes_to_valc _ _ _ |- _ ] => complete computes_to_value_isvalue
    | [ H : computes_to_valcn  _ _ _ |- _ ] => complete computes_to_value_isvalue
    | [ H : ccomputes_to_valcn _ _ _ |- _ ] => complete computes_to_value_isvalue
    (* univi cases *)
    | [ H : univi _ _ (mkcn_equality _ _ _) _ _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_requality _ _ _) _ _          |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_tequality _ _) _ _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_approx _ _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_cequiv _ _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_function _ _ _) _ _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_isect _ _ _) _ _              |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_eisect _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_disect _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_pertype _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_ipertype _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_spertype _) _ _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_partial _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_admiss _) _ _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_mono _) _ _                   |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
(*    | [ H : univi _ _ (mkcn_free_from_atom _ _ _) _ _     |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_efree_from_atom _ _ _) _ _    |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_free_from_atoms _ _) _ _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2*)
    | [ H : univi _ _ (mkcn_w _ _ _) _ _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_m _ _ _) _ _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_pw _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_pm _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_texc _ _) _ _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_union _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_image _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_set _ _ _) _ _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_tunion _ _ _) _ _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkcn_product _ _ _) _ _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
(*    | [ H : univi _ _ (mkcn_esquash _) _ _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2*)
    | [ H : univi _ _ mkcn_base _ _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
(*    | [ H : univi _ _ mkcn_uatom _ _                      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2*)
    | [ H : univi _ _ mkcn_atom _ _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkcn_int _ _                        |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    (* univ cases *)
    | [ H : univ _ (mkcn_equality _ _ _) _ _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_requality _ _ _) _ _          |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_tequality _ _) _ _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_approx _ _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_cequiv _ _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_function _ _ _) _ _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_isect _ _ _) _ _              |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_eisect _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_disect _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_pertype _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_ipertype _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_spertype _) _ _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_partial _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_admiss _) _ _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_mono _) _ _                   |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
(*    | [ H : univ _ (mkcn_free_from_atom _ _ _) _ _     |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_efree_from_atom _ _ _) _ _    |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_free_from_atoms _ _) _ _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2*)
    | [ H : univ _ (mkcn_w _ _ _) _ _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_m _ _ _) _ _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_pw _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_pm _ _ _ _ _ _ _ _ _ _ _) _ _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_texc _ _) _ _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_union _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_image _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_set _ _ _) _ _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_tunion _ _ _) _ _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkcn_product _ _ _) _ _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
(*    | [ H : univ _ (mkcn_esquash _) _ _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2*)
    | [ H : univ _ mkcn_base _ _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
(*    | [ H : univ _ mkcn_uatom _ _                      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2*)
    | [ H : univ _ mkcn_atom _ _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkcn_int _ _                        |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
  end.


(* This is like close_diff in per.v *)
Ltac not_univ := (try not_univ_p1); not_univ_p2.

Ltac computes_to_value_refl :=
  complete (first [apply computes_to_valc_refl | apply computes_to_valcn_refl];
            apply_iscvalue;
            auto).


Ltac duniv i h :=
  match goal with
    | [ H : univ _ _ _ _ |- _ ] => destruct H as [i h]
  end.
