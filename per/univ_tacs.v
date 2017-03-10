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
    | [ H : _ _ _ (@close _ _ (@univ _ _)) _ _ |- _ ] =>
        inversion H; exrepd; subst;
      try (match goal with
             | [ H : type_family _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
(*             | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst*)
(*             | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst*)
           end)
    | [ H : _ _ _ (@close _ _ (@univi _ _ _)) _ _ |- _ ] =>
        inversion H; exrepd; subst;
      try (match goal with
             | [ H : type_family _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst
(*             | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst*)
(*             | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inversion H; exrepd; subst*)
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
Lemma iscvalue_mkc_aequality {p} :
  forall t1 t2 T : @CTerm p, iscvalue (mkc_aequality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_aequality; allrw @isprog_eq; auto.
  apply isprogram_aequality; sp.
Qed.

Ltac apply_iscvalue :=
  match goal with
    | [ |- iscvalue _ ] =>
      first [ apply iscvalue_mkc_cequiv
            | apply iscvalue_mkc_approx
            | apply iscvalue_mkc_sup
            | apply iscvalue_mkc_equality
            | apply iscvalue_mkc_aequality
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
            | apply iscvalue_mkc_refl
            ]
  end.

Ltac one_computes_to_value_isvalue :=
  match goal with
    | [ H : computes_to_valc _ _ _ |- _ ] =>
      apply computes_to_valc_isvalue_eq in H;
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

    (* univi cases *)
    | [ H : univi _ _ (mkc_equality _ _ _) _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_aequality _ _ _) _          |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_tequality _ _) _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_approx _ _) _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_cequiv _ _) _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_function _ _ _) _           |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_isect _ _ _) _              |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_eisect _ _ _) _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_disect _ _ _) _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pertype _) _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_ipertype _) _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_spertype _) _               |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_partial _) _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_admiss _) _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_mono _) _                   |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_free_from_atom _ _ _) _     |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_efree_from_atom _ _ _) _    |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_free_from_atoms _ _) _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_w _ _ _) _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_m _ _ _) _                  |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pw _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_pm _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_texc _ _) _                 |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_union _ _) _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_image _ _) _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_set _ _ _) _                |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_tunion _ _ _) _             |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ (mkc_product _ _ _) _            |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
(*    | [ H : univi _ _ (mkc_esquash _) _      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2*)
    | [ H : univi _ _ mkc_base _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_uatom _                      |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_atom _                       |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2
    | [ H : univi _ _ mkc_int _                        |- _ ] => trw_h univi_exists_iff H; exrepd; not_univ_p2

    (* univ cases *)
    | [ H : univ _ (mkc_equality _ _ _) _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_aequality _ _ _) _          |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_tequality _ _) _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_approx _ _) _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_cequiv _ _) _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_function _ _ _) _           |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_isect _ _ _) _              |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_eisect _ _ _) _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_disect _ _ _) _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pertype _) _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_ipertype _) _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_spertype _) _               |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_partial _) _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_admiss _) _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_mono _) _                   |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_free_from_atom _ _ _) _     |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_efree_from_atom _ _ _) _    |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_free_from_atoms _ _) _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_w _ _ _) _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_m _ _ _) _                  |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pw _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_pm _ _ _ _ _ _ _ _ _ _ _) _ |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_texc _ _) _                 |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_union _ _) _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_image _ _) _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_set _ _ _) _                |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_tunion _ _ _) _             |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ (mkc_product _ _ _) _            |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
(*    | [ H : univ _ (mkc_esquash _) _      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2*)
    | [ H : univ _ mkc_base _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_uatom _                      |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_atom _                       |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
    | [ H : univ _ mkc_int _                        |- _ ] => let i := fresh "i" in destruct H as [ i H ]; not_univ_p2
  end.


(* This is like close_diff in per.v *)
Ltac not_univ := (try not_univ_p1); not_univ_p2.

Ltac computes_to_value_refl :=
  complete (apply computes_to_valc_refl;
            apply_iscvalue;
            auto).


Ltac duniv i h :=
  match goal with
  | [ H : univ _ _ _ |- _ ] => destruct H as [i h]
  end.
