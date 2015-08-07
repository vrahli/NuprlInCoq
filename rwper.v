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


Require Export per_props2.
Require Export per_props_equality.


Ltac rwper :=
  match goal with
    (* isect *)
    | [ H : equality _ _ _ (mkc_isect _ _ _) |- _ ] => trw_h equality_in_isect2 H; repnd
    | [ H : member _ _ (mkc_isect _ _ _) |- _ ] => trw_h member_in_isect H; repnd
    | [ H : tequality _ (mkc_isect _ _ _) (mkc_isect _ _ _) |- _ ] => trw_h tequality_isect H; repnd

    (* pertype *)
    | [ H : equality _ _ _ (mkc_pertype _) |- _ ] => trw_h equality_in_mkc_pertype H; repnd
    | [ H : tequality _ (mkc_pertype _) (mkc_pertype _) |- _ ] => trw_h tequality_mkc_pertype H; repnd

    (* ipertype *)
    | [ H : equality _ _ _ (mkc_ipertype _) |- _ ] => trw_h equality_in_mkc_ipertype H; repnd
    | [ H : tequality _ (mkc_ipertype _) (mkc_ipertype _) |- _ ] => trw_h tequality_mkc_ipertype H; repnd

    (* spertype *)
    | [ H : equality _ _ _ (mkc_spertype _) |- _ ] => trw_h equality_in_mkc_spertype H; repnd
    | [ H : tequality _ (mkc_spertype _) (mkc_spertype _) |- _ ] => trw_h tequality_mkc_spertype H; repnd

    (* base *)
    | [ H : equality _ ?t ?t mkc_base |- _ ] => clear H
    | [ H : member _ _ mkc_base |- _ ] => clear H
    | [ H : tequality _ mkc_base mkc_base |- _ ] => clear H
    | [ H : type _ mkc_base |- _ ] => clear H
    | [ H : equality _ _ _ mkc_base |- _ ] => trw_h equality_in_base_iff H
    | [ |- equality _ ?t ?t mkc_base ] => trw member_in_base_iff
    | [ |- member _ _ mkc_base ] => trw member_in_base_iff
    | [ |- equality _ _ _ mkc_base ] => trw equality_in_base_iff

    (* equality *)
    | [ H : type _ (mkc_equality _ _ _) |- _ ] => trw_h type_mkc_equality H
    | [ H : equality _ mkc_axiom mkc_axiom (mkc_equality _ _ _) |- _ ] => trw_rev_h member_equality_iff H
    | [ H : member _ mkc_axiom (mkc_equality _ _ _) |- _ ] => trw_rev_h member_equality_iff H
    | [ H : equality _ _ _ (mkc_equality _ _ _) |- _ ] => trw_h equality_in_mkc_equality H
    | [ H : member _ _ (mkc_equality _ _ _) |- _ ] => trw_h equality_in_mkc_equality H
    | [ H : tequality _ (mkc_equality _ _ _) (mkc_equality _ _ _) |- _ ] => trw_h tequality_mkc_equality2 H
    | [ |- equality _ mkc_axiom mkc_axiom (mkc_equality _ _ _) ] => trw_rev member_equality_iff
    | [ |- member _ mkc_axiom (mkc_equality _ _ _) ] => trw_rev member_equality_iff

    (* member *)
    | [ H : member _ mkc_axiom (mkc_member _ _) |- _ ] => trw_rev_h member_member_iff H
    | [ |- member _ mkc_axiom (mkc_member _ _) ] => trw_rev member_member_iff

    (* halts *)
    | [ H : member _ mkc_axiom (mkc_halts _) |- _ ] => trw_rev_h member_halts_iff H
    | [ H : equality _ mkc_axiom mkc_axiom (mkc_halts _) |- _ ] => trw_rev_h member_halts_iff H
    | [ |- member _ mkc_axiom (mkc_halts _) ] => trw_rev member_halts_iff
    | [ |- equality _ mkc_axiom mkc_axiom (mkc_halts _) ] => trw_rev member_halts_iff
  end.

Ltac rwpers := repeat (rwper; try (complete auto)).
