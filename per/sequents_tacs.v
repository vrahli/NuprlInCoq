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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents.
Require Export lift_lsubst_tacs.


Ltac free_vars_rw :=
  match goal with
    | [ |- context[free_vars (mk_isaxiom  _ _ _)] ] => rewrite free_vars_isaxiom
    | [ |- context[free_vars (mk_equality _ _ _)] ] => rewrite free_vars_equality

    | [ |- context[free_vars (mk_union     _ _)] ] => rewrite free_vars_union
    | [ |- context[free_vars (mk_bunion    _ _)] ] => rewrite free_vars_bunion
    | [ |- context[free_vars (mk_uand      _ _)] ] => rewrite free_vars_uand
    | [ |- context[free_vars (mk_apply     _ _)] ] => rewrite free_vars_apply
    | [ |- context[free_vars (mk_tequality _ _)] ] => rewrite free_vars_tequality
    | [ |- context[free_vars (mk_approx    _ _)] ] => rewrite free_vars_approx

    | [ |- context[free_vars mk_axiom] ] => rewrite free_vars_axiom
    | [ |- context[free_vars mk_base]  ] => rewrite free_vars_base
    | [ |- context[free_vars mk_bool]  ] => rewrite free_vars_bool
    | [ |- context[free_vars mk_unit]  ] => rewrite free_vars_unit

    | [ H : context[free_vars (mk_isaxiom  _ _ _)] |- _ ] => rewrite free_vars_isaxiom in H
    | [ H : context[free_vars (mk_equality _ _ _)] |- _ ] => rewrite free_vars_equality in H

    | [ H : context[free_vars (mk_union     _ _)] |- _ ] => rewrite free_vars_union in H
    | [ H : context[free_vars (mk_bunion    _ _)] |- _ ] => rewrite free_vars_bunion in H
    | [ H : context[free_vars (mk_uand      _ _)] |- _ ] => rewrite free_vars_uand in H
    | [ H : context[free_vars (mk_apply     _ _)] |- _ ] => rewrite free_vars_apply in H
    | [ H : context[free_vars (mk_tequality _ _)] |- _ ] => rewrite free_vars_tequality in H
    | [ H : context[free_vars (mk_approx    _ _)] |- _ ] => rewrite free_vars_approx in H

    | [ H : context[free_vars mk_axiom] |- _ ] => rewrite free_vars_axiom in H
    | [ H : context[free_vars mk_base]  |- _ ] => rewrite free_vars_base in H
    | [ H : context[free_vars mk_bool]  |- _ ] => rewrite free_vars_bool in H
    | [ H : context[free_vars mk_unit]  |- _ ] => rewrite free_vars_unit in H
  end.

Ltac insub_step :=
  match goal with
    | [ H : similarity _ _ _ _ _ |- _ ] => apply similarity_dom in H; repnd
    | [ H : eq_hyps _ _ _ _ _ |- _ ] => apply eq_hyps_dom in H; repnd
    | [ H : sub_eq_hyps _ _ _ _ _ _ _ |- _ ] => apply sub_eq_hyps_dom in H; repnd
    | [ |- context[dom_csub (snoc _ _)] ] => rewrite dom_csub_snoc
    | [ |- context[LIn _ (snoc _ _)] ] => trw in_snoc
    | [ |- context[_ ++ nil] ] => rewrite app_nil_r
    | [ |- context[dom_csub (snoc _ _)] ] => rewrite dom_csub_snoc
    | [ |- context[LIn _ (_ :: nil)] ] => trw in_single_iff
    | [ |- context[LIn _ (snoc _ _)] ] => trw in_snoc
    | [ |- context[LIn _ (app _ _)] ] => trw in_app_iff
    | [ |- context[LIn _ (remove_nvars _ _)] ] => trw in_remove_nvars
    | [ |- context[!(_ [+] _)] ] => trw not_over_or
    | [ |- context[vars_hyps (substitute_hyps _ _)] ] => rewrite vars_hyps_substitute_hyps
    | [ |- context[disjoint [_] _] ] => trw disjoint_singleton_l
    | [ H : vars_hyps _ = dom_csub ?s |- context[dom_csub ?s] ] => rewrite <- H
    | [ H : dom_csub ?s = vars_hyps _ |- context[dom_csub ?s] ] => rewrite H
    | [ H : vars_hyps _ = dom_csub ?s, H2 : context[dom_csub ?s] |- _ ] => rewrite <- H in H2
    | [ H : dom_csub ?s = vars_hyps _, H2 : context[dom_csub ?s] |- _ ] => rewrite H in H2
  end.

Ltac ainsub := repeat (first [ free_vars_rw | simpl; insub_step; simpl ]; auto).
Ltac insub := ainsub; sp.

Ltac splst_step :=
  match goal with
    | [ |- context[LIn _ (_ :: nil)] ] => trw in_single_iff
    | [ |- context[LIn _ (snoc _ _)] ] => trw in_snoc
    | [ |- context[LIn _ (app _ _)] ] => trw in_app_iff
    | [ |- context[LIn _ (remove_nvars _ _)] ] => trw in_remove_nvars
    | [ |- context[dom_csub (snoc _ _)] ] => rewrite dom_csub_snoc
    | [ |- context[dom_csub (csub_filter _ _)] ] => rewrite dom_csub_csub_filter
    | [ |- context[dom_sub (snoc _ _)] ] => rewrite dom_sub_snoc
    | [ |- context[dom_sub (csub2sub _)] ] => rewrite dom_csub_eq
    | [ |- context[!(_ [+] _)] ] => trw not_over_or
  end.

Ltac splst_step_hyp h :=
  match type of h with
    | context[LIn _ (_ :: nil)] => trw_h in_single_iff h
    | context[LIn _ (snoc _ _)] => trw_h in_snoc h
    | context[LIn _ (app _ _)] => trw_h in_app_iff h
    | context[LIn _ (remove_nvars _ _)] => trw_h in_remove_nvars h
    | context[dom_csub (snoc _ _)] => rewrite dom_csub_snoc in h
    | context[dom_csub (csub_filter _ _)] => rewrite dom_csub_csub_filter in h
    | context[dom_sub (snoc _ _)] => rewrite dom_sub_snoc in h
    | context[dom_sub (csub2sub _)] => rewrite dom_csub_eq in h
    | context[!(_ [+] _)] => trw_h not_over_or h
  end.

Tactic Notation "splst" := repeat (splst_step; simpl).
Tactic Notation "splst" "in" ident(h) := repeat (splst_step_hyp h; simpl in h).

Ltac rwall eq :=
  match type of eq with
    | ?x = ?y =>
      repeat match goal with
               | [ eq : x = y |- context[x] ] => rewrite eq
               | [ eq : x = y, H : context[x] |- _ ] => rewrite eq in H
             end
  end.

Lemma test_rwall :
  forall x y,
    x = 1
    -> x = y
    -> x = y
    -> y = x
    -> False.
Proof.
  introv e1 e2 e3 e4.
  rwall e3.
Abort.

Tactic Notation "lsubstc_snoc_step" constr(T) tactic(tac) :=
  match T with
    (*
     * ==== 1 ====
     * lsubstc t (snoc s (x,u)) = lsubstc t s
     * if x not in the free variables of t
     *)
    | context[lsubstc ?t ?w (snoc ?s (?x, ?u)) ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : !LIn x (free_vars t) |- _ ] =>
          pose proof (subset_free_vars_lsubstc_snoc_ex t s x u w c H) neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x (free_vars t)) as H by tac;
            pose proof (subset_free_vars_lsubstc_snoc_ex t s x u w c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 2 ====
     * lsubstc t ((x,u) :: s) = lsubstc t s
     * if x not in the free variables of t
     *)
    | context[lsubstc ?t ?w ((?x, ?u) :: ?s) ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : !LIn x (free_vars t) |- _ ] =>
          pose proof (subset_free_vars_lsubstc_cons_ex t s x u w c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x (free_vars t)) as H by tac;
            pose proof (subset_free_vars_lsubstc_cons_ex t s x u w c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 3 ====
     * lsubstc (mk_var x) (snoc s (y,t)) = lsubstc (mk_var x) s
     * if x in s
     *)
    | context[lsubstc (mk_var ?x) ?w (snoc ?s (?y, ?t)) ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : LIn x (dom_csub s) |- _ ] =>
          pose proof (lsubstc_snoc_var2_ex x s y t w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (LIn x (dom_csub s)) as H by tac;
            pose proof (lsubstc_snoc_var2_ex x s y t w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 4 ====
     * lsubstc (mk_var x) (snoc s (x,t)) = t
     * if x not in s
     *)
    | context[lsubstc (mk_var ?x) ?w (snoc ?s (?x, ?t)) ?c] =>
      let neq := fresh "eq" in
      match goal with
        | [ H : !LIn x (dom_csub s) |- _ ] =>
          pose proof (lsubstc_snoc_var s x t w c H) as neq;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x (dom_csub s)) as H by tac;
            pose proof (lsubstc_snoc_var s x t w c H) as neq;
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 5 ====
     * lsubstc (mk_var x) ((y,t) :: s) = lsubstc (mk_var x) s
     * if x <> y
     *)
    | context[lsubstc (mk_var ?x) ?w ((?y, ?t) :: ?s) ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : x <> y |- _ ] =>
          pose proof (lsubstc_cons_var2_ex x s y t w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (x <> y) as H by tac;
            pose proof (lsubstc_cons_var2_ex x s y t w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 6 ====
     * lsubstc (mk_var x) ((x,t) :: s) = t
     *)
    | context[lsubstc (mk_var ?x) ?w ((?x, ?t) :: ?s) ?c] =>
      let neq := fresh "eq" in
      pose proof (lsubstc_cons_var s x t w c) as neq;
        rwall neq;
        clear neq

    (*
     * ==== 7 ====
     * lsubstc t p (sub1 ++ sub2) c = lsubstc t p sub1 c'
     * if disjoint (Free_vars t) (dom_csub sub2)
     *)
    | context[lsubstc ?t ?w (app ?s1 ?s2) ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : disjoint (free_vars t) (dom_csub s2) |- _ ] =>
          pose proof (subset_free_vars_lsubstc_app_ex t s1 s2 w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "disj" in
          assert (disjoint (free_vars t) (dom_csub s2)) as H by tac;
            pose proof (subset_free_vars_lsubstc_app_ex t s1 s2 w c H) as neq;
            destruct neq as [ nc neq ];
            rwall neq;
            clear neq;
            clear H
      end

    (*
     * ==== 8 ====
     * csubst t (snoc s (x,u)) = csubst t s
     * if x not in the free variables of t
     *)
    | context[csubst ?t (snoc ?s (?x, ?u))] =>
      let neq := fresh "eq" in
      match goal with
        | [ H : !LIn x (free_vars t) |- _ ] =>
          pose proof (subset_free_vars_csub_snoc t s x u H) as neq;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x (free_vars t)) as H by tac;
            pose proof (subset_free_vars_csub_snoc t s x u H) as neq;
            rwall neq;
            clear neq;
            clear H
      end
end.

Tactic Notation "lsubstc_snoc_step_vs" constr(T) tactic(tac) :=
  match T with
    (*
     * ==== 9 ====
     * lsubstc_vars t w (snoc s (x,u)) vs c = lsubstc_vars t w s vs c'
     * if x not in the free variables of t
     *)
    | context[lsubstc_vars ?t ?w (snoc ?s (?x, ?u)) ?vs ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : !LIn x (free_vars t) |- _ ] =>
          pose proof (subset_free_vars_lsubstc_vars_snoc_ex t s x u w vs c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x (free_vars t)) as H by tac;
            pose proof (subset_free_vars_lsubstc_vars_snoc_ex t s x u w vs c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq;
            clear H
      end


    (*
     * ==== 10 ====
     * lsubstc_vars t w (csub_filter (snoc s (x,u)) vs) vs c
     *   = lsubstc_vars t w (csub_filter s vs) vs c'
     * if x not in the free variables of t
     *)
    | context[lsubstc_vars ?t ?w (csub_filter (snoc ?s (?x, ?u)) ?vs) ?vs ?c] =>
      let neq := fresh "eq" in
      let nc := fresh "c" in
      match goal with
        | [ H : !LIn x vs -> !LIn x (free_vars t) |- _ ] =>
          pose proof (lsubstc_vars_csub_filter_snoc_ex t w s x u vs c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq
        | _ =>
          let H := fresh "lin" in
          assert (!LIn x vs -> !LIn x (free_vars t)) as H by (first [splst; sp | tac]);
            pose proof (lsubstc_vars_csub_filter_snoc_ex t w s x u vs c H) as neq;
            destruct neq as [ nc neq ];
            clear_irr;
            rwall neq;
            clear neq;
            clear H
      end
  end.

Tactic Notation "lsubstc_snoc_step_hyp" ident(H) tactic(tac) :=
  let T := type of H in
  progress (lsubstc_snoc_step T tac).

Tactic Notation "lsubstc_snoc_step_concl" tactic(tac) :=
  match goal with
  | [ |- ?T ] => progress (lsubstc_snoc_step T tac)
  end.

Tactic Notation "lsubstc_snoc_step_all" tactic(tac) :=
  match goal with
  | [ |- ?T ] => progress (lsubstc_snoc_step T tac)
  | [ H : ?T |- _ ] => progress (lsubstc_snoc_step T tac)
  end.

Tactic Notation "lsubstc_snoc_step_vs_hyp" ident(H) tactic(tac) :=
  let T := type of H in
  progress (lsubstc_snoc_step_vs T tac).

Tactic Notation "lsubstc_snoc_step_vs_concl" tactic(tac) :=
  match goal with
  | [ |- ?T ] => progress (lsubstc_snoc_step_vs T tac)
  end.

Tactic Notation "lsubstc_snoc_step_vs_all" tactic(tac) :=
  match goal with
  | [ |- ?T ] => progress (lsubstc_snoc_step_vs T tac)
  | [ H : ?T |- _ ] => progress (lsubstc_snoc_step_vs T tac)
  end.

Ltac lsubstc_snoc := repeat (lsubstc_snoc_step_all insub).
Ltac lsubstc_snoc_concl := repeat (lsubstc_snoc_step_concl insub).
Ltac lsubstc_snoc_hyp H := repeat (lsubstc_snoc_step_hyp H insub).
Ltac lsubstc_snoc_vs := repeat (lsubstc_snoc_step_vs_all insub).

Ltac ai_lsubstc_snoc := repeat (lsubstc_snoc_step_all ainsub).
Ltac ai_lsubstc_snoc_vs := repeat (lsubstc_snoc_step_vs_all ainsub).

Ltac a_lsubstc_snoc := repeat (lsubstc_snoc_step_all auto).
Ltac a_lsubstc_snoc_vs := repeat (lsubstc_snoc_step_vs_all auto).

Ltac lsubst_tac :=
  lift_lsubsts;
  lsubstc_snoc;
  lift_lsubsts.

(* !! Make a hyp version of lsubstc_snoc *)
Ltac lsubst_tac_h H :=
  lift_lsubst_hyp H;
  lsubstc_snoc;
  lift_lsubst_hyp H.

Ltac a_lsubst_tac :=
  lift_lsubsts;
  a_lsubstc_snoc;
  lift_lsubsts.

Ltac ai_lsubst_tac :=
  lift_lsubsts;
  ai_lsubstc_snoc;
  lift_lsubsts.

Ltac simplerw :=
  allrw @wf_equality_iff2;    exrepd; allsimpl;
  allrw @covered_equality;    exrepd; allsimpl;
  allrw @vars_hyps_app;       exrepd; allsimpl;
  allrw @vars_hyps_snoc;      exrepd; allsimpl;
  allrw @nh_vars_hyps_app;    exrepd; allsimpl;
  allrw @nh_vars_hyps_snoc;   exrepd; allsimpl;
  allrw @subvars_singleton_l; exrepd; allsimpl;
  allrw @in_app_iff;          exrepd; allsimpl;
  allrw @in_snoc;             exrepd; allsimpl;
  try (complete sp).

Ltac prove_seq :=
  allunfold args_constraints;
  allunfold arg_constraints;
  allunfold wf_csequent;
  allunfold closed_type_baresequent;
  allunfold closed_extract_baresequent;
  allunfold closed_type;
  allunfold closed_extract;
  allunfold wf_sequent;
  allunfold wf_concl;
  allsimpl; sp; subst; allsimpl; sp;
  simplerw.

(* This is meant to replace prove_seq *)
Ltac wfseq :=
  repeat (first [ progress sp
                | progress subst
                | progress allsimpl
                | progress simplerw
                | progress (allunfold @args_constraints); allsimpl
                | progress (allunfold @arg_constraints); allsimpl
                | progress (allunfold @wf_csequent); allsimpl
                | progress (allunfold @closed_type_baresequent); allsimpl
                | progress (allunfold @closed_extract_baresequent); allsimpl
                | progress (allunfold @closed_type); allsimpl
                | progress (allunfold @closed_extract); allsimpl
                | progress (allunfold @wf_sequent); allsimpl
                | progress (allunfold @wf_concl); allsimpl
                | progress (rw @covered_isect); allsimpl
                | progress (rw @covered_cequiv); allsimpl
                | progress (rw @covered_approx); allsimpl
                | progress (rw @covered_equality); allsimpl
                | progress (rw @covered_var); allsimpl
         ]).

(* This is meant to replace wfseq and prove_seq *)
Ltac dwfseq_step :=
  match goal with
    (* unfold in hyp *)
    | [ H : wf_csequent _ |- _ ] => unfold wf_csequent in H; repnd; allsimpl
    | [ H : wf_sequent _ |- _ ] => unfold wf_sequent in H; repnd; allsimpl
    | [ H : wf_concl _ |- _ ] => unfold wf_concl in H; repnd; allsimpl
    | [ H : closed_type _ _ |- _ ] => unfold closed_type in H; repnd; allsimpl
    | [ H : closed_extract _ _ |- _ ] => unfold closed_extract in H; repnd; allsimpl
    | [ H : closed_type_baresequent _ |- _ ] => unfold closed_type_baresequent in H; repnd; allsimpl
    | [ H : closed_extract_baresequent _ |- _ ] => unfold closed_extract_baresequent in H; repnd; allsimpl
    | [ H : covered _ _ |- _ ] => unfold covered in H; repnd; allsimpl
    | [ H : args_constraints _ _ |- _ ] => unfold args_constraints in H; repnd; allsimpl
    | [ H : arg_constraints _ _ |- _ ] => unfold arg_constraints in H; repnd; allsimpl
    (* unfold in concl *)
    | [ |- context[covered _ _] ] => unfold covered; allsimpl
    (* rewrite in context in hyps *)
    | [ H : context[hyps_free_vars (_ ++ _)] |- _ ] => rewrite hyps_free_vars_app in H
    | [ H : context[hyps_free_vars (snoc _ _)] |- _ ] => rewrite hyps_free_vars_snoc in H
    | [ H : context[app _ nil] |- _ ] => rewrite app_nil_r in H; repnd; allsimpl
    | [ H : context[remove_nvars [] _] |- _ ] => rewrite remove_nvars_nil_l in H; repnd; allsimpl
    | [ H : context[vars_hyps (app _ _)] |- _ ] => rewrite vars_hyps_app in H; allsimpl
    | [ H : context[vars_hyps (snoc _ _)] |- _ ] => rewrite vars_hyps_snoc in H; allsimpl
    | [ H : context[nh_vars_hyps (app _ _)] |- _ ] => rewrite nh_vars_hyps_app in H; repnd; allsimpl
    | [ H : context[nh_vars_hyps (snoc _ _)] |- _ ] => rewrite nh_vars_hyps_snoc in H; repnd; allsimpl
    | [ H : context[hyp_free_vars (mk_hyp _ _)] |- _ ] => rewrite hyp_free_vars_mk_hyp in H; repnd; allsimpl
    | [ H : context[hyp_free_vars (mk_hhyp _ _)] |- _ ] => rewrite hyp_free_vars_mk_hhyp in H; repnd; allsimpl
    | [ H : context[filter _ (app _ _)] |- _ ] => rewrite filter_app in H; repnd; allsimpl
    | [ H : context[filter _ (snoc _ _)] |- _ ] => rewrite filter_snoc in H; repnd; allsimpl
    (* rewrite in context in concl *)
    | [ |- context[hyps_free_vars (_ ++ _)] ] => rewrite hyps_free_vars_app
    | [ |- context[hyps_free_vars (snoc _ _)] ] => rewrite hyps_free_vars_snoc
    | [ |- context[app _ nil] ] => rewrite app_nil_r; repnd; allsimpl
    | [ |- context[remove_nvars [] _] ] => rewrite remove_nvars_nil_l; repnd; allsimpl
    | [ |- context[vars_hyps (app _ _)] ] => rewrite vars_hyps_app; allsimpl
    | [ |- context[vars_hyps (snoc _ _)] ] => rewrite vars_hyps_snoc; allsimpl
    | [ |- context[nh_vars_hyps (app _ _)] ] => rewrite nh_vars_hyps_app; repnd; allsimpl
    | [ |- context[nh_vars_hyps (snoc _ _)] ] => rewrite nh_vars_hyps_snoc; repnd; allsimpl
    | [ |- context[hyp_free_vars (mk_hyp _ _)] ] => rewrite hyp_free_vars_mk_hyp; repnd; allsimpl
    | [ |- context[hyp_free_vars (mk_hhyp _ _)] ] => rewrite hyp_free_vars_mk_hhyp; repnd; allsimpl
    | [ |- context[filter _ (app _ _)] ] => rewrite filter_app; repnd; allsimpl
    | [ |- context[filter _ (snoc _ _)] ] => rewrite filter_snoc; repnd; allsimpl
    (* trw_h in context in hyps *)
    | [ H : context [LIn _ (snoc _ _)] |- _ ] => trw_h in_snoc H; repnd; allsimpl
    | [ H : context [LIn _ (app _ _)] |- _ ] => trw_h in_app_iff H; repnd; allsimpl
    (* trw_h in context in concl *)
    | [ |- context [LIn _ (snoc _ _)] ] => trw in_snoc; repnd; allsimpl
    | [ |- context [LIn _ (app _ _)] ] => trw in_app_iff; repnd; allsimpl
    (* trw_h *)
    | [ H : vs_wf_hypotheses _ (app _ _) |- _ ] => trw_h vs_wf_hypotheses_app H; repnd; allsimpl
    | [ H : vs_wf_hypotheses _ (snoc _ _) |- _ ] => trw_h vs_wf_hypotheses_snoc H; repnd; allsimpl
    | [ H : wf_hypotheses (app _ _) |- _ ] => trw_h wf_hypotheses_app H; repnd; allsimpl
    | [ H : wf_hypotheses (snoc _ _) |- _ ] => trw_h wf_hypotheses_snoc H; repnd; allsimpl
    | [ H : isprog_vars _ _ |- _ ] => trw_h isprog_vars_eq H; repnd; allsimpl
    | [ H : disjoint (snoc _ _) _ |- _ ] => trw_h disjoint_snoc_l H; repnd; allsimpl
    | [ H : disjoint _ (snoc _ _) |- _ ] => trw_h disjoint_snoc_r H; repnd; allsimpl
    | [ H : subvars nil _ |- _ ] => trw_h subvars_nil_l_iff H
    | [ H : subvars (app _ _) _ |- _ ] => trw_h subvars_app_l H; repnd; allsimpl
    | [ H : subvars (cons _ _) _ |- _ ] => trw_h subvars_cons_l H; repnd; allsimpl
    | [ H : subvars _ _ |- _ ] => trw_h subvars_prop H; repnd; allsimpl
    | [ H : nt_wf _ |- _ ] => trw_h nt_wf_eq H; repnd; allsimpl
    (* trw *)
    | [ |- context[subvars _ _] ] => trw subvars_prop; allsimpl
    (* apply *)
    | [ H : vs_wf_hypotheses _ _ |- _ ] => apply vs_wf_hypotheses_implies in H; repnd
    | [ H : vswf_hypotheses _ _ |- _ ] => apply vswf_hypotheses_nil_implies in H; repnd
    | [ H : ~ (_ \/ _) |- _ ] => apply not_or in H; repnd
    | [ H : !(_ [+] _) |- _ ] => apply not_over_or in H; repnd
  end; GC.

Ltac dwfseq := repeat dwfseq_step.

Tactic Notation "vr_seq_true" :=
  rw @sequent_true_eq_VR;
  rw @VR_sequent_true_all;
  simpl;
  introv ext sim eqh;
  introv;
  proof_irr;
  GC.

 Ltac vr_seq_true_ltac H :=
  trw_h sequent_true_eq_VR  H;
  trw_h VR_sequent_true_ex  H;
  simpl in H.

Tactic Notation "vr_seq_true" "in" ident(H) :=
  vr_seq_true_ltac H.

Ltac subst_app_step :=
  match goal with
    | [ |- context[lsubstc ?t ?w (?s1 ++ ?s2) ?c] ] =>
        let w' := fresh "w'" in
        let c' := fresh "c'" in
        let h  := fresh "h"  in
          generalize (lsubstc_csubst_ex2 t s1 s2 w c);
        intro h;
        destruct h as [w' h];
        destruct h as [c' h];
        rewrite <- h;
        clear h;
        proof_irr

    | [ H : context[lsubstc ?t ?w (?s1 ++ ?s2) ?c] |- _ ] =>
        let w' := fresh "w'" in
        let c' := fresh "c'" in
        let h  := fresh "h"  in
          generalize (lsubstc_csubst_ex2 t s1 s2 w c);
        intro h;
        destruct h as [w' h];
        destruct h as [c' h];
        rewrite <- h in H;
        clear h;
        proof_irr;
        GC
  end.

Ltac subst_app := repeat subst_app_step.
