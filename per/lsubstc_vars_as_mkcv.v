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


Require Export per_props4.
Require Export sequents.


Ltac lsubstc_vars_as_mkcv :=
  match goal with

    (* ====== on hypotheses ====== *)

    | [ H : context[lsubstc_vars mk_tnat ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      pose proof (lsubstc_vars_mk_tnat_as_mkcv w s vs c) as hyp;
        rewrite hyp in H;
        clear hyp

    | [ H : context[lsubstc_vars (mk_squash ?t) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf := fresh "w" in
      let cv := fresh "c" in
      pose proof (lsubstc_vars_mk_squash_as_mkcv t w s vs c) as hyp;
        destruct hyp as [wf hyp];
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_cequiv ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_cequiv_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_approx ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_approx_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_apply ?t1 ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_apply_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_apply2 ?t1 ?t2 ?t3) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      pose proof (lsubstc_vars_mk_apply2_as_mkcv t1 t2 t3 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_int_eq ?t1 ?t2 ?t3 ?t4) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let wf4 := fresh "w4" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      let cv4 := fresh "c4" in
      pose proof (lsubstc_vars_mk_int_eq_as_mkcv t1 t2 t3 t4 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [wf4 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        destruct hyp as [cv4 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_lam ?v ?t) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      pose proof (lsubstc_vars_mk_lam_as_mkcv v t w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [cv1 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_function ?t1 ?v ?t2) ?w ?s ?vs ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_function_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    | [ H : context[lsubstc_vars (mk_var ?v) ?w ?s (?v :: ?vs) ?c] |- _ ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv1 v w s vs c ni) as hyp;
        rewrite hyp in H;
        clear ni hyp

    | [ H : context[lsubstc_vars (mk_var ?v) ?w ?s [?v1, ?v] ?c] |- _ ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv2 v v1 w s c ni) as hyp;
        rewrite hyp in H;
        clear ni hyp

    | [ H : context[lsubstc_vars ?t ?w ?s ?vs ?c] |- _ ] =>
      let ni  := fresh "ni" in
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      assert (disjoint vs (free_vars t)) as ni
          by (repeat (trw disjoint_cons_l);
              repeat (trw not_over_or);
              simpl;
              repeat (rewrite app_nil_r);
              repeat (trw in_remove_nvars);
              simpl;
              repeat propagate_true_step;
              dands; auto;
              intro xxx; repnd; repndors; auto;
              GC; match xxx with | _ => idtac end;
              tcsp);
        pose proof (lsubstc_vars_as_mk_cv t w s vs c ni) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear ni hyp;
        proof_irr

    | [ H : context[lsubstc ?t ?w (csub_filter ?s ?vs) ?c] |- _ ] =>
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      pose proof (lsubstc_csub_filter_eq t w s vs c) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp in H;
        clear hyp;
        proof_irr

    (* ====== on conclusion ====== *)

    | [ |- context[lsubstc_vars mk_tnat ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      pose proof (lsubstc_vars_mk_tnat_as_mkcv w s vs c) as hyp;
        rewrite hyp;
        clear hyp

    | [ |- context[lsubstc_vars (mk_squash ?t) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf := fresh "w" in
      let cv := fresh "c" in
      pose proof (lsubstc_vars_mk_squash_as_mkcv t w s vs c) as hyp;
        destruct hyp as [wf hyp];
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_cequiv ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_cequiv_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_approx ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_approx_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_apply ?t1 ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_apply_as_mkcv t1 t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_apply2 ?t1 ?t2 ?t3) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      pose proof (lsubstc_vars_mk_apply2_as_mkcv t1 t2 t3 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_int_eq ?t1 ?t2 ?t3 ?t4) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let wf2 := fresh "w2" in
      let wf3 := fresh "w3" in
      let wf4 := fresh "w4" in
      let cv1 := fresh "c1" in
      let cv2 := fresh "c2" in
      let cv3 := fresh "c3" in
      let cv4 := fresh "c4" in
      pose proof (lsubstc_vars_mk_int_eq_as_mkcv t1 t2 t3 t4 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [wf3 hyp];
        destruct hyp as [wf4 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        destruct hyp as [cv3 hyp];
        destruct hyp as [cv4 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_lam ?v ?t) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      pose proof (lsubstc_vars_mk_lam_as_mkcv v t w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [cv1 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_function ?t1 ?v ?t2) ?w ?s ?vs ?c] ] =>
      let hyp := fresh "hyp" in
      let wf1 := fresh "w1" in
      let cv1 := fresh "c1" in
      let wf2 := fresh "w2" in
      let cv2 := fresh "c2" in
      pose proof (lsubstc_vars_mk_function_as_mkcv t1 v t2 w s vs c) as hyp;
        destruct hyp as [wf1 hyp];
        destruct hyp as [wf2 hyp];
        destruct hyp as [cv1 hyp];
        destruct hyp as [cv2 hyp];
        rewrite hyp;
        clear hyp;
        proof_irr

    | [ |- context[lsubstc_vars (mk_var ?v) ?w ?s (?v :: ?vs) ?c] ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv1 v w s vs c ni) as hyp;
        rewrite hyp;
        clear ni hyp

    | [ |- context[lsubstc_vars (mk_var ?v) ?w ?s [?v1, ?v] ?c] ] =>
      let ni := fresh "ni" in
      let hyp := fresh "hyp" in
      assert (!LIn v (dom_csub s)) as ni
          by (repeat (rewrite @dom_csub_csub_filter);
              repeat (trw in_remove_nvars);
              repeat (trw in_single_iff);
              tcsp);
        pose proof (lsubstc_vars_mk_var_as_mkcv2 v v1 w s c ni) as hyp;
        rewrite hyp;
        clear ni hyp

    | [ |- context[lsubstc_vars ?t ?w ?s ?vs ?c] ] =>
      let ni  := fresh "ni" in
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      let xxx := fresh "xxx" in
      assert (disjoint vs (free_vars t)) as ni
          by (repeat (trw disjoint_cons_l);
              repeat (trw not_over_or);
              simpl;
              repeat (rewrite app_nil_r);
              repeat (trw in_remove_nvars);
              simpl;
              repeat propagate_true_step;
              dands; auto;
              intro xxx; repnd; repndors; auto;
              GC; match xxx with | _ => idtac end;
              tcsp);
        pose proof (lsubstc_vars_as_mk_cv t w s vs c ni) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear ni hyp;
        proof_irr

    | [ |- context[lsubstc ?t ?w (csub_filter ?s ?vs) ?c] ] =>
      let hyp := fresh "hyp" in
      let cv  := fresh "c" in
      pose proof (lsubstc_csub_filter_eq t w s vs c) as hyp;
        destruct hyp as [cv hyp];
        rewrite hyp;
        clear hyp;
        proof_irr
  end.
