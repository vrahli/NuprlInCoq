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
Require Import dest_close.


Lemma eq_term_equals_preserves_per_req_eq {o} :
  forall lib (a1 a2 : @cterm o) eqa1 eqa2,
    (eqa1 <=2=> eqa2)
    -> (per_req_eq lib a1 a2 eqa1) <=2=> (per_req_eq lib a1 a2 eqa2).
Proof.
  introv e; introv; unfold per_req_eq; split; intro h; exrepnd; spcast.

  - apply e in h3.
    apply e in h4.
    apply e in h1.
    exists x1 x2; dands; spcast; auto.

  - apply e in h3.
    apply e in h4.
    apply e in h1.
    exists x1 x2; dands; spcast; auto.
Qed.

Lemma per_req_eq_respects_cequivc {o} :
  forall lib (a1 a2 b1 b2 : @cterm o) eqa,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> term_equality_respecting lib eqa
    -> cequivcn lib a1 b1
    -> cequivcn lib a2 b2
    -> (per_req_eq lib a1 a2 eqa) <=2=> (per_req_eq lib b1 b2 eqa).
Proof.
  introv sym trans resp ceq1 ceq2; introv; unfold per_req_eq; split; intro h; exrepnd; spcast.

  - exists x1 x2; dands; spcast; auto.

    + apply (trans _ a1).

      * apply sym.
        apply resp; spcast; auto.
        apply (trans _ a2); auto.

      * apply (trans _ a2); auto.
        apply resp; spcast; auto.
        apply (trans _ a1); auto.

    + apply (trans _ a1); auto.
      apply sym.
      apply resp; spcast; auto.
      apply (trans _ a2); auto.

    + apply (trans _ a2); auto.
      apply sym; apply resp; spcast; auto.
      apply (trans _ a1); auto.

  - exists x1 x2; dands; spcast; auto.

    + apply (trans _ b1).

      * apply sym; apply resp;[|spcast; apply cequivcn_sym;auto].
        apply (trans _ b2); auto.

      * apply (trans _ b2); auto.
        apply resp;[|spcast;apply cequivcn_sym;auto].
        apply (trans _ b1); auto.

    + apply (trans _ b1); auto.
      apply sym.
      apply resp;[|spcast; apply cequivcn_sym;auto].
      apply (trans _ b2); auto.

    + apply (trans _ b2); auto.
      apply sym;apply resp;[|spcast;apply cequivcn_sym;auto].
      apply (trans _ b1); auto.
Qed.

Lemma per_req_eq_respects_eqorceq {o} :
  forall lib (a1 a2 b1 b2 : @cterm o) eqa,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> term_equality_respecting lib eqa
    -> eqorceq lib eqa a1 b1
    -> eqorceq lib eqa a2 b2
    -> (per_req_eq lib a1 a2 eqa) <=2=> (per_req_eq lib b1 b2 eqa).
Proof.
  introv sym trans resp ceq1 ceq2; introv; unfold per_req_eq; split; intro h; exrepnd; spcast;
    exists x1 x2; dands; spcast; auto.

    + apply (trans _ a1).

      * apply sym.
        eapply eqorceq_implies_eq; eauto.

      * apply (trans _ a2); auto.
        eapply eqorceq_implies_eq; eauto.

    + apply (trans _ a1); auto.
      apply sym.
      eapply eqorceq_implies_eq; eauto.

    + apply (trans _ a2); auto.
      apply sym.
      eapply eqorceq_implies_eq; eauto.

    + apply (trans _ b1).

      * eapply eqorceq_implies_eq2; eauto.

      * apply (trans _ b2); auto.
        apply sym.
        eapply eqorceq_implies_eq2; eauto.

    + apply (trans _ b1); auto.
      eapply eqorceq_implies_eq2; eauto.

    + apply (trans _ b2); auto.
      eapply eqorceq_implies_eq2; eauto.
Qed.

Lemma close_type_system_req {p} :
  forall lib (ts : cts(p)),
  forall T T' (eq : per) A B a1 a2 b1 b2 eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valcn lib T (mkcn_requality a1 a2 A)
    -> computes_to_valcn lib T' (mkcn_requality b1 b2 B)
    -> close lib ts A B eqa
    -> eqorceq lib eqa a1 b1
    -> eqorceq lib eqa a2 b2
    -> eq <=2=> (per_req_eq lib a1 a2 eqa)
    -> per_req lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A B eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp1 comp2 cla eo1 eo2 eqiff per tysysa.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_req".
    clear per.
    allunfold @per_req; exrepnd.
    introv.
    spcast; allrw.
    ccomputes_to_eqval.
    revert t1 t2.

    unfold type_sys_props in tysysa; repnd.
    pose proof (tysysa3 B0 eqa0) as w; repeat autodimp w hyp; repnd.
    pose proof (tysysa0 B0 eqa0) as q; autodimp q hyp.
    apply eq_term_equals_preserves_per_req_eq; auto.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
      allunfold @per_req; exrepd;
        ccomputes_to_eqval;
        apply CL_req; unfold per_req.

    exists A B0 a1 a2 b0 b3 eqa0; dands; spcast; auto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|].
    auto.

  + SCase "type_value_respecting".
    repndors; subst;
      apply CL_req; allunfold @per_req; sp;
        ccomputes_to_eqval.

    {
      duplicate comp1 as c0.
      apply cequivcn_mkcn_requality with (t' := T3) in c0; sp.
      exists A c' a1 a2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp)).

      unfold type_sys_props in tysysa; repnd.
      pose proof (tysysa4 A c') as q; repeat (autodimp q hyp).
    }

    {
      duplicate comp2 as c0.
      apply cequivcn_mkcn_requality with (t' := T3) in c0; sp.
      exists B c' b1 b2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp)).

      { unfold type_sys_props in tysysa; repnd.
        apply tysysa4; auto. }

      { eapply eq_term_equals_trans;[exact eqiff|].
        unfold type_sys_props in tysysa; repnd.
        apply per_req_eq_respects_eqorceq; auto. }
    }

  + SCase "term_symmetric".
    unfold term_equality_symmetric; introv e.
    rw eqiff in e; apply eqiff.
    unfold per_req_eq in e; unfold per_req_eq; exrepnd; spcast.
    exists x2 x1; dands; spcast; auto.

    { unfold type_sys_props in tysysa; repnd.
      apply (tysysa6 _ a2); auto. }

    { unfold type_sys_props in tysysa; repnd.
      apply (tysysa6 _ a1); auto. }

  + SCase "term_transitive".
    introv e1 e2.
    rw eqiff in e1; rw eqiff in e2; apply eqiff.
    unfold per_req_eq in e1, e2; unfold per_req_eq; exrepnd; spcast.
    computes_to_eqval.
    exists x0 x2; dands; spcast; auto.

  + SCase "term_value_respecting".
    introv e ceq; spcast.
    apply eqiff in e; apply eqiff.
    unfold per_req_eq in e; unfold per_req_eq; exrepnd; spcast; computes_to_eqval.
    eapply cequivcn_mkcn_refl in ceq;[|eauto]; exrepnd.
    exists x1 a'; dands; spcast; auto.

    unfold type_sys_props in tysysa; repnd.
    apply (tysysa6 _ x1); auto.
    apply tysysa7; spcast; auto.
    apply (tysysa6 _ a1); auto.

  + SCase "type_gsymmetric".
    split; intro h; dclose_lr; apply CL_req; clear per;
      unfold per_req in h0; unfold per_req; exrepnd; spcast; computes_to_eqval.

    {
      unfold type_sys_props in tysysa; repnd.
      pose proof (tysysa0 B0 eqa0) as q; autodimp q hyp.
      exists B0 A b0 b3 a1 a2 eqa0; dands; spcast; auto.

      { eapply (tysysa8 A); auto. }

      { eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_eq_term_equals in h4;[|eauto].
        apply eqorceq_sym; auto. }

      { eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        apply eqorceq_sym; auto. }

      { eapply eq_term_equals_trans;[eauto|].
        eapply eq_term_equals_trans;
          [apply eq_term_equals_preserves_per_req_eq;
           apply eq_term_equals_sym;eauto|].
        eapply eq_term_equals_trans;
          [|apply eq_term_equals_preserves_per_req_eq;eauto].
        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        apply per_req_eq_respects_eqorceq; auto. }
    }

    {
      unfold type_sys_props in tysysa; repnd.
      pose proof (tysysa8 A A0 eqa0) as q; autodimp q hyp.
      apply q in h3.
      pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.
      exists A A0 a1 a2 a0 a3 eqa0; dands; spcast; auto.

      { eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_eq_term_equals in h4;[|eauto].
        apply eqorceq_sym; auto. }

      { eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        apply eqorceq_sym; auto. }

      { eapply eq_term_equals_trans;[eauto|].
        eapply eq_term_equals_trans;
          [apply eq_term_equals_preserves_per_req_eq;
           apply eq_term_equals_sym;eauto|].
        eapply eq_term_equals_trans;
          [|apply eq_term_equals_preserves_per_req_eq;eauto].
        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        apply per_req_eq_respects_eqorceq; auto. }
    }

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr; clear per;
      allunfold @per_req; exrepnd;
        ccomputes_to_eqval;
        dands; apply CL_req; unfold per_req.

    { exists A0 B1 a0 a3 b4 b5 eqa0; dands; spcast; auto.

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa A A0 B1 eqa0 eqa1) as q; repeat (autodimp q hyp); tcsp.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 A A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 A A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }
    }

    { exists A0 B1 a0 a3 b4 b5 eqa0; dands; spcast; auto.

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa A A0 B1 eqa0 eqa1) as q; repeat (autodimp q hyp); tcsp.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 A A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 A A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        eapply eq_term_equals_trans;[eauto|].

        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 A A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].

        eapply eq_term_equals_trans;
          [apply eq_term_equals_preserves_per_req_eq;apply eq_term_equals_sym;eauto|].
        eapply eq_term_equals_trans;
          [|apply eq_term_equals_preserves_per_req_eq;eauto].
        apply per_req_eq_respects_eqorceq; auto; apply eqorceq_sym; auto.
      }
    }

    { exists A0 B1 a0 a3 b4 b5 eqa0; dands; spcast; auto.

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa B A0 B1 eqa0 eqa1) as q; repeat (autodimp q hyp); tcsp.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 B A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 B A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }
    }

    { exists A0 B1 a0 a3 b4 b5 eqa0; dands; spcast; auto.

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa B A0 B1 eqa0 eqa1) as q; repeat (autodimp q hyp); tcsp.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 B A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 B A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].
        eapply eqorceq_eq_term_equals;[apply eq_term_equals_sym;eauto|].
        eapply eqorceq_trans; eauto.
      }

      {
        eapply eq_term_equals_trans;[eauto|].

        unfold type_sys_props in tysysa; repnd.
        pose proof (tysysa0 B1 eqa1) as q; autodimp q hyp.
        pose proof (tysysa8 B A0 eqa0) as w; autodimp w hyp.
        apply w in h3; clear w.
        pose proof (tysysa0 A0 eqa0) as w; autodimp w hyp.

        eapply eqorceq_eq_term_equals in h4;[|eauto].
        eapply eqorceq_eq_term_equals in h5;[|eauto].
        eapply eqorceq_eq_term_equals in h10;[|eauto].
        eapply eqorceq_eq_term_equals in h11;[|eauto].

        eapply eq_term_equals_trans;
          [apply eq_term_equals_preserves_per_req_eq;apply eq_term_equals_sym;eauto|].
        eapply eq_term_equals_trans;
          [|apply eq_term_equals_preserves_per_req_eq;eauto].
        apply per_req_eq_respects_eqorceq; auto; apply eqorceq_sym; auto.
      }
    }
Qed.
