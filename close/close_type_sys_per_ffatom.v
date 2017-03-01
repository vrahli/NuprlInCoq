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


Require Import type_sys_useful.
Require Import dest_close.



Lemma eq_term_equals_per_ffatom_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)) u x,
    (eqa1 <=2=> eqa2)
    -> (per_ffatom_eq lib eqa1 u x) <=2=> (per_ffatom_eq lib eqa2 u x).
Proof.
  introv eqt.
  unfold per_ffatom_eq; introv; split; intro k; exrepnd;
  dands; auto; exists y; dands; auto; apply eqt; auto.
Qed.

Lemma per_ffatom_eq_symmetric {p} :
  forall lib (eq : per(p)) x u t1 t2,
    term_equality_symmetric eq
    -> per_ffatom_eq lib eq x u t1 t2
    -> per_ffatom_eq lib eq x u t2 t1.
Proof.
  introv tes per.
  allunfold @per_ffatom_eq; exrepnd; dands; allrw; try (complete sp).
  exists y; dands; auto.
Qed.

Lemma per_ffatom_eq_transitive {p} :
  forall lib (eq : per(p)) x u t1 t2 t3,
    term_equality_transitive eq
    -> per_ffatom_eq lib eq x u t1 t2
    -> per_ffatom_eq lib eq x u t2 t3
    -> per_ffatom_eq lib eq x u t1 t3.
Proof.
  introv tet per1 per2.
  allunfold @per_ffatom_eq; exrepnd.
  dands; try (allrw; complete sp).
  exists y; dands; auto.
Qed.

Lemma per_ffatom_eq_cequiv {p} :
  forall lib (eq : per(p)) x u t1 t2,
    term_equality_respecting lib eq
    -> cequivc lib t1 t2
    -> per_ffatom_eq lib eq x u t1 t1
    -> per_ffatom_eq lib eq x u t1 t2.
Proof.
  introv res ceq per.
  allunfold @per_ffatom_eq; repnd; dands; auto; spcast.
  apply cequivc_axiom in ceq; auto.
Qed.

Lemma cequiv_mk_ffatom {p} :
  forall lib t t' T x a,
    computes_to_value lib t (mk_free_from_atom T x a)
    -> cequiv lib t t'
    -> {T', x', a' : @NTerm p $
         computes_to_value lib t' (mk_free_from_atom T' x' a')
         # cequiv lib T T'
         # cequiv lib x x'
         # cequiv lib a a'}.
Proof. prove_cequiv_mk.
Qed.

Lemma cequivc_mkc_ffatom {p} :
  forall lib t t' T x a,
    computes_to_valc lib t (mkc_free_from_atom T x a)
    -> cequivc lib t t'
    -> {T', x', a' : @CTerm p $
         computes_to_valc lib t' (mkc_free_from_atom T' x' a')
         # cequivc lib T T'
         # cequivc lib x x'
         # cequivc lib a a'}.
Proof.
  unfold computes_to_valc, cequivc; intros; destruct_cterms; allsimpl.
  generalize (cequiv_mk_ffatom lib x3 x2 x1 x x0); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_free_from_atom_iff; repnd.
  exists (mk_cterm T' isp0) (mk_cterm x' isp1) (mk_cterm a' isp); simpl; sp.
Qed.

Lemma cequivc_utoken {o} :
  forall lib t t' u,
    computes_to_valc lib t (mkc_utoken u)
    -> @cequivc o lib t t'
    -> computes_to_valc lib t' (mkc_utoken u).
Proof.
  introv comp ceq.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_canonical_form with (t' := t') in comp; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma per_ffatom_eq_elt {o} :
  forall lib (eqa : per(o)) u x1 x2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> eqa x1 x2
    -> (per_ffatom_eq lib eqa u x1) <=2=> (per_ffatom_eq lib eqa u x2).
Proof.
  introv sym trans eqxs.
  unfold per_ffatom_eq; introv; split; introv k; exrepnd; dands; auto;
  exists y; dands; auto.
  apply (trans x2 x1 y); sp.
  apply (trans x1 x2 y); sp.
Qed.

Lemma close_type_system_ffatom {p} :
  forall lib (ts : cts(p)) T (eq : per) A x a eqa (u : get_patom_set p),
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_free_from_atom A x a)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> eqa x x
    -> computes_to_valc lib a (mkc_utoken u)
    -> (eq <=2=> (per_ffatom_eq lib eqa u x))
    -> per_ffatom lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa eqxs ca eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_ffatom in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    apply eq_term_equals_per_ffatom_eq_if; auto.

    dts_props tsa uv tv te tes tet tev.
    eapply uv; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_ffatom.
    exists A x a eqa u; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_ffatom.
    eapply cequivc_mkc_ffatom in comp;[|eauto]; exrepnd.
    pose proof (cequiv.cequivc_utoken lib a a' u) as q; repeat (autodimp q hyp).
    exists T'0 x' a' eqa u; dands; spcast; auto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsa uv tv te tes tet tev.
      apply (tet _ x);[apply tes|]; apply tev; spcast; auto. }
    { eapply eq_term_equals_trans;[eauto|].
      dts_props tsa uv tv te tes tet tev; repnd.
      apply per_ffatom_eq_elt; auto.
      apply tev; spcast; auto. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_ffatom_eq_symmetric; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_ffatom_eq_transitive; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.
    dts_props tsa uva tva tea tesa teta teva; repnd.
    eapply per_ffatom_eq_cequiv; spcast; eauto.
Qed.
