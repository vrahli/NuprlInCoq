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



Lemma  tequality_mkc_partial_eq {o} :
  forall lib eq T,
  nuprl lib (mkc_partial T) (mkc_partial T) eq
  <=> {eqt : per,  nuprl lib T T eqt
        # (forall a : @CTerm o, eqt a a -> chaltsc lib a)
        # eq_term_equals eq (per_partial_eq lib eqt)}.
Proof.
  introv; split; introv X.
  - invertsn X; subst; try not_univ.
    allunfold @per_partial; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    allunfold @per_partial_eq. exrepnd.
    exists eqa.
    dands; sp.
  - exrepnd.
    apply CL_partial.
    unfold per_partial.
    exists T T eqt.
    dands; spcast; auto;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_partial).
Qed.

Lemma equality_partial_in_uni {o} :
  forall lib i (T1 T2 : @CTerm o),
  equality lib (mkc_partial T1) (mkc_partial T2) (mkc_uni i)
  <=> (equality lib T1 T2 (mkc_uni i) # (forall t, member lib t T1 -> chaltsc lib t)).
Proof.
  introv; split; intro teq; repnd.

  - destruct teq as [eq n]; repnd.
    inversion n0; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in n; exrepnd.
    inversion n1; try not_univ.
    allunfold @per_partial; exrepnd; spcast; computes_to_value_isvalue.
    allfold (@nuprli o lib j0).
    dands.
    exists eq.
    dands; auto.
    allrw.
    exists eqa0; auto.
    introv m.
    destruct m as [eqa' m]; repnd.
    allapply @nuprli_implies_nuprl.
    generalize (nuprl_uniquely_valued lib A1 eqa0 eqa'); intro k; repeat (autodimp k hyp).
    apply (nuprl_refl lib A1 A2); auto.
    apply k in m; discover; auto.

  - destruct teq0 as [eq n]; repnd.
    exists eq; dands; auto.
    inversion n0; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rw h0 in n; exrepnd.
    allfold (@nuprli o lib j0).
    allrw.
    exists (per_partial_eq lib eqa).
    apply CL_partial.
    exists T1 T2 eqa.
    dands; spcast; auto;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_partial).
    introv m.
    apply teq.
    exists eqa; sp.
    allapply @nuprli_implies_nuprl.
    apply nuprl_refl in n1; auto.
Qed.

(** %\noindent% We first characterize
    the central content of the formation rule for partial types.
    The proof is a straightforward consequence of the definition of
    [per_partial]. Like Crary%\cite{Crary:1998}%, we can form the 
    partial type 
    [mkc_partial T]
    only if the [T] is a total type.
    A type is a total type if all its members converge to a value.
    [chaltsc] is a lifted version of [hasvalue], i.e.,
    [chaltsc t] asserts [t] converges to a cononical form.
    
*)


Lemma tequality_mkc_partial {o} :
  forall lib (T1 T2 : @CTerm o),
  tequality lib (mkc_partial T1) (mkc_partial T2)
  <=> (tequality lib T1 T2 # (forall t, member lib t T1 -> chaltsc lib t)).
Proof.
  introv; split; intro teq; repnd.

  - destruct teq as [eq n].
    inversion n; subst; try not_univ.
    allunfold @per_partial; exrepnd; spcast; computes_to_value_isvalue.
    allfold @nuprl.
    dands.
    exists eqa; sp.
    introv m.
    destruct m as [eqa' m]; repnd.
    generalize (nuprl_uniquely_valued lib A1 eqa eqa'); intro k; repeat (autodimp k hyp).
    apply (nuprl_refl lib A1 A2); auto.
    apply k in m; discover; auto.

  - destruct teq0 as [eq n].
    exists (per_partial_eq lib eq).
    apply CL_partial.
    exists T1 T2 eq.
    dands; spcast; auto;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_partial).
    introv m.
    apply teq.
    exists eq; sp.
    apply nuprl_refl in n; auto.
Qed.


(** %\noindent% Now, We characterize when two elements are equal in a
     partial type.
    The proof is a straightforward consequence of the definition of
    [per_partial_eq] that is used in [per_partial].
*)

Lemma equality_in_mkc_partial {o} :
  forall lib (t t' T : @CTerm o),
    equality lib t t' (mkc_partial T)
    <=> (type lib (mkc_partial T)
        # (chaltsc lib t <=> chaltsc lib t')
        # (chaltsc lib t -> equality lib t t' T)).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_partial; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    allunfold @per_partial_eq. exrepnd.
    dands; auto; [exists eq; sp  |introv Hyp].
    unfold equality.
    exists eqa.
    dands; auto.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    apply tequality_mkc_partial_eq in e2. exrepnd.
    exists (per_partial_eq lib eqt); dands; auto.
    + apply CL_partial; unfold per_partial.
      exrepnd. exists T T eqt; sp; spcast;
      try (apply computes_to_valc_refl; apply iscvalue_mkc_partial).
    + unfold per_partial_eq. dands; auto.
      introv Hc.
      apply e in Hc.
      repnud Hc.
      exrepnd.
      apply (nuprl_uniquely_valued lib T _ eqt ) in Hc0;auto.
Qed.

Lemma not_chavaluec_bot {o} : forall lib, @chaltsc o lib mkc_bot -> False.
Proof.
  introv Hsc.
  spcast.
  allunfold @hasvaluec.
  allunfold @mkc_bot.
  allsimpl.
  apply (not_hasvalue_bot lib); auto.
Qed.

Lemma bot_in_partial_type {o} : forall lib (T : @CTerm o),
  type lib (mkc_partial T)
  -> equality lib mkc_bot mkc_bot (mkc_partial T).
Proof.
  introv Ht.
  apply equality_in_mkc_partial.
  dands; auto;[].
  introv Hc.
  provefalse.
  apply (not_chavaluec_bot lib); auto.
Qed.
