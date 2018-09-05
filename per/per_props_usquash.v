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

  Authors: Vincent Rahli

 *)


Require Export usquash.
Require Export per_props_psquash.



Lemma member_iff_inhabited_mkc_apply2_mkc_usquash_per {o} :
  forall lib (t1 t2 T : @CTerm o),
    inhabited_type lib (mkc_apply2 (mkc_usquash_per nvarx nvary T) t1 t2)
    <=> inhabited_type lib T.
Proof.
  introv.

  split; introv inh.

  - eapply inhabited_type_respects_cequivc in inh;
    [|apply cequivc_beta2].
    rw @mkcv_lam_substc in inh; try (complete (intro xx; ginv)).

    eapply inhabited_type_respects_cequivc in inh;
      [|apply cequivc_beta].

    autorewrite with slow in *; auto.

  - eapply inhabited_type_respects_cequivc;
    [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply inhabited_type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    autorewrite with slow in *; auto.
Qed.

Lemma implies_tequality_mkc_usquash {o} :
  forall lib (t1 t2 : @CTerm o),
    type lib t1
    -> type lib t2
    -> (inhabited_type lib t1 <=> inhabited_type lib t2)
    -> tequality lib (mkc_usquash t1) (mkc_usquash t2).
Proof.
  introv tt1 tt2 tiff.
  unfold mkc_usquash.
  rw @tequality_mkc_pertype.
  dands.

  - (* type 1 *)
    introv.
    unfold mkc_usquash_per.

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    autorewrite with slow in *; auto.

  - (* type 2 *)
    introv.
    unfold mkc_psquash_per.

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta2|].
    rw @mkcv_lam_substc; try (complete (intro xx; ginv)).

    eapply type_respects_cequivc;
      [apply cequivc_sym;apply cequivc_beta|].

    autorewrite with slow in *; auto.

  - (* extensional eq *)
    introv.
    allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; tcsp.

  - (* PER *)
    unfold is_per_type; dands.

    (* symmetry *)
    + introv inh.
      allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; sp.

    (* transitivity *)
    + introv inh1 inh2.
      allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; sp.
Qed.

Lemma tequality_mkc_usquash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib (mkc_usquash t1) (mkc_usquash t2)
    <=> (type lib t1
         # type lib t2
         # (inhabited_type lib t1 <=> inhabited_type lib t2)).
Proof.
  introv; split; intro k; try (apply implies_tequality_mkc_usquash; tcsp);[].

  unfold mkc_usquash in k.
  rw @tequality_mkc_pertype in k; repnd.

  (* let's get that t1 is a type *)
  pose proof (k0 mkc_axiom mkc_axiom) as tt1.
  unfold mkc_usquash_per in tt1.

  eapply type_respects_cequivc in tt1;[|apply cequivc_beta2].
  rw @mkcv_lam_substc in tt1; try (complete (intro xx; ginv)).
  eapply type_respects_cequivc in tt1;[|apply cequivc_beta].
  autorewrite with slow in *.

  (* let's get that t2 is a type *)
  pose proof (k1 mkc_axiom mkc_axiom) as tt2.
  unfold mkc_usquash_per in tt2.

  eapply type_respects_cequivc in tt2;[|apply cequivc_beta2].
  rw @mkcv_lam_substc in tt2; try (complete (intro xx; ginv)).
  eapply type_respects_cequivc in tt2;[|apply cequivc_beta].
  autorewrite with slow in *.

  dands; auto;[].

  pose proof (k2 mkc_axiom mkc_axiom) as k2.
  allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; tcsp.
Qed.

Lemma sp_implies_tequality_mkc_usquash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> tequality lib (mkc_usquash t1) (mkc_usquash t2).
Proof.
  introv teq.
  apply tequality_mkc_usquash.
  dands; eauto 3 with slow.

  - apply tequality_refl in teq; auto.

  - apply tequality_sym in teq; apply tequality_refl in teq; auto.

  - introv; split; intro mem; eapply inhabited_type_tequality; eauto.
    apply tequality_sym; auto.
Qed.

Lemma implies_equality_in_mkc_usquash {o} :
  forall lib (a b T : @CTerm o),
    inhabited_type lib T
    -> equality lib a b (mkc_usquash T).
Proof.
  introv inh.
  unfold mkc_usquash.

  apply equality_in_mkc_pertype2; dands.

  - apply member_iff_inhabited_mkc_apply2_mkc_usquash_per; sp.

  - apply sp_implies_tequality_mkc_usquash.
    unfold inhabited_type in inh; exrepnd.
    apply inhabited_implies_tequality in inh0; auto.
Qed.

Lemma equality_in_mkc_usquash {o} :
  forall lib (a b T : @CTerm o),
    equality lib a b (mkc_usquash T)
    <=> inhabited_type lib T.
Proof.
  introv; split; introv k; try (apply implies_equality_in_mkc_usquash; sp);[].
  unfold mkc_usquash in k.

  apply equality_in_mkc_pertype2 in k; repnd.
  apply member_iff_inhabited_mkc_apply2_mkc_usquash_per in k0; sp.
Qed.

Lemma equality_mkc_usquash_in_uni {o} :
  forall lib (t1 t2 : @CTerm o) i,
    equality lib (mkc_usquash t1) (mkc_usquash t2) (mkc_uni i)
    <=> (member lib t1 (mkc_uni i)
         # member lib t2 (mkc_uni i)
         # (inhabited_type lib t1 <=> inhabited_type lib t2)).
Proof.
  introv.
  sp_iff Case; introv h; repnd.

  - Case "->".
    apply mkc_pertype_equality_in_uni in h; repnd.

    pose proof (h0 mkc_axiom mkc_axiom) as h0.
    eapply member_respects_cequivc in h0;[|apply cequivc_beta2].
    repeat (rw @mkcv_lam_substc in h0; try (complete (intro xx; ginv));[]).
    eapply member_respects_cequivc in h0;[|apply cequivc_beta].
    autorewrite with slow in *.

    pose proof (h1 mkc_axiom mkc_axiom) as h1.
    eapply member_respects_cequivc in h1;[|apply cequivc_beta2].
    repeat (rw @mkcv_lam_substc in h1; try (complete (intro xx; ginv));[]).
    eapply member_respects_cequivc in h1;[|apply cequivc_beta].
    autorewrite with slow in *.

    dands; auto.

    pose proof (h2 mkc_axiom mkc_axiom) as h2.
    allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; tcsp.

  - unfold mkc_usquash.
    apply mkc_pertype_equality_in_uni.
    dands; introv;
      [| | |].

    { eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      repeat (rw @mkcv_lam_substc; try (complete (intro xx; ginv));[]).
      eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      autorewrite with slow in *; auto. }

    { eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      repeat (rw @mkcv_lam_substc; try (complete (intro xx; ginv));[]).
      eapply member_respects_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      autorewrite with slow in *; auto. }

    { repeat rw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; tcsp. }

    { unfold is_per_type; dands.

      + introv inh.
        allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; sp.

      + introv inh1 inh2.
        allrw @member_iff_inhabited_mkc_apply2_mkc_usquash_per; sp. }
Qed.
