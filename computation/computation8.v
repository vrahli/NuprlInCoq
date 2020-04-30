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

  Authors: Abhishek Anand
           Vincent Rahli
           Mark Bickford

*)


Require Export computation7.



Lemma computes_steps_prinargs_comp2 {p} :
  forall lib a ntp1 ntp2 lbt k1 k2 ntpc1 ntpc2,
    compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
    -> iswfpk a ntpc1
    -> compute_at_most_k_steps lib k2 ntp2 = @csuccess p ntpc2
    -> {j : nat $ compute_at_most_k_steps lib j (oterm (NCan (NCompOp a))
                        ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
            = csuccess (oterm (NCan (NCompOp a))
                              ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt)))
                       # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind];  introv H1c H1v H2c.
  - inverts H2c.
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end.
    exrepnd. exists j. dands; spc. omega.
  - rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [|ntp2o ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail|].

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v eq_refl) as XX. exrepnd.
    destruct csk as [sckv| csko csklbt]; [inverts Hck; fail|].

    dopid csko as [cskoc| cskon | csknsw | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j). dands;[|omega].
      allsimpl.
      rw XX1.
      unfold iswfpk in H1v; destruct a.
      * unfold isinteger in H1v; exrepnd; subst.
        csunf; simpl.
        rw Hck;sp.
      * unfold ispk in H1v; exrepnd; subst.
        csunf; simpl; allrw @pk2term_eq; dcwf h; allsimpl;
        try (rw Hck;sp);[].
        unfold co_wf in Heqh; allrw @get_param_from_cop_pk2can; ginv.
    + Case "NSwapCs2".
      exists (S j). dands;[|omega].
      allsimpl.
      rw XX1.
      unfold iswfpk in H1v; destruct a.
      * unfold isinteger in H1v; exrepnd; subst.
        csunf; simpl.
        rw Hck;sp.
      * unfold ispk in H1v; exrepnd; subst.
        csunf; simpl; allrw @pk2term_eq; dcwf h; allsimpl;
        try (rw Hck;sp);[].
        unfold co_wf in Heqh; allrw @get_param_from_cop_pk2can; ginv.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      exists (S j). dands;[|omega].
      simpl.
      rw XX1.
      unfold iswfpk in H1v; destruct a.
      * unfold isinteger in H1v; exrepnd; subst.
        csunf; simpl.
        rw Hck;sp.
      * unfold ispk in H1v; exrepnd; subst.
        csunf; simpl; allrw @pk2term_eq; dcwf h; allsimpl;
        try (rw Hck;sp);[].
        unfold co_wf in Heqh; allrw @get_param_from_cop_pk2can; ginv.
Qed.

Lemma reduce_to_prinargs_comp2 {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt ntpv1 ntpc2,
    reduces_to lib ntp1 ntpv1
    -> iswfpk a ntpv1
    -> reduces_to lib ntp2 ntpc2
    -> reduces_to lib (oterm (NCan (NCompOp a))
                             ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                  (oterm (NCan (NCompOp a))
                         ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv H1c isc H2c.
  repnud H2c.
  repnud H1c.
  exrepnd.
  eapply @computes_steps_prinargs_comp2
  with (lbt:=lbt)
         (a:=a)
         (ntpc1:= ntpv1)
         (ntpc2:= ntpc2) in H1c0;
    exrepnd; eauto.
  unfolds_base; exists j; eauto.
Qed.

Lemma computes_steps_prinargs_arith2 {p} :
  forall lib a ntp1 ntp2 lbt k1 k2 ntpc1 ntpc2,
    compute_at_most_k_steps lib k1 ntp1 = csuccess ntpc1
    -> isinteger ntpc1
    -> compute_at_most_k_steps lib k2 ntp2 = @csuccess p ntpc2
    -> {j : nat $ compute_at_most_k_steps lib j (oterm (NCan (NArithOp a))
                        ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
            = csuccess (oterm (NCan (NArithOp a))
                              ((bterm [] ntpc1)::((bterm [] ntpc2)::lbt)))
                       # j<= (k1+k2)}.
Proof.
  induction k2 as [| k2 Hind];  introv H1c H1v H2c.
  - inverts H2c.
    match goal with
    | [ |- {_ : nat $ compute_at_most_k_steps _ _
          (oterm (NCan ?no) (?h :: ?tl)) = _ # _ }] =>
     apply @computes_atmost_ksteps_prinarg with (lbt:= tl)
      (op:=no) in H1c
    end.
    exrepnd. exists j. dands; spc. omega.
  - rename H2c into Hck. rename k2 into k.
    destruct ntp2 as [|ntp2o ntp2lbt];
      [rw @compute_at_most_steps_var in Hck; spc; fail|].

    allsimpl.
    remember (compute_at_most_k_steps lib k (oterm ntp2o ntp2lbt)) as ck.
    destruct ck as [csk | cf]; spc;[].
    pose proof (Hind _ csk H1c H1v eq_refl) as XX. exrepnd.
    unfold isinteger in H1v; exrepnd; subst.
    destruct csk as [sckv|csko csklbt]; [inverts Hck; fail|].

    dopid csko as [cskoc| cskon | csknsw | cskexc | cskabs] Case.
    + Case "Can".
      simpl in Hck. inverts Hck. exists j; sp. omega.
    + Case "NCan".
      exists (S j). dands;[|omega].
      simpl.
      rw XX1.
      csunf; simpl.
      rw Hck;sp.
    + Case "NSwapCs2".
      exists (S j). dands;[|omega].
      simpl.
      rw XX1.
      csunf; simpl.
      rw Hck;sp.
    + Case "Exc".
      rw @compute_step_exception in Hck; sp; inversion Hck; subst; GC.
      exists j; sp; omega.
    + Case "Abs".
      exists (S j). dands;[|omega].
      simpl.
      rw XX1.
      csunf; simpl.
      rw Hck;sp.
Qed.

Lemma reduce_to_prinargs_arith2 {p} :
  forall lib a (ntp1 ntp2 : @NTerm p) lbt ntpv1 ntpc2,
    reduces_to lib ntp1 ntpv1
    -> isinteger ntpv1
    -> reduces_to lib ntp2 ntpc2
    -> reduces_to lib (oterm (NCan (NArithOp a))
                             ((bterm [] ntp1)::((bterm [] ntp2)::lbt)))
                  (oterm (NCan (NArithOp a))
                         ((bterm [] ntpv1)::((bterm [] ntpc2)::lbt))).
Proof.
  introv H1c isc H2c.
  repnud H2c.
  repnud H1c.
  exrepnd.
  eapply @computes_steps_prinargs_arith2
  with (lbt:=lbt)
         (a:=a)
         (ntpc1:= ntpv1)
         (ntpc2:= ntpc2) in H1c0;
    exrepnd; eauto.
  unfolds_base; exists j; eauto.
Qed.

Lemma reduces_to_fresh2 {o} :
  forall (lib : plibrary) (t u : @NTerm o) (v : NVar) a,
  wf_term t
  -> !LIn a (get_utokens_lib lib t)
  -> reduces_to lib (subst t v (mk_utoken a)) u
  -> {z : NTerm
      $ reduces_to lib (mk_fresh v t) (mk_fresh v z)
      # alpha_eq z (subst_utokens u [(a, mk_var v)])}.
Proof.
  introv w ni r.

  pose proof (reduces_to_change_utok_sub
                lib t u
                [(v,mk_utoken a)]
                [(v,mk_utoken (get_fresh_atom lib t))]) as r'.
  allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
  allrw disjoint_singleton_l.
  repeat (autodimp r' hyp); eauto 3 with slow.
  { apply nr_ut_sub_cons; eauto with slow.
    intro i; apply get_fresh_atom_prop_and_lib. }
  { apply get_fresh_atom_prop_and_lib. }
  exrepnd.

  allrw disjoint_singleton_l.
  allrw @fold_subst.

  pose proof (reduces_to_fresh lib t s v) as h; simpl in h.
  repeat (autodimp h hyp); exrepnd.
  exists z; dands; auto.

  remember (get_fresh_atom lib t) as a'.

  pose proof (alpha_eq_subst_utokens
                s (subst w0 v (mk_utoken a'))
                [(a', mk_var v)]
                [(a', mk_var v)]) as aeqs1.
  repeat (autodimp aeqs1 hyp); eauto 3 with slow.
  pose proof (simple_alphaeq_subst_utokens_subst w0 v a') as aeqs2.
  autodimp aeqs2 hyp.
  { subst; intro i.
    eapply get_utokens_subset_get_utokens_lib in i.
    apply r'4 in i; apply get_fresh_atom_prop_and_lib in i; sp. }
  eapply alpha_eq_trans in aeqs2;[|exact aeqs1]; clear aeqs1.
  eapply alpha_eq_trans in aeqs2;[|exact h0].
  eapply alpha_eq_trans;[exact aeqs2|].

  pose proof (alpha_eq_subst_utokens
                u (subst w0 v (mk_utoken a))
                [(a, mk_var v)]
                [(a, mk_var v)]) as aeqs1.
  repeat (autodimp aeqs1 hyp); eauto 3 with slow.
  pose proof (simple_alphaeq_subst_utokens_subst w0 v a) as aeqs3.
  autodimp aeqs3 hyp.
  { intro i.
    eapply get_utokens_subset_get_utokens_lib in i; tcsp. }
  eapply alpha_eq_trans in aeqs3;[|exact aeqs1]; eauto with slow.
Qed.

Lemma alpha_eq_subst_utokens_same {o} :
  forall (t1 t2 : @NTerm o) (s : utok_sub),
    alpha_eq t1 t2
    -> alpha_eq (subst_utokens t1 s) (subst_utokens t2 s).
Proof.
  introv aeq.
  apply alpha_eq_subst_utokens; eauto with slow.
Qed.
