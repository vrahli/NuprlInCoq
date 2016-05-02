(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export computation8.
Require Export list_tacs.
Require Export alphaeq2.
Require Export substitution2.
Require Export terms4.
Require Export computation10.
Require Export nat_defs.




Definition uexc {o} (a : get_patom_set o) :=
  mk_exception (mk_utoken a) mk_axiom.

Lemma isnexc_uexc {o} :
  forall lib (a : get_patom_set o),
    isnexc lib a (uexc a).
Proof.
  introv; simpl; eauto with slow.
Qed.
Hint Resolve isnexc_uexc : slow.

Definition get_ints_can {o} (c : @CanonicalOp o) : list Z :=
  match c with
    | Nint z => [z]
    | _ => []
  end.

Definition get_ints_op {o} (op : @Opid o) : list Z :=
  match op with
    | Can c => get_ints_can c
    | _ => []
  end.

Fixpoint get_ints {o} (t : @NTerm o) : list Z :=
  match t with
    | vterm _ => []
    | sterm _ => []
    | oterm op bs => get_ints_op op ++ flat_map get_ints_b bs
  end
with get_ints_b {o} (b : @BTerm o) : list Z :=
       match  b with
         | bterm vs t => get_ints t
       end.

(*
   t + 0
 *)
Definition force_int {o} (t : @NTerm o) : NTerm := mk_add t mk_zero.

(*
   if |t| < b then t else e
 *)
Definition less_bound {o} (b : nat) (t e : @NTerm o) :=
  mk_less (absolute_value t) (mk_nat b) t e.

(*
   let v := t
   in if |v| < b then v else e
 *)
Definition force_int_bound {o} (v : NVar) (b : nat) (t e : @NTerm o) : NTerm :=
  mk_cbv t v (less_bound b (mk_var v) e).



Definition force_int_f {o} v (f : @NTerm o) :=
  mk_lam v (mk_cbv
              (force_int (mk_var v))
              v
              (mk_apply f (mk_var v))).

Definition force_int_F {o} v (F f : @NTerm o) :=
  mk_apply F (force_int_f v f).

Definition force_int_bound_f {o} v b (f : @NTerm o) e :=
  mk_lam v (mk_cbv
              (force_int_bound v b (mk_var v) e)
              v
              (mk_apply f (mk_var v))).

Definition force_int_bound_F {o} v b (F f : @NTerm o) e :=
  mk_apply F (force_int_bound_f v b f e).

Definition agree_upto_red_b {o} lib b (f g : @NTerm o) :=
  forall t1 t2 (i : Z),
    reduces_to lib t1 (mk_integer i)
    -> reduces_to lib t2 (mk_integer i)
    -> Z.abs_nat i < b
    -> {z : Z
        & reduces_to lib (mk_apply f t1) (mk_integer z)
        # reduces_to lib (mk_apply g t2) (mk_integer z)}.

Definition agree_upto_b {o} lib b (f g : @NTerm o) :=
  forall (i : Z),
    Z.abs_nat i < b
    -> {z : Z
        & reduces_to lib (mk_apply f (mk_integer i)) (mk_integer z)
        # reduces_to lib (mk_apply g (mk_integer i)) (mk_integer z)}.

Lemma agree_upto_red_implies {o} :
  forall lib b (f g : @NTerm o),
    agree_upto_red_b lib b f g
    -> agree_upto_b lib b f g.
Proof.
  introv agree.

  unfold agree_upto_b; introv l.
  unfold agree_upto_red_b in agree.

  pose proof (agree (mk_integer i) (mk_integer i) i) as h.
  repeat (autodimp h hyp); eauto with slow.
Qed.

Lemma agree_upto_red_if {o} :
  forall lib b (f g : @NTerm o),
    agree_upto_b lib b f g
    -> agree_upto_red_b lib b f g.
Proof.
  introv agree.

  unfold agree_upto_red_b; introv r1 r2 l.
  unfold agree_upto_b in agree.

  pose proof (agree i) as h; autodimp h hyp.
  exrepnd.
  exists z; dands.
Abort.

Definition reduces_to_int {o} lib (t : @NTerm o) :=
  {z : Z & reduces_to lib t (mk_integer z)}.

(*

  let v := (let v := arg in if |v| < b then v else e) in f(v)

 *)
Definition force_int_bound_app {o} (v : NVar) (b : nat) (arg f e : @NTerm o) : NTerm :=
  mk_cbv (force_int_bound v b arg e) v (mk_apply f (mk_var v)).

Lemma alpha_eq_force_int {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (force_int t1) (force_int t2).
Proof.
  introv aeq.
  unfold force_int, mk_add.
  prove_alpha_eq4.
  introv i.
  destruct n;[|destruct n]; try omega.
  - apply alphaeqbt_nilv2; auto.
  - apply alphaeqbt_nilv2; auto.
Qed.

Definition br_list {T} R (l1 l2 : list T) :=
  length l1 = length l2
  # (forall a1 a2,
       LIn (a1,a2) (combine l1 l2)
       -> R a1 a2).

Definition br_bterms {o} R (bs1 bs2 : list (@BTerm o)) := br_list R bs1 bs2.

Lemma br_bterms_nil {o} :
  forall (R : @BTerm o -> @BTerm o -> Type),
    br_bterms R [] [].
Proof.
  introv.
  unfold br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve br_bterms_nil : slow.

Lemma br_bterms_cons {o} :
  forall R (b1 b2 : @BTerm o) bs1 bs2,
    R b1 b2
    -> br_bterms R bs1 bs2
    -> br_bterms R (b1 :: bs1) (b2 :: bs2).
Proof.
  introv h1 h2.
  allunfold @br_bterms.
  allunfold @br_list; simpl; tcsp.
  dands; tcsp.
  introv i; dorn i; cpx; tcsp.
Qed.
Hint Resolve br_bterms_cons : slow.

Lemma alpha_eq_bterms_implies_same_length {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    alpha_eq_bterms bs1 bs2 -> length bs1 = length bs2.
Proof.
  introv aeq.
  unfold alpha_eq_bterms, br_bterms, br_list in aeq; sp.
Qed.
Hint Resolve alpha_eq_bterms_implies_same_length : slow.

Lemma alpha_eq_force_int_bound {o} :
  forall b v1 v2 (t1 t2 e1 e2 : @NTerm o),
    !LIn v1 (free_vars e1)
    -> !LIn v2 (free_vars e2)
    -> alpha_eq t1 t2
    -> alpha_eq e1 e2
    -> alpha_eq
         (force_int_bound v1 b t1 e1)
         (force_int_bound v2 b t2 e2).
Proof.
  introv ni1 ni2 aeq1 aeq2.
  unfold force_int_bound, mk_cbv, mk_less.
  prove_alpha_eq4.
  introv i.
  destruct n;[|destruct n]; try omega.

  - apply alphaeqbt_nilv2; auto.

  - pose proof (ex_fresh_var
                  ([v1,v2]
                     ++ all_vars (less_bound b (vterm v1) e1)
                     ++ all_vars (less_bound b (vterm v2) e2)
               )) as h; exrepnd.
    allunfold @all_vars; allsimpl.
    allsimpl; allrw app_nil_r; allrw remove_nvars_nil_l.
    allrw in_app_iff; allsimpl; allrw in_app_iff.
    allrw not_over_or; repnd; GC.

    apply (al_bterm _ _ [v]); simpl; auto.

    + unfold all_vars; simpl.
      allrw remove_nvars_nil_l; allrw app_nil_r.
      rw disjoint_singleton_l; simpl.
      allrw in_app_iff; simpl; allrw in_app_iff; sp.

    + unfold lsubst; simpl; boolvar; allrw app_nil_r;
      allrw disjoint_singleton_r; tcsp.
      prove_alpha_eq4.
      introv j.
      destruct n;[|destruct n;[|destruct n;[|destruct n]]];
      try omega; eauto 3 with slow.

      apply alphaeqbt_nilv2; auto.
      repeat (rw @lsubst_aux_trivial_cl_term); auto; simpl;
      allrw disjoint_singleton_r; auto.
Qed.

Lemma alpha_bterm_change_aux {o} :
  forall (bt : @BTerm o) lv nt lvn,
  alpha_eq_bterm bt (bterm lv nt)
  -> disjoint (all_vars nt) lvn
  -> no_repeats lvn
  -> length lv = length lvn
  -> alpha_eq_bterm bt (bterm lvn (lsubst_aux nt (var_ren lv lvn))).
Proof.
  introv aeq disj norep len.
  pose proof (alpha_bterm_change
                bt lv nt lvn
                aeq disj norep len) as h.
  unfold lsubst in h; simpl h; boolvar; auto.
  provefalse; destruct n.
  rw @range_var_ren; auto.
  rw flat_map_map.
  unfold compose.
  rw disjoint_flat_map_r; introv i; simpl.
  rw disjoint_singleton_r; intro k.
  apply disjoint_sym in disj; apply disj in i.
  rw in_app_iff in i; rw not_over_or in i; sp.
Qed.

Lemma implies_eqvars_flat_map_diff :
  forall (A : tuniv) (f g : A -> list NVar) (l k : list A),
    length l = length k
    -> (forall x y : A, LIn (x,y) (combine l k) -> eqvars (f x) (g y))
    -> eqvars (flat_map f l) (flat_map g k).
Proof.
  induction l; destruct k; introv len imp; allsimpl; cpx.
  apply eqvars_app; auto.
Qed.

Lemma fresh_var_lt :
  forall vs v,
    (forall x, LIn (nvar x) vs -> v < x)
    -> fresh_var_aux v vs = v.
Proof.
  induction vs; introv i; allsimpl; tcsp.
  destruct a.
  boolvar; auto; subst.
  pose proof (i n) as h; autodimp h hyp; sp.
Qed.

Lemma le_var_implies_eq :
  forall a b, le_var a b -> le_var b a -> a = b.
Proof.
  introv k1 k2.
  destruct a, b.
  allunfold le_var.
  f_equal; omega.
Qed.

Inductive sublist {T} : list T -> list T -> Type :=
| sublist_nil : sublist [] []
| sublist_cons :
    forall t l1 l2,
      sublist l1 l2
      -> sublist (t :: l1) (t :: l2)
| sublist_tl :
    forall t l1 l2,
      sublist l1 l2
      -> sublist l1 (t :: l2).
Hint Constructors sublist.

Lemma sublist_refl :
  forall T (l : list T),
    sublist l l.
Proof.
  induction l; auto.
Qed.

Lemma list_ind_sublist :
  forall (A : Type) (P : list A -> Type),
    P []
    -> (forall (l : list A),
          (forall (k : list A),
             length k < length l
             -> sublist k l
             -> P k)
          -> P l)
    -> forall l : list A, P l.
Proof.
  introv nc sc; introv.
  assert ({n | length l = n}) as e by (exists (length l); auto); sp.
  revert l e.
  induction n as [n Hind] using comp_ind_type; introv len; cpx.
  destruct n; cpx.
  destruct l; allsimpl; cpx.
  apply (sc (a :: l)); allsimpl; tcsp.
  introv i s.
  apply (Hind (length k)); auto.
Qed.

Tactic Notation "sublist_ind" ident(h) ident(c) :=
  induction h using list_ind_sublist;
  [ Case_aux c "nil"
  | Case_aux c "cons"
  ].

Tactic Notation "sublist_ind" ident(h) "as" simple_intropattern(I) ident(c) :=
  induction h as I using list_ind_sublist;
  [ Case_aux c "nil"
  | Case_aux c "cons"
  ].

Lemma issorted_eqvars :
  forall l1 l2 x,
    issorted (x :: l1)
    -> issorted l2
    -> eqvars (x :: l1) l2
    -> {l1h : list NVar
        & {l1t : list NVar
        & {l2h : list NVar
        & {l2t : list NVar
        & l1 = l1h ++ l1t
        # l2 = l2h ++ l2t
        # (forall t, LIn t l1h -> t = x)
        # (forall t, LIn t l2h -> t = x)
        # !LIn x l1t
        # !LIn x l2t
        # eqvars l1t l2t}}}}.
Proof.
  sublist_ind l1 as [|l1 ind] Case; destruct l2; introv iss1 iss2 eqv; allsimpl.

  - apply eqvars_sym in eqv.
    apply eqvars_nil in eqv; cpx.

  - exists ([] : list NVar) ([] : list NVar) (n :: l2) ([] : list NVar); simpl.
    allrw app_nil_r; dands; tcsp.
    rw eqvars_prop in eqv.
    introv i; dorn i; subst; auto.

    + pose proof (eqv t) as h; destruct h as [h1 h]; clear h1.
      simpl in h; sp.

    + pose proof (eqv t) as h; destruct h as [h1 h]; clear h1.
      simpl in h; sp.

  - apply eqvars_sym in eqv.
    apply eqvars_nil in eqv; cpx.

  - inversion iss1 as [|? ? h1 h2]; subst.
    assert (x = n) as e.

    + rw eqvars_prop in eqv.

      pose proof (eqv x) as k1.
      destruct k1 as [k1 k]; clear k.
      simpl in k1; autodimp k1 hyp.

      pose proof (eqv n) as k2.
      destruct k2 as [k k2]; clear k.
      simpl in k2; autodimp k2 hyp.

      dorn k2; auto.
      pose proof (h1 n) as h; simpl in h; autodimp h hyp.
      dorn k1; auto.
      inversion iss2 as [|? ? p1 p2]; subst.
      apply p1 in k1.
      apply le_var_implies_eq; auto.

    + subst.
      pose proof (eqvars_remove_nvar (n :: l1) (n :: l2) n eqv) as h.
      allrw (remove_nvar_cons n n); boolvar.
      inversion iss2 as [|? ? k1 k2]; subst.
Abort.

Definition remove_repeated_vars := remove_repeats deq_nvar.
Hint Unfold remove_repeated_vars.

Lemma fresh_var_aux_eq_S :
  forall vs n,
    issorted vs
    -> LIn (nvar n) vs
    -> fresh_var_aux (S n) vs = fresh_var_aux n vs.
Proof.
  induction vs; introv iss i; allsimpl; tcsp.
  destruct a.
  inversion iss as [|? ? imp iss1]; subst; clear iss.
  boolvar; tcsp; try omega.
  - provefalse.
    dorn i; ginv; try omega.
    discover.
    allunfold le_var; allsimpl; omega.
  - subst.
    provefalse.
    dorn i; ginv.
    + inversion i; omega.
    + discover.
      allunfold le_var; omega.
  - dorn i; ginv; auto; omega.
Qed.

Lemma eq_fresh_var_aux_remove_repeated :
  forall vs n,
    issorted vs
    -> fresh_var_aux n vs = fresh_var_aux n (remove_repeated_vars vs).
Proof.
  induction vs; introv iss; simpl; auto.
  destruct a.
  inversion iss as [|? ? imp iss1]; subst; clear iss.
  allunfold remove_repeated_vars; simpl.
  boolvar; auto; simpl; boolvar; tcsp; subst.

  - rw fresh_var_lt; auto.
    introv i.
    allrw in_remove_repeats.
    discover.
    allunfold le_var; omega.

  - rw <- IHvs; auto.
    apply fresh_var_aux_eq_S; auto.
Qed.

Lemma issorted_remove_repeated_vars :
  forall l, issorted l -> issorted (remove_repeated_vars l).
Proof.
  induction l; introv iss; allunfold remove_repeated_vars; allsimpl; auto.
  inversion iss as [|? ? imp iss1]; subst; clear iss.
  boolvar; auto.
  constructor; auto.
  introv i.
  allrw in_remove_repeats.
  discover; auto.
Qed.

Lemma eqvars_remove_repeated_vars :
  forall l1 l2,
    eqvars l1 l2
    -> eqvars (remove_repeated_vars l1) l2.
Proof.
  introv eqv.
  allrw eqvars_prop.
  introv.
  unfold remove_repeated_vars.
  rw in_remove_repeats; auto.
Qed.

Lemma no_repeats_remove_repeated_vars :
  forall vs, no_repeats (remove_repeated_vars vs).
Proof.
  introv; apply no_repeats_remove_repeats.
Qed.

Lemma if_eqvars_cons :
  forall v vs1 vs2,
    !LIn v vs1
    -> !LIn v vs2
    -> eqvars (v :: vs1) (v :: vs2)
    -> eqvars vs1 vs2.
Proof.
  introv ni1 ni2 eqv.
  allrw eqvars_prop.
  introv.
  pose proof (eqv x) as h; destruct h as [h1 h2]; allsimpl.
  split; introv i.
  - autodimp h1 hyp; dorn h1; subst; tcsp.
  - autodimp h2 hyp; dorn h2; subst; tcsp.
Qed.

Lemma eq_vars_if_issorted_no_repeats_and_eqvars :
  forall vs1 vs2,
    issorted vs1
    -> issorted vs2
    -> eqvars vs1 vs2
    -> no_repeats vs1
    -> no_repeats vs2
    -> vs1 = vs2.
Proof.
  induction vs1; introv iss1 iss2 eqv norep1 norep2; allsimpl; tcsp.
  - apply eqvars_nil in eqv; subst; auto.
  - inversion norep1 as [|? ? ni1 nr1]; subst; clear norep1.
    inversion iss1 as [|? ? imp1 is1]; subst; clear iss1.
    destruct vs2.
    + apply eqvars_sym in eqv; apply eqvars_nil in eqv; sp.
    + inversion norep2 as [|? ? ni2 nr2]; subst; clear norep2.
      inversion iss2 as [|? ? imp2 is2]; subst; clear iss2.

      dup eqv as i.
      rw eqvars_prop in i.

      pose proof (i a) as h1; destruct h1 as [h1 h]; clear h.
      simpl in h1; autodimp h1 hyp.

      pose proof (i n) as h2; destruct h2 as [h h2]; clear h.
      simpl in h2; autodimp h2 hyp.

      dorn h1; subst;[|dorn h2; subst].

      * clear h2.
        apply if_eqvars_cons in eqv; auto.
        f_equal.
        apply IHvs1; auto.

      * apply if_eqvars_cons in eqv; auto.
        f_equal.
        apply IHvs1; auto.

      * discover.
        assert (a = n) as e.
        { destruct a, n; allunfold le_var; allsimpl; f_equal; omega. }

        subst.
        apply if_eqvars_cons in eqv; auto.
        f_equal.
        apply IHvs1; auto.
Qed.

Lemma eq_fresh_var :
  forall vs1 vs2,
    eqvars vs1 vs2
    -> fresh_var vs1 = fresh_var vs2.
Proof.
  introv eqv.
  unfold fresh_var.
  remember 0 as n; clear Heqn.
  f_equal.
  remember (sort vs1) as l1.
  remember (sort vs2) as l2.
  pose proof (sort_eqvars vs1) as e1.
  rw <- Heql1 in e1.
  pose proof (sort_eqvars vs2) as e2.
  rw <- Heql2 in e2.
  pose proof (sort_issorted vs1) as i1.
  rw <- Heql1 in i1.
  pose proof (sort_issorted vs2) as i2.
  rw <- Heql2 in i2.
  assert (eqvars l1 l2) as ev.
  eapply eqvars_trans;[|exact e2].
  eapply eqvars_trans;[|exact eqv].
  apply eqvars_sym; auto.
  clear dependent vs1.
  clear dependent vs2.

  rw (eq_fresh_var_aux_remove_repeated l1); auto.
  rw (eq_fresh_var_aux_remove_repeated l2); auto.
  apply issorted_remove_repeated_vars in i1.
  apply issorted_remove_repeated_vars in i2.
  apply eqvars_remove_repeated_vars in ev.
  apply eqvars_sym in ev.
  apply eqvars_remove_repeated_vars in ev.
  apply eqvars_sym in ev.
  pose proof (no_repeats_remove_repeated_vars l1) as nr1.
  pose proof (no_repeats_remove_repeated_vars l2) as nr2.
  remember (remove_repeated_vars l1) as vs1.
  remember (remove_repeated_vars l2) as vs2.
  clear dependent l1.
  clear dependent l2.

  apply eq_vars_if_issorted_no_repeats_and_eqvars in ev; auto.
  rw ev; auto.
Qed.


Lemma fresh_distinct_vars_if_eqvars :
  forall n vs1 vs2,
    eqvars vs1 vs2
    -> fresh_distinct_vars n vs1 = fresh_distinct_vars n vs2.
Proof.
  induction n; introv eqv; simpl; auto.
  rw (eq_fresh_var vs1 vs2); auto.
  f_equal; auto.
  apply IHn.
  apply eqvars_cons_lr; auto.
Qed.

Lemma br_bterms_cons_iff {o} :
  forall R (b1 b2 : @BTerm o) bs1 bs2,
    br_bterms R (b1 :: bs1) (b2 :: bs2)
    <=> (R b1 b2 # br_bterms R bs1 bs2).
Proof.
  introv.
  allunfold @br_bterms.
  allunfold @br_list.
  split; intro k; repnd; dands; allsimpl; cpx.
  introv i; dorn i; cpx; tcsp.
Qed.

Lemma matching_bterms_implies_eq_length {o} :
  forall vars (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> length vars = length bs.
Proof.
  introv m.
  unfold matching_bterms in m.
  rw <- (map_length (fun v : NVar # nat => snd v)).
  rw <- (map_length num_bvars bs).
  rw m; auto.
Qed.

Lemma all_fo_vars_eqvars {o} :
  forall (t : @SOTerm o),
    eqvars
      (all_fo_vars t)
      (fo_bound_vars t ++ sovars2vars (so_free_vars t)).
Proof.
  soterm_ind t as [v ts ind| |op bs ind] Case; simpl; auto.

  - Case "sovar".
    eapply eqvars_trans;[|apply eqvars_move_around].
    apply eqvars_cons_lr.
    rw eqvars_prop; introv; split; intro k; allrw in_app_iff; allrw lin_flat_map; exrepnd.
    + applydup ind in k1; allrw eqvars_prop.
      apply k2 in k0; allrw in_app_iff.
      dorn k0.
      * left.
        exists x0; sp.
      * right.
        rw sovars2vars_flat_map.
        rw lin_flat_map.
        exists x0; sp.
    + dorn k; exrepnd.
      * applydup ind in k1.
        exists x0; dands; auto.
        rw eqvars_prop in k2.
        apply k2; rw in_app_iff; tcsp.
      * rw sovars2vars_flat_map in k.
        rw lin_flat_map in k; exrepnd.
        exists x0; dands; auto.
        applydup ind in k1.
        rw eqvars_prop in k2.
        apply k2; rw in_app_iff; tcsp.

  - Case "soterm".
    induction bs; simpl; auto.
    autodimp IHbs hyp.
    { introv i; eapply ind; simpl; eauto. }
    rw sovars2vars_app.
    destruct a as [l t].
    pose proof (ind t l) as h; simpl in h; autodimp h hyp; clear ind.
    allrw eqvars_prop; introv; simpl.
    allrw in_app_iff.
    rw h; clear h.
    rw IHbs; clear IHbs.
    allrw in_app_iff.
    split; intro k; repnd.
    + dorn k;[dorn k|dorn k]; tcsp.
      dorn k; tcsp.
      destruct (in_deq NVar deq_nvar x l); tcsp.
      right; left.
      allrw in_sovars2vars; exrepnd.
      exists n0.
      rw in_remove_so_vars; dands; auto.
      intro k.
      rw in_vars2sovars in k; repnd; subst; sp.
    + dorn k;[dorn k;[dorn k|]|]; tcsp.
      dorn k; tcsp.
      left; right; right.
      allrw in_sovars2vars; exrepnd.
      allrw in_remove_so_vars; repnd.
      exists n; sp.
Qed.

Lemma eqvars_app_r_implies_subvars :
  forall vs1 vs2 vs3,
    eqvars vs1 (vs2 ++ vs3)
    -> (subvars vs2 vs1 # subvars vs3 vs1).
Proof.
  introv e; allrw eqvars_prop; allrw subvars_prop; dands; introv i; apply e;
  rw in_app_iff; sp.
Qed.

Lemma compute_step_lib_if_found_entry {o} :
  forall (lib : library)
         (oa1 oa2 : opabs)
         (bs : list BTerm)
         (vars : list sovar_sig)
         (rhs : @SOTerm o)
         (correct : correct_abs oa2 vars rhs),
    found_entry lib oa1 bs oa2 vars rhs correct
    -> compute_step_lib lib oa1 bs = csuccess (mk_instance vars bs rhs).
Proof.
  introv fe.
  eapply compute_step_lib_success_change_bs; eauto.
Qed.

Lemma can_doesnt_reduce_to_exc {o} :
  forall lib can (l1 l2 : list (@BTerm o)),
    reduces_to lib (oterm (Can can) l1) (oterm Exc l2)
    -> False.
Proof.
  introv r.
  unfold reduces_to in r; exrepnd.
  revert dependent l2.
  revert dependent l1.
  induction k; introv r.
  - rw @reduces_in_atmost_k_steps_0 in r; ginv.
  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; simpl in r1; ginv.
    apply IHk in r0; sp.
Qed.

Definition converges_to_can_or_exc {o} lib (t : @NTerm o) :=
  {u : NTerm & reduces_to lib t u # is_can_or_exc u}.

Lemma converges_to_value_like_narithop1 {o} :
  forall (lib : @library o) a bs,
    converges_to_value_like
      lib
      (oterm (NCan (NArithOp a)) bs)
    -> {t1 : NTerm
        & {t2 : NTerm
        & {z1 : Z
        & {z2 : Z
        & bs = [nobnd t1, nobnd t2]
        # reduces_to lib t1 (mk_integer z1)
        # reduces_to lib t2 (mk_integer z2)
       }}}}
       [+]
       {t : NTerm
        & {e : NTerm
        & {l : list BTerm
        & bs = nobnd t :: l
        # reduces_to lib t e
        # isexc e
       }}}
       [+]
       {t1 : NTerm
        & {t2 : NTerm
        & {z : Z
        & {e : NTerm
        & {l : list BTerm
        & bs = nobnd t1 :: nobnd t2 :: l
        # reduces_to lib t1 (mk_integer z)
        # reduces_to lib t2 e
        # isexc e
       }}}}}.
Proof.
  introv conv.
  unfold converges_to_value_like, reduces_to in conv; exrepnd.
  revert dependent u.
  revert dependent bs.
  induction k; introv comp isv.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    provefalse; unfold isvalue_like in isv; sp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct bs; ginv.
    destruct b; ginv.
    destruct l; ginv.
    destruct n; ginv.
    dopid o0 as [can2|ncan2|exc2|abs2] Case; ginv.

    + Case "Can".
      destruct bs; ginv; try (complete (csunf comp1; allsimpl; dcwf h));[].
      destruct b.
      destruct l0; destruct n; try (complete (csunf comp1; allsimpl; dcwf h));[].
      dopid o0 as [can3|ncan3|exc3|abs3] SCase; ginv.

      * SCase "Can".
        allsimpl.
        destruct l; try (complete (csunf comp1; allsimpl; dcwf h));[].
        destruct l0; try (complete (csunf comp1; allsimpl; dcwf h));[].
        destruct bs; try (complete (csunf comp1; allsimpl; dcwf h));[].
        csunf comp1; allsimpl.
        dcwf h.
        apply compute_step_arithop_success_can_can in comp1; repnd; GC; exrepnd.
        allrw @get_param_from_cop_some; allsimpl; subst.

        left.

        exists (@mk_integer o n1) (@mk_integer o n2) n1 n2; dands; tcsp;
        apply computes_to_value_isvalue_refl;
        repeat constructor; simpl; sp.

      * SCase "NCan".
        rw @compute_step_narithop_ncan2 in comp1.
        dcwf h.
        remember (compute_step lib (oterm (NCan ncan3) l0)) as c;
          symmetry in Heqc; destruct c; ginv.
        apply IHk in comp0; auto; exrepnd; cpx; GC;[].
        repndors; exrepnd; cpx; GC.

        { left.
          exists (oterm (Can can2) l) (oterm (NCan ncan3) l0) z1 z2; dands; tcsp.
          eapply reduces_to_if_split2; eauto. }

        { provefalse.
          allapply @isexc_implies2; exrepnd; subst.
          apply can_doesnt_reduce_to_exc in comp2; sp. }

        { right; right.
          allunfold @ca_wf_def; exrepnd; subst.
          exists (@mk_integer o i)
                 (oterm (NCan ncan3) l0)
                 i e l1;
            dands; tcsp; eauto with slow.
          eapply reduces_to_if_split2; eauto. }

      * SCase "Exc".
        csunf comp1; allsimpl; dcwf h; ginv.
        allunfold @ca_wf_def; exrepnd; subst.
        right; right.
        exists (@mk_integer o i)
               (oterm Exc l0)
               i
               (oterm Exc l0) bs; dands; tcsp; eauto with slow.

      * SCase "Abs".
        rw @compute_step_narithop_abs2 in comp1.
        dcwf h;[].
        remember (compute_step_lib lib abs3 l0) as c.
        symmetry in Heqc; destruct c; ginv.
        apply IHk in comp0; auto; exrepnd; cpx; GC.
        repndors; exrepnd; cpx; GC.

        { left.
          exists (oterm (Can can2) l) (oterm (Abs abs3) l0) z1 z2; dands; tcsp.
          eapply reduces_to_if_split2; eauto. }

        { provefalse.
          allapply @isexc_implies2; exrepnd; subst.
          apply can_doesnt_reduce_to_exc in comp2; sp. }

        { right; right.
          allunfold @ca_wf_def; exrepnd; subst.
          exists (@mk_integer o i)
                 (oterm (Abs abs3) l0)
                 i e l1; dands; tcsp; eauto with slow.
          eapply reduces_to_if_split2; eauto. }

    + Case "NCan".
      rw @compute_step_narithop_ncan1 in comp1.
      remember (compute_step lib (oterm (NCan ncan2) l)) as c;
        symmetry in Heqc; destruct c; ginv.
      apply IHk in comp0; auto; exrepnd; cpx; GC.
      dorn comp0;[|dorn comp0]; exrepnd; cpx; GC.

      { left.
        exists (oterm (NCan ncan2) l) t2 z1 z2; dands; tcsp.
        eapply reduces_to_if_split2; eauto. }

      { right; left.
        exists (oterm (NCan ncan2) l) e l0; dands; tcsp.
        eapply reduces_to_if_split2; eauto. }

      { right; right.
        exists (oterm (NCan ncan2) l)
               t2
               z e l0; dands; tcsp; eauto with slow.
        eapply reduces_to_if_split2; eauto. }

    + Case "Exc".
      simpl in comp1.
      unfold compute_step_catch in comp1; ginv.
      right; left.
      exists (oterm Exc l) (oterm Exc l) bs; dands; tcsp; eauto with slow.

    + Case "Abs".
      rw @compute_step_narithop_abs1 in comp1.
      remember (compute_step_lib lib abs2 l) as c.
      symmetry in Heqc; destruct c; ginv.
      apply IHk in comp0; auto; exrepnd; cpx; GC.
      dorn comp0;[|dorn comp0]; exrepnd; cpx; GC.

      { left.
        exists (oterm (Abs abs2) l) t2 z1 z2; dands; tcsp.
        eapply reduces_to_if_split2; eauto. }

      { right; left.
        exists (oterm (Abs abs2) l) e l0; dands; tcsp.
        eapply reduces_to_if_split2; eauto. }

      { right; right.
        exists (oterm (Abs abs2) l)
               t2 z e l0; dands; tcsp; eauto with slow.
        eapply reduces_to_if_split2; eauto. }
Qed.

Lemma converges_to_can_or_exc_implies_converges_to_value_like {o} :
  forall lib (t : @NTerm o),
    converges_to_can_or_exc lib t
    -> converges_to_value_like lib t.
Proof.
  introv c.
  unfold converges_to_can_or_exc in c.
  unfold converges_to_value_like.
  exrepnd; exists u; dands; eauto with slow.
Qed.
Hint Resolve converges_to_can_or_exc_implies_converges_to_value_like : slow.

Lemma abs_of_neg :
  forall z b,
    (z < 0)%Z
    -> (- z < Z.of_nat b)%Z
    -> Z.abs_nat z < b.
Proof.
  introv h1 h2.
  pose proof (Zabs.Zabs_nat_lt (-z) (Z.of_nat b)) as k.
  autodimp k hyp; try omega.
  allrw Znat.Zabs2Nat.id.
  destruct z; allsimpl; try omega.
Qed.

Lemma abs_of_pos :
  forall z b,
    (0 <= z)%Z
    -> (z < Z.of_nat b)%Z
    -> Z.abs_nat z < b.
Proof.
  introv h1 h2.
  pose proof (Zabs.Zabs_nat_lt z (Z.of_nat b)) as k.
  autodimp k hyp; try omega.
  allrw Znat.Zabs2Nat.id.
  destruct z; allsimpl; try omega.
Qed.

Lemma reduces_to_int_subst_less_bound {o} :
  forall lib b v a can z (bs : list (@BTerm o)),
    reduces_to
      lib
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
      (mk_integer z)
    -> can = Nint z # bs = [] # Z.abs_nat z < b.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.

  apply reduces_to_split2 in r; dorn r; allsimpl; exrepnd; ginv.
  csunf r1; allsimpl.
  unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r0; dorn r0; allsimpl; exrepnd; ginv.
  csunf r0; allsimpl.
  boolvar; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; ginv.
    exrepnd; allsimpl.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      inversion r0; subst; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      inversion r0.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r0; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      inversion r1; subst; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      inversion r1.
Qed.

Lemma abs_of_neg2 :
  forall z b,
    (z < 0)%Z
    -> Z.abs_nat z < b
    -> (- z < Z.of_nat b)%Z.
Proof.
  introv h1 h2.
  destruct (Z_lt_le_dec (- z) (Z.of_nat b)) as [h|h]; auto.
  provefalse.
  pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as k.
  autodimp k hyp; try omega.
  allrw Znat.Zabs2Nat.id.
  destruct z; allsimpl; try omega.
Qed.

Lemma abs_of_pos2 :
  forall z b,
    (0 <= z)%Z
    -> Z.abs_nat z < b
    -> (z < Z.of_nat b)%Z.
Proof.
  introv h1 h2.
  destruct (Z_lt_le_dec z (Z.of_nat b)) as [h|h]; auto.
  provefalse.
  pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as k.
  autodimp k hyp; try omega.
  allrw Znat.Zabs2Nat.id.
  destruct z; allsimpl; try omega.
Qed.

Definition has_value_like_except {p} lib a (t : @NTerm p) :=
  {u : NTerm
   & reduces_to lib t u
   # isvalue_like u
   # !isnexc lib a u}.

Lemma has_value_like_except_subst_less_bound {o} :
  forall lib b v a can (bs : list (@BTerm o)),
    has_value_like_except
      lib a
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
    -> {z : Z & can = Nint z # bs = [] # Z.abs_nat z < b}.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.
  unfold has_value_like_except in r; exrepnd.

  apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

  { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

  csunf r1; allsimpl.
  unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r3; dorn r3; allsimpl; exrepnd; subst.

  { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

  csunf r3; allsimpl; boolvar; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r2; exrepnd; repndors; inversion r2. }

    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
      exists z; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
      destruct r0; simpl; exists (mk_utoken a); simpl; boolvar; dands; tcsp; eauto with slow.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r3; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
      exists z; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
      destruct r0; simpl; exists (mk_utoken a); simpl; boolvar; dands; tcsp; eauto with slow.
Qed.

Lemma hasvalue_like_subst_less_bound {o} :
  forall lib b v can (bs : list (@BTerm o)),
    hasvalue_like
      lib
      (subst (less_bound b (mk_var v) (mk_vbot v)) v (oterm (Can can) bs))
    -> {z : Z & can = Nint z # bs = [] # Z.abs_nat z < b}.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; repndors; csunf r2; allsimpl; exrepnd; subst; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst; csunf r2; allsimpl; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }
Qed.

Lemma compose_reduces_to_step_primarg_ncompop {o} :
  forall lib c can bs (t1 t2 u : @NTerm o) l,
    reduces_to
      lib
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs) :: bterm [] t1 :: l)) u
    -> compute_step lib t1 = csuccess t2
    -> isvalue_like u
    -> reduces_to
         lib
         (oterm (NCan (NCompOp c))
                (bterm [] (oterm (Can can) bs) :: bterm [] t2 :: l)) u.
Proof.
  introv r comp isv.
  apply reduces_to_split2 in r; dorn r.
  - subst; allunfold @isvalue_like; allsimpl; sp.
  - exrepnd.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    destruct t1 as [v1|f1|op1 bs1]; ginv.
    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf comp; allsimpl; ginv.
      apply compute_step_compop_success_can_can in r1; exrepnd; subst.
      repndors; exrepnd; subst;
      allrw @get_param_from_cop_some; subst.
      * apply (reduces_to_if_split2
                 _ _ (if Z_lt_le_dec n1 n2 then t1 else t2)); auto.
      * apply (reduces_to_if_split2
                 _ _ (if param_kind_deq pk1 pk2 then t1 else t2)); auto.
        csunf; simpl; dcwf h;
        unfold compute_step_comp; simpl; allrw @get_param_from_cop_pk2can; auto.

    + Case "NCan".
      unfold on_success in r1.
      rw comp in r1; ginv; auto.

    + Case "Exc".
      csunf comp; allsimpl.
      ginv; allsimpl; ginv.
      apply (reduces_to_if_split2 _ _ (oterm Exc bs1)); auto.
      csunf; simpl; dcwf h; auto.

    + Case "Abs".
      unfold on_success in r1.
      rw comp in r1; ginv; auto.
Qed.

Lemma compose_reduces_to_step_primarg_arithop {o} :
  forall lib c can bs (t1 t2 u : @NTerm o) l,
    reduces_to
      lib
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs) :: bterm [] t1 :: l)) u
    -> compute_step lib t1 = csuccess t2
    -> isvalue_like u
    -> reduces_to
         lib
         (oterm (NCan (NArithOp c))
                (bterm [] (oterm (Can can) bs) :: bterm [] t2 :: l)) u.
Proof.
  introv r comp isv.
  apply reduces_to_split2 in r; dorn r.
  - subst; allunfold @isvalue_like; allsimpl; sp.
  - exrepnd.
    csunf r1; allsimpl.
    dcwf h.
    destruct t1 as [v1|f1|op1 bs1]; ginv.
    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf comp; allsimpl.
      allsimpl; ginv.
      apply compute_step_arithop_success_can_can in r1; exrepnd; subst.
      allapply @get_param_from_cop_pki; subst.
      apply (reduces_to_if_split2
               _ _ (oterm (Can (Nint (get_arith_op c n1 n2))) [])); auto.

    + Case "NCan".
      unfold on_success in r1.
      rw comp in r1; ginv; auto.

    + Case "Exc".
      csunf comp; allsimpl.
      ginv; allsimpl; ginv.
      apply (reduces_to_if_split2
               _ _ (oterm Exc bs1)); auto.
      csunf; simpl; dcwf h; auto.

    + Case "Abs".
      unfold on_success in r1.
      rw comp in r1; ginv; auto.
Qed.

Lemma compose_reduces_to_primarg_ncompop {o} :
  forall lib c can bs (t1 t2 u : @NTerm o) l,
    reduces_to
      lib
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs) :: bterm [] t1 :: l)) u
    -> reduces_to lib t1 t2
    -> isvalue_like u
    -> reduces_to
         lib
         (oterm (NCan (NCompOp c))
                (bterm [] (oterm (Can can) bs) :: bterm [] t2 :: l)) u.
Proof.
  introv r1 r2 isv.
  unfold reduces_to in r2; exrepnd.
  revert dependent t2.
  revert dependent t1.
  induction k; introv r1 r2.

  - allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eapply compose_reduces_to_step_primarg_ncompop in r1;[|eauto|]; auto.
    eapply IHk; eauto.
Qed.

Lemma compose_reduces_to_primarg_arithop {o} :
  forall lib c can bs (t1 t2 u : @NTerm o) l,
    reduces_to
      lib
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs) :: bterm [] t1 :: l)) u
    -> reduces_to lib t1 t2
    -> isvalue_like u
    -> reduces_to
         lib
         (oterm (NCan (NArithOp c))
                (bterm [] (oterm (Can can) bs) :: bterm [] t2 :: l)) u.
Proof.
  introv r1 r2 isv.
  unfold reduces_to in r2; exrepnd.
  revert dependent t2.
  revert dependent t1.
  induction k; introv r1 r2.

  - allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    eapply compose_reduces_to_step_primarg_arithop in r1;[|eauto|]; auto.
    eapply IHk; eauto.
Qed.

Lemma if_has_value_like_except_ncompop_can1 {o} :
  forall lib a c can bs (t : @NTerm o) l,
    has_value_like_except
      lib a
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_ncompop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (pk2term pk); dands; eauto 3 with slow.
    rw @pk2term_eq; simpl; tcsp.

  - exists e; dands; auto.
    + unfold isvalue_like; simpl; sp.
    + apply isexc_implies2 in h0; exrepnd; subst.
      eapply compose_reduces_to_primarg_ncompop in h1; eauto.
      apply reduces_to_split2 in h1; dorn h1.
      * subst; allunfold @isvalue_like; allsimpl; sp.
      * exrepnd; csunf h1; simpl in h1; ginv.
        dcwf h; ginv.
        apply reduces_to_if_isvalue_like in h0; eauto with slow.
        subst; auto.
Qed.

Lemma if_has_value_like_except_arithop_can1 {o} :
  forall lib a c can bs (t : @NTerm o) l,
    has_value_like_except
      lib a
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_narithop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists u; sp. }

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.
    + intro k; inversion k.

  - exists e; dands; auto.
    + unfold isvalue_like; simpl; sp.
    + apply isexc_implies2 in h0; exrepnd; subst.
      eapply compose_reduces_to_primarg_arithop in h1; eauto.
      apply reduces_to_split2 in h1; dorn h1.
      * subst; allunfold @isvalue_like; allsimpl; sp.
      * exrepnd; csunf h1; simpl in h1; ginv.
        dcwf h; ginv.
        apply reduces_to_if_isvalue_like in h0; eauto with slow.
        subst; auto.
Qed.

Lemma if_hasvalue_like_ncompop_can1 {o} :
  forall lib c can bs (t : @NTerm o) l,
    hasvalue_like
      lib
      (oterm (NCan (NCompOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.

  pose proof (converges_to_value_like_ncompop lib c can bs t l) as h.
  autodimp h hyp.

  { unfold converges_to_value_like; exists v; sp. }

  repndors; exrepnd.

  - exists (pk2term pk); dands; eauto 3 with slow.

  - exists e; dands; auto.
    unfold isvalue_like; simpl; sp.
Qed.

Lemma if_hasvalue_like_arithop_can1 {o} :
  forall lib c can bs (t : @NTerm o) l,
    hasvalue_like
      lib
      (oterm (NCan (NArithOp c))
             (bterm [] (oterm (Can can) bs)
                    :: bterm [] t
                    :: l))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.

  pose proof (converges_to_value_like_narithop lib c can bs t l) as h.
  autodimp h hyp.

  repndors; exrepnd.

  - exists (@mk_integer o i); dands.
    + unfold computes_to_value in h0; sp.
    + unfold isvalue_like; simpl; sp.

  - exists e; dands; auto.
    unfold isvalue_like; simpl; sp.
Qed.

Lemma reduces_in_atmost_k_steps_if_isvalue_like {o} :
  forall lib k (t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t1 t2 k
    -> isvalue_like t1
    -> t2 = t1.
Proof.
  induction k; introv r iv.
  - rw @reduces_in_atmost_k_steps_0 in r; auto.
  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    rw @compute_step_value_like in r1; auto; ginv.
    apply IHk in r0; auto; subst; auto.
Qed.

Lemma reduces_in_atmost_k_steps_if_reduces_to {o} :
  forall lib k (t1 t2 v : @NTerm o),
    reduces_in_atmost_k_steps lib t1 v k
    -> reduces_to lib t1 t2
    -> isvalue_like v
    -> {k' : nat & k' <= k # reduces_in_atmost_k_steps lib t2 v k'}.
Proof.
  introv r1 r2 iv.
  unfold reduces_to in r2; exrepnd.
  destruct (le_gt_dec k0 k) as [i|i].
  - pose proof (reduces_atmost_split lib k0 k t1 t2 v) as h.
    repeat (autodimp h hyp).
    exists (k - k0); dands; auto; try omega.
  - pose proof (reduces_atmost_split lib k k0 t1 v t2) as h.
    repeat (autodimp h hyp); try omega.
    apply reduces_in_atmost_k_steps_if_isvalue_like in h; auto; subst.
    exists 0; dands; auto; try omega.
    rw @reduces_in_atmost_k_steps_0; auto.
Qed.

Lemma wf_term_absolute_value {o} :
  forall (t : @NTerm o), wf_term (absolute_value t) <=> wf_term t.
Proof.
  introv; unfold absolute_value.
  rw <- @wf_less_iff.
  rw <- @wf_minus_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma wf_term_force_int {o} :
  forall (t : @NTerm o), wf_term (force_int t) <=> wf_term t.
Proof.
  introv; unfold force_int.
  rw @wf_arithop_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma hasvalue_like_absolute_value {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> hasvalue_like lib (absolute_value t)
    -> ({z : Z & computes_to_value lib t (mk_integer z)} [+] raises_exception lib t).
Proof.
  introv wf r.
  unfold hasvalue_like in r; exrepnd.
  unfold absolute_value, reduces_to in r1; exrepnd.
  pose proof (has_value_like_k_mk_less lib k t mk_zero (mk_minus t) t) as h.
  repeat (autodimp h hyp); eauto 3 with slow;
  try (apply wf_minus; auto).
  { exists v; unfold computes_to_val_like_in_max_k_steps; dands; auto. }

  repndors; exrepnd.

  - right.
    exists u e k1; auto.

  - left.
    exists z.
    split; eauto 3 with slow.

  - left.
    exists i1.
    split; eauto 3 with slow.
Qed.

Lemma computes_to_exception_minus {o} :
  forall lib (t : @NTerm o) a e,
    wf_term t
    -> computes_to_exception lib a (mk_minus t) e
    -> computes_to_exception lib a t e.
Proof.
  introv wf r.
  allunfold @computes_to_exception.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; ginv.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    csunf comp1; allsimpl.
    destruct t as [v|f|op bs]; ginv.
    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.

    + Case "Can".
      apply compute_step_minus_success in comp1; exrepnd; subst; GC; fold_terms.
      apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; ginv.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bs)) as cs; symmetry in Heqcs; destruct cs; allsimpl; ginv.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto.
      eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; ginv.
      unfold mk_exception in comp0; ginv; eauto 3 with slow.

    + Case "Abs".
      remember (compute_step lib (oterm (Abs abs) bs)) as cs; symmetry in Heqcs; destruct cs; allsimpl; ginv.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma computes_to_exception_absolute_value {o} :
  forall lib (t : @NTerm o) a e,
    wf_term t
    -> computes_to_exception lib a (absolute_value t) e
    -> computes_to_exception lib a t e.
Proof.
  introv wf r.
  apply computes_to_exception_mk_less in r; eauto 3 with slow;
  try (apply wf_minus; auto).

  repndors; exrepnd; repndors; exrepnd; auto;
  try (complete (exists a e; auto)).

  - apply computes_to_exception_minus in r1; auto.

  - apply can_doesnt_raise_an_exception in r0; sp.
Qed.

(*
Lemma absolute_value_reduces_to_int {o} :
  forall lib (t : @NTerm o) z,
    reduces_to lib (absolute_value t) (mk_integer z)
    -> {i : Z & reduces_to lib t (mk_integer i) # z = Z.abs i}.
Proof.
  introv comp.
  unfold reduces_to in comp; exrepnd.
  revert dependent t.
  induction k; introv comp.

  - allrw @reduces_in_atmost_k_steps_0; ginv.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [v|f|op bs]; ginv.
    dopid op as [can|ncan|exc|abs] Case.

    + Case "Can".
      dcwf h; allsimpl.
      apply compute_step_compop_success_can_can in comp1; exrepnd; subst; GC; allsimpl.
      repndors; exrepnd; subst; ginv.
      allrw @get_param_from_cop_some; subst; allsimpl; fold_terms.
      boolvar.

      * pose proof (computes_to_val_like_in_max_k_steps_minus_implies
                      lib k (mk_integer n1) (mk_integer z)) as h.
        autodimp h hyp.
        { split; eauto 3 with slow. }
        exrepnd; repndors; exrepnd; subst; allsimpl; ginv; tcsp.

        exists n1; dands; eauto 3 with slow.
        apply computes_to_val_like_in_max_k_steps_if_isvalue_like in h2; eauto 3 with slow; ginv.
        symmetry; apply Z.abs_neq; try omega.

      * apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; ginv.
        exists n1; dands; eauto 3 with slow.
        symmetry; apply Z.abs_eq; try omega.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bs)) as cs; symmetry in Heqcs; destruct cs; ginv.
      pose proof (IHk n) as h; autodimp h hyp.
      {
      }
Qed.
 *)

(*
Lemma hasvalue_like_subst_less_bound2 {o} :
  forall lib b v (t : @NTerm o),
    wf_term t
    -> hasvalue_like
         lib
         (subst (less_bound b (mk_var v) (mk_vbot v)) v t)
    -> ({z : Z & computes_to_value lib t (mk_integer z) # Z.abs_nat z < b}
        [+] raises_exception lib t).
Proof.
  introv wf r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.

    remember (compute_step lib (absolute_value t)) as cs;
      symmetry in Heqcs; destruct cs; ginv.
    fold_terms.
    unfold reduces_to in r2; exrepnd.
    applydup @compute_step_preserves_wf in Heqcs; auto;
    try (apply wf_term_absolute_value; auto).

    pose proof (has_value_like_k_mk_less lib k n (mk_nat b) t (mk_fix (mk_lam v (mk_var v)))) as h.
    repeat (autodimp h hyp); eauto 3 with slow;
    try (apply wf_fix; apply wf_lam; eauto 3 with slow).
    { exists v0.
      unfold computes_to_val_like_in_max_k_steps; dands; auto. }
    repndors; exrepnd.

    { pose proof (computes_to_exception_absolute_value lib t u e) as q.
      repeat (autodimp q hyp).
      { eapply computes_to_exception_step;[|eauto].
        exists k1; auto. }
      right.
      exists u e; auto. }

    { apply computes_to_exception_in_max_k_steps_can in h3; sp. }

    { apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in h3; eauto 3 with slow.
      allunfold @mk_nat; ginv; fold_terms.
      boolvar;[|apply has_value_like_k_vbot in h4; sp];[].
      left.


    }

      pose proof (hasvalue_like_absolute_value lib t) as q.
      repeat (autodimp q hyp).
      { exists (mk_exception u e); dands; eauto 3 with slow.
        eapply reduces_to_if_split2;[eauto|].
        exists k1; auto. }
      repndors; exrepnd.
      { left.
        exists z; dands; auto.

XXXXXXXXXXXX

    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; repndors; csunf r2; allsimpl; exrepnd; subst; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }

  { unfold hasvalue_like in r; exrepnd.

    apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    csunf r1; allsimpl.
    unfold on_success in r1.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1.
    destruct bs; allsimpl; ginv.
    remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
    destruct p; ginv.
    allapply @get_param_from_cop_pki; subst.

    apply reduces_to_split2 in r2; dorn r2; allsimpl; exrepnd; subst.

    { unfold isvalue_like in r0; allsimpl; sp. }

    boolvar; allsimpl; ginv.

    - apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst; csunf r2; allsimpl; ginv.

      { unfold isvalue_like in r0; allsimpl; sp. }

      csunf r1; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r1; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r3; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_neg; auto.

      + apply reduces_to_vbot_if_isvalue_like in r3; eauto with slow; subst; sp.

    - csunf r2; allsimpl.
      dcwf h; allsimpl.
      unfold compute_step_comp in r2; allsimpl; ginv.
      boolvar; allsimpl.

      + apply reduces_to_if_isvalue_like in r1; eauto with slow; subst.
        exists z; dands; auto.
        apply abs_of_pos; auto.

      + apply reduces_to_vbot_if_isvalue_like in r1; eauto with slow; subst; sp.
  }
Qed.
 *)

Lemma hasvalue_like_subst_less_bound_seq {o} :
  forall lib b v e (f : @ntseq o),
    hasvalue_like
      lib
      (subst (less_bound b (mk_var v) e) v (sterm f))
    -> False.
Proof.
  introv r.
  unfold subst, lsubst in r; allsimpl; boolvar;
  repndors; try (subst v'); tcsp;
  allrw not_over_or; repnd; GC;
  try (complete (match goal with
                   | [ H : context[fresh_var ?l] |- _ ] =>
                     let h := fresh "h" in
                     pose proof (fresh_var_not_in l) as h;
                   unfold all_vars in h;
                   simpl in h;
                   repeat (rw in_app_iff in h);
                   repeat (rw not_over_or in h);
                   repnd; allsimpl; tcsp
                 end));
  allsimpl; boolvar; tcsp; fold_terms; allrw app_nil_r.

  unfold hasvalue_like in r; exrepnd.
  apply reduces_to_split2 in r1; dorn r1; allsimpl; exrepnd; subst.
  { unfold isvalue_like in r0; allsimpl; sp. }
  csunf r1; allsimpl; ginv.
Qed.

Lemma reduces_to_force_int_bound {o} :
  forall lib v b (t e u : @NTerm o),
    nt_wf t
    -> !LIn v (free_vars e)
    -> disjoint (bound_vars e) (free_vars t) (* should be enough, make things easier *)
    -> reduces_to lib (force_int_bound v b t e) u
    -> isvalue_like u
    -> {z : Z & reduces_to lib t (mk_integer z)
        # (
           (Z.abs_nat z < b # u = mk_integer z)
           [+]
           (b <= Z.abs_nat z # reduces_to lib e u)
          )
       }
       [+]
       (reduces_to lib t u # isexc u).
Proof.
  introv wf ni disj r.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf disj r isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v1|f1|op1 bs1].

    { simpl in r1; ginv. }

    { csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl.
      allrw @fold_subst.
      pose proof (hasvalue_like_subst_less_bound_seq lib b v e f1) as h.
      autodimp h hyp; tcsp.
      exists u; dands; auto.
      exists k; auto. }

    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl.
      unfold lsubst in r0.
      boolvar;[|provefalse; simpl in n; allrw app_nil_r; complete sp].
      simpl in r0; boolvar.
      fold_terms.
      rw @lsubst_aux_trivial_cl_term in r0;
        [|simpl; rw disjoint_singleton_r; auto].
      destruct k.

      { allrw @reduces_in_atmost_k_steps_0; subst.
        allunfold @isvalue_like; allsimpl; sp. }

      allrw @reduces_in_atmost_k_steps_S; exrepnd.
      allsimpl; allrw app_nil_r.
      csunf r0; allsimpl.
      unfold on_success in r0.
      csunf r0; allsimpl.
      dcwf h; allsimpl.
      match goal with
        | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
          remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
      end.
      symmetry in Heqcomp; destruct comp; ginv.
      apply compute_step_compop_success_can_can in Heqcomp.
      exrepnd; subst; allsimpl; cpx; GC.
      repndors; exrepnd; ginv.
      allapply @get_param_from_cop_pki; subst.

      destruct k.

      { allrw @reduces_in_atmost_k_steps_0; subst.
        unfold isvalue_like in isv; allsimpl; cpx. }

      allrw @reduces_in_atmost_k_steps_S; exrepnd.
      left.
      csunf r1; allsimpl.
      boolvar; allsimpl; ginv.

      * destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        allsimpl.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

        { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
          exists n1; dands; eauto with slow.
          left; dands; eauto with slow.
          apply abs_of_neg; auto. }

        { exists n1; dands; eauto with slow.
          right; dands; eauto with slow.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-n1)) as p.
          autodimp p hyp; try omega.
          allrw Znat.Zabs2Nat.id.
          destruct n1; allsimpl; try omega. }

      * dcwf h; allsimpl.
        unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

        { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
          exists n1; dands; eauto with slow.
          left; dands; eauto with slow.
          apply abs_of_pos; auto. }

        { exists n1; dands; eauto with slow.
          right; dands; eauto with slow.
          pose proof (Zabs.Zabs_nat_le (Z.of_nat b) n1) as p.
          autodimp p hyp; try omega.
          allrw Znat.Zabs2Nat.id.
          destruct n1; allsimpl; try omega. }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      applydup @compute_step_preserves in Heqcomp; repnd; auto.
      eapply subvars_disjoint_r in Heqcomp1;[|exact disj].

      apply IHk in r0; auto; exrepnd.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; simpl in r1; ginv.
      right.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.

    + Case "Abs".
      csunf r1; allsimpl.
      unfold on_success in r1.
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      pose proof (compute_step_preserves lib (oterm (Abs abs1) bs1) n) as h.
      repeat (autodimp h hyp); repnd.
      eapply subvars_disjoint_r in h0;[|exact disj].

      apply IHk in r0; auto.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.
Qed.

Lemma reduces_to_force_int_bound_vbot {o} :
  forall lib v b (t u : @NTerm o),
    nt_wf t
    -> reduces_to lib (force_int_bound v b t (mk_vbot v)) u
    -> isvalue_like u
    -> {z : Z & reduces_to lib t (mk_integer z)
        # Z.abs_nat z < b
        # u = mk_integer z}
       [+]
       (reduces_to lib t u # isexc u).
Proof.
  introv wf r isv.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv wf r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v1|f1|op1 bs1].

    { simpl in r1; ginv. }

    { csunf r1; allsimpl; ginv.
      unfold apply_bterm in r0; allsimpl; allrw @fold_subst.
      pose proof (hasvalue_like_subst_less_bound_seq lib b v (mk_vbot v) f1) as h.
      autodimp h hyp; tcsp.
      exists u; dands; auto.
      exists k; auto. }

    dopid op1 as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      csunf r1; simpl in r1; ginv.
      unfold apply_bterm in r0; allsimpl.
      unfold lsubst in r0.
      boolvar; allsimpl; fold_terms; boolvar; allsimpl;
      allrw app_nil_r; allrw @var_ren_nil_l; allrw @lsubst_aux_nil;
      repndors; tcsp; GC; boolvar; allrw not_over_or; repnd; tcsp; GC;
      try (complete (match goal with
                       | [ H : context[fresh_var ?l] |- _ ] =>
                         let h := fresh "h" in
                         pose proof (fresh_var_not_in l) as h;
                       unfold all_vars in h;
                       simpl in h;
                       repeat (rw in_app_iff in h);
                       repeat (rw not_over_or in h);
                       repnd; allsimpl; tcsp
                     end)); fold_terms.

      { destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          allunfold @isvalue_like; allsimpl; sp. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        csunf r0; allsimpl.
        unfold on_success in r0.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        match goal with
          | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
            remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
        end.
        symmetry in Heqcomp; destruct comp; ginv.
        apply compute_step_compop_success_can_can in Heqcomp.
        exrepnd; subst; allsimpl; cpx; GC.
        repndors; exrepnd; ginv.
        allapply @get_param_from_cop_pki; subst.

        destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        left.
        csunf r1; allsimpl.
        boolvar; allsimpl; ginv.

        * destruct k.

          { allrw @reduces_in_atmost_k_steps_0; subst.
            unfold isvalue_like in isv; allsimpl; cpx. }

          allrw @reduces_in_atmost_k_steps_S; exrepnd.
          csunf r0; allsimpl.
          dcwf h; allsimpl.
          unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_neg; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r1; sp. }

        * dcwf h; allsimpl.
          unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_pos; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r0; sp. }
      }

      { destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          allunfold @isvalue_like; allsimpl; sp. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        csunf r0; allsimpl.
        unfold on_success in r0.
        csunf r0; allsimpl.
        dcwf h; allsimpl.
        fold_terms.
        match goal with
          | [ H : context[compute_step_comp ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] |- _ ] =>
            remember (compute_step_comp a1 a2 a3 a4 a5 a6 a7)  as comp
        end.
        symmetry in Heqcomp; destruct comp; ginv.
        apply compute_step_compop_success_can_can in Heqcomp.
        exrepnd; subst; allsimpl; cpx; GC.
        repndors; exrepnd; ginv.
        allapply @get_param_from_cop_pki; subst.

        destruct k.

        { allrw @reduces_in_atmost_k_steps_0; subst.
          unfold isvalue_like in isv; allsimpl; cpx. }

        allrw @reduces_in_atmost_k_steps_S; exrepnd.
        left.
        csunf r1; allsimpl.
        boolvar; allsimpl; ginv.

        * destruct k.

          { allrw @reduces_in_atmost_k_steps_0; subst.
            unfold isvalue_like in isv; allsimpl; cpx. }

          allrw @reduces_in_atmost_k_steps_S; exrepnd.
          csunf r0; allsimpl.
          dcwf h; allsimpl.
          unfold compute_step_comp in r0; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r1; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_neg; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r1; sp. }

        * dcwf h; allsimpl.
          unfold compute_step_comp in r1; allsimpl; boolvar; ginv.

          { apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.
            exists n1; dands; eauto with slow.
            apply abs_of_pos; auto. }

          { provefalse; apply reduces_in_atmost_k_steps_vbot in r0; sp. }
      }

    + Case "NCan".
      unfold force_int_bound in r1.
      rw @compute_step_mk_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      applydup @compute_step_preserves in Heqcomp; repnd; auto.

      apply IHk in r0; auto; exrepnd.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; simpl in r1; ginv.
      right.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.

    + Case "Abs".
      csunf r1; allsimpl.
      unfold on_success in r1.
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs1 bs1) as comp.
      symmetry in Heqcomp; destruct comp; ginv.

      pose proof (compute_step_preserves lib (oterm (Abs abs1) bs1) n) as h.
      repeat (autodimp h hyp); repnd.

      apply IHk in r0; auto.
      dorn r0; exrepnd.

      * left; exists z; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @computes_to_exception; dands; auto.
        eapply reduces_to_if_split2; eauto.
Qed.

Lemma if_has_value_like_except_force_int_bound {o} :
  forall lib a v b (t : @NTerm o),
    nt_wf t
    -> has_value_like_except
         lib a
         (force_int_bound v b t (uexc a))
    -> {u : NTerm
        & reduces_to lib t u
        # isvalue_like u
        # (
           {z : Z & u = mk_integer z # Z.abs_nat z < b}
           [+]
           (isexc u # !isnexc lib a u)
          )
       }.
Proof.
  introv wf hv.
  unfold has_value_like_except in hv; exrepnd.
  apply reduces_to_force_int_bound in hv1; simpl; tcsp.
  dorn hv1; exrepnd.

  - exists (@mk_integer o z); dands; eauto with slow;
    try (complete (unfold mk_integer; eauto with slow)).
    left; exists z; dands; auto.
    dorn hv3; repnd; auto.
    apply reduces_to_if_isvalue_like in hv3;[|unfold uexc; eauto with slow].
    subst.
    destruct hv0.
    simpl; boolvar; eauto with slow.

  - exists u; dands; eauto with slow.
Qed.

Lemma if_hasvalue_like_force_int_bound {o} :
  forall lib v b (t : @NTerm o),
    nt_wf t
    -> hasvalue_like lib (force_int_bound v b t (mk_vbot v))
    -> {u : NTerm
        & reduces_to lib t u
        # isvalue_like u
        # (
           {z : Z & u = mk_integer z # Z.abs_nat z < b}
           [+]
           isexc u
          )
       }.
Proof.
  introv wf hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_to_force_int_bound_vbot in hv1; simpl; tcsp;
  allrw remove_nvars_eq; tcsp.
  dorn hv1; exrepnd.

  - exists (@mk_integer o z); dands; eauto with slow;
    try (complete (unfold mk_integer; eauto with slow)).

  - exists v0; dands; eauto with slow.
Qed.

Lemma reduces_to_cbv_to_value_like {o} :
  forall lib (t : @NTerm o) v b u,
    reduces_to lib (mk_cbv t v b) u
    -> isvalue_like u
    -> {c : NTerm & reduces_to lib t c # iscan c # reduces_to lib (subst b v c) u}
       [+]
       (reduces_to lib t u # isexc u).
Proof.
  introv r.
  unfold reduces_to in r; exrepnd.
  revert dependent t.
  induction k; introv r isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isv; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [x|f|op bs]; try (complete (allsimpl; ginv)).

    { csunf r1; allsimpl; ginv.
      allunfold @apply_bterm; allsimpl; allrw @fold_subst.
      left.
      exists (sterm f); simpl; dands; eauto 3 with slow. }

    dopid op as [can|ncan|exc|abs] Case.

    + Case "Can".
      csunf r1; simpl in r1; ginv.
      left.
      unfold apply_bterm in r0; allsimpl.
      exists (oterm (Can can) bs); dands; eauto with slow.

    + Case "NCan".
      rw @compute_step_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan) bs)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; auto; dorn r0; exrepnd.

      * left; exists c; dands; eauto with slow.
        eapply reduces_to_if_split2; eauto.

      * right; dands; eauto with slow.
        eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; subst; eauto with slow.

    + Case "Abs".
      rw @compute_step_cbv_abs in r1.
      remember (compute_step lib (oterm (Abs abs) bs)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; auto; dorn r0; exrepnd.

      * left; exists c; dands; eauto with slow.
        eapply reduces_to_if_split2; eauto.

      * right; dands; eauto with slow.
        eapply reduces_to_if_split2; eauto.
Qed.

Lemma reduces_to_int_subst_less_bound3 {o} :
  forall lib b v a can (bs : list (@BTerm o)) u,
    reduces_to
      lib
      (subst (less_bound b (mk_var v) (uexc a)) v (oterm (Can can) bs))
      u
    -> isvalue_like u
    -> {z : Z
        & can = Nint z
        # bs = []
        # (
           (Z.abs_nat z < b # u = mk_integer z)
           [+]
           (b <= Z.abs_nat z # u = uexc a)
          )
       }.
Proof.
  introv r isv.
  unfold subst, lsubst in r; allsimpl; boolvar.
  fold_terms.

  apply reduces_to_split2 in r; dorn r; subst.

  { allunfold @isvalue_like; allsimpl; sp. }

  exrepnd; allsimpl.
  csunf r1; allsimpl; unfold on_success in r1.
  csunf r1; allsimpl.
  dcwf h; allsimpl.
  unfold compute_step_comp in r1.
  destruct bs; allsimpl; ginv.
  remember (get_param_from_cop can) as g; symmetry in Heqg; destruct g; ginv.
  destruct p; ginv.
  allapply @get_param_from_cop_pki; subst.

  apply reduces_to_split2 in r0; dorn r0; subst.

  { allunfold @isvalue_like; allsimpl; sp. }

  exrepnd; allsimpl.
  boolvar; allsimpl; ginv; csunf r0; allsimpl; ginv.

  - apply reduces_to_split2 in r1; dorn r1; subst.

    { allunfold @isvalue_like; allsimpl; sp. }

    exrepnd; allsimpl.
    csunf r1; allsimpl.
    dcwf h; allsimpl.
    unfold compute_step_comp in r1; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      subst.
      exists z; dands; auto.
      left; dands; auto.
      apply abs_of_neg; auto.

    + apply reduces_to_if_isvalue_like in r0; eauto with slow.
      subst.
      exists z; dands; auto.
      right; dands; auto.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) (-z)) as k.
      autodimp k hyp; try omega.
      allrw Znat.Zabs2Nat.id.
      destruct z; allsimpl; try omega.

  - dcwf h; allsimpl.
    unfold compute_step_comp in r0; allsimpl; ginv.
    boolvar; allsimpl.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      subst.
      exists z; dands; auto.
      left; dands; auto.
      apply abs_of_pos; auto.

    + apply reduces_to_if_isvalue_like in r1; eauto with slow.
      subst.
      exists z; dands; auto.
      right; dands; auto.
      pose proof (Zabs.Zabs_nat_le (Z.of_nat b) z) as k.
      autodimp k hyp; try omega.
      allrw Znat.Zabs2Nat.id.
      destruct z; allsimpl; try omega.
Qed.

(*
Lemma if_has_value_like_except_ncan_primarg {o} :
  forall lib a ncan (t : @NTerm o) bs,
    has_value_like_except lib a (oterm (NCan ncan) (bterm [] t :: bs))
    -> has_value_like_except lib a t.
Proof.
  introv hv.
  allunfold @has_value_like_except; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t.
  induction k; introv r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv2; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [v|op l].

    { simpl in r1; ginv. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists (oterm (Can can1) l); dands; simpl; eauto with slow; tcsp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists u0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; allsimpl.
      apply compute_step_catch_success in r1.
      repndors; exrepnd; subst; allsimpl.

      *

Lemma reduces_in_atmost_k_steps_mk_atom_eq {o}:
  forall lib (a b c d : @NTerm o) u,
    reduces_in_atmost_k_steps lib (mk_atom_eq a b c d) u k
    -> isvalue_like u
    -> {k1 : nat
        & {k2 : nat
        & {v1 : NTerm
        & {v2 : NTerm
        & reduces_in_atmost_k_steps lib a v1 k1
        # reduces_in_atmost_k_steps lib b v2 k2
        # }}}}.
Proof.
Qed.

        exists (oterm Exc [bterm [] a', bterm [] e]); dands; eauto with slow.
        allsimpl.
        destruct exc1; allsimpl; tcsp.
        boolvar; ginv; allrw not_over_or; tcsp.

      * apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; subst.
        exists (oterm (Exc exc1) l); dands; eauto with slow.

    + Case "Mrk".
      allsimpl; ginv.
      apply reduces_in_atmost_k_steps_primarg_marker in r0; subst.
      unfold isvalue_like in hv2; allsimpl; sp.

    + Case "Abs".
      allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists u0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.
Qed.
*)

Lemma if_hasvalue_like_ncan_primarg {o} :
  forall lib ncan (t : @NTerm o) bs,
    hasvalue_like lib (oterm (NCan ncan) (bterm [] t :: bs))
    -> hasvalue_like lib t.
Proof.
  introv hv.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hv1; exrepnd.
  revert dependent t.
  induction k; introv r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in hv0; allsimpl; sp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    destruct t as [x|f|op l].

    { simpl in r1; ginv. }

    { exists (sterm f); dands; eauto 3 with slow. }

    dopid op as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      exists (oterm (Can can1) l); dands; simpl; eauto with slow; tcsp.

    + Case "NCan".
      rw @compute_step_ncan_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan1) l)) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists v0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.

    + Case "Exc".
      csunf r1; allsimpl.
      apply compute_step_catch_success in r1.
      dorn r1; exrepnd; subst; allsimpl.

      * exists (oterm Exc [bterm [] a', bterm [] e]); dands; eauto with slow.

      * apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto with slow; subst.

    + Case "Abs".
      csunf r1; allsimpl.
      csunf r1; allsimpl.
      unfold on_success in r1.
      remember (compute_step_lib lib abs1 l) as comp.
      symmetry in Heqcomp; destruct comp; ginv.
      apply IHk in r0; exrepnd.
      exists v0; dands; eauto with slow.
      eapply reduces_to_if_split2; eauto.
Qed.

(*
Lemma if_has_value_like_except_exc {o} :
  forall lib a exc (bs : list (@BTerm o)),
    has_value_like_except lib a (oterm (Exc exc) bs)
    -> exc <> Some a.
Proof.
  introv hv.
  unfold has_value_like_except in hv; exrepnd.
  apply reduces_to_if_isvalue_like in hv1; eauto with slow.
  subst.
  introv k.
  destruct exc; allsimpl; ginv; boolvar; cpx.
Qed.
*)

(*
Lemma compute_step_apply_failure {o} :
  forall can (bs1 bs2 : list (@BTerm o)) s t,
    compute_step_apply
      can
      (oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
      bs1 bs2 = cfailure s t
    -> (
         (can = NLambda
          # (forall v b, bs1 <> [bterm [v] b])
          # s = compute_step_apply_not_well_formed
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
         [+]
         (can = NLambda
          # (forall arg, bs2 <> [bterm [] arg])
          # s = compute_step_apply_not_well_formed
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
         [+]
         (can <> NLambda
          # s = bad_first_arg
          # t = oterm (NCan NApply) (bterm [] (oterm (Can can) bs1) :: bs2))
       ).
Proof.
  introv comp.
  destruct can;
    try (complete (simpl in comp; ginv; right; right; dands; tcsp; intro k; inversion k)).
  destruct bs1.
  - simpl in comp; ginv.
    left; dands; sp.
  - destruct bs1.
    + destruct b.
      destruct l.
      * simpl in comp; ginv.
        left; dands; tcsp.
        introv k; tcsp; ginv.
      * destruct l.
        { destruct bs2.
          { simpl in comp; ginv.
            right; left; sp. }
          { destruct bs2.
            - destruct b.
              destruct l.
              + simpl in comp; ginv.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
                introv k; ginv.
            - destruct b.
              destruct l.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
              + simpl in comp; ginv.
                right; left; dands; tcsp.
          }
        }
        { simpl in comp; ginv.
          left; dands; tcsp.
          introv k; ginv. }
    + destruct b.
      destruct l.
      * simpl in comp; ginv.
        left; dands; tcsp.
      * destruct l.
        { simpl in comp; ginv.
          left; dands; tcsp. }
        { simpl in comp; ginv.
          left; dands; tcsp. }
Qed.
*)

Lemma reduces_to_steps_alpha {o} :
  forall lib (t1 t2 t : @NTerm o),
    nt_wf t1
    -> alpha_eq t1 t2
    -> reduces_to lib t1 t
    -> {u : NTerm $ reduces_to lib t2 u # alpha_eq t u}.
Proof.
  introv wf aeq r.
  unfold reduces_to in r; exrepnd.
  pose proof (reduces_in_atmost_k_steps_alpha lib t1 t2 wf aeq k t r0) as h.
  exrepnd.
  exists t2'; dands; auto.
  exists k; auto.
Qed.

Lemma alpha_eq_bterms_nil {o} :
  @alpha_eq_bterms o [] [].
Proof.
  unfold alpha_eq_bterms, br_bterms, br_list; simpl; sp.
Qed.
Hint Resolve alpha_eq_bterms_nil : slow.

Lemma alpha_eq_bterms_cons_if {o} :
  forall (b1 b2 : @BTerm o) bs1 bs2,
    alpha_eq_bterm b1 b2
    -> alpha_eq_bterms bs1 bs2
    -> alpha_eq_bterms (b1 :: bs1) (b2 :: bs2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_bterms_cons; auto.
Qed.
Hint Resolve alpha_eq_bterms_cons_if : slow.

Lemma length_mk_fresh_bterms {o} :
  forall v (bs : list (@BTerm o)),
    length (mk_fresh_bterms v bs) = length bs.
Proof.
  introv; unfold mk_fresh_bterms.
  allrw map_length; auto.
Qed.

Lemma free_vars_subst_utokens_aux_subset {o} :
  forall (t : @NTerm o) (sub : utok_sub),
    subset (free_vars (subst_utokens_aux t sub))
           (free_vars t ++ free_vars_utok_sub sub).
Proof.
  introv.
  rw <- subvars_eq; apply free_vars_subst_utokens_aux.
Qed.

Lemma wf_force_int_bound {o} :
  forall v b (t : @NTerm o) e,
    wf_term (force_int_bound v b t e) <=> (wf_term t # wf_term e).
Proof.
  introv.
  unfold force_int_bound.
  rw <- @wf_cbv_iff.
  unfold less_bound.
  rw <- @wf_less_iff.
  unfold absolute_value.
  rw <- @wf_less_iff.
  rw @wf_minus.
  split; introv k; repndors; repnd; dands; tcsp.
Qed.

Lemma wf_term_force_int_bound_F_if {o} :
  forall x b (F f e : @NTerm o),
    wf_term F
    -> wf_term f
    -> wf_term e
    -> wf_term (force_int_bound_F x b F f e).
Proof.
  introv wF wf we.
  unfold force_int_bound_F.
  apply wf_apply; auto.
  unfold force_int_bound_f.
  apply wf_lam.
  apply wf_cbv.
  - apply wf_force_int_bound; sp.
  - apply wf_apply; sp.
Qed.
Hint Resolve wf_term_force_int_bound_F_if : slow.

Lemma wf_term_force_int_F_if {o} :
  forall x (F f : @NTerm o),
    wf_term F
    -> wf_term f
    -> wf_term (force_int_F x F f).
Proof.
  introv wF wf.
  unfold force_int_F.
  apply wf_apply; auto.
  unfold force_int_f.
  apply wf_lam.
  apply wf_cbv; tcsp.
  apply wf_apply; sp.
Qed.
Hint Resolve wf_term_force_int_F_if : slow.

Lemma hasvalue_like_fresh_implies {o} :
  forall lib a v (t : @NTerm o),
    wf_term t
    -> !LIn a (get_utokens t)
    -> hasvalue_like lib (mk_fresh v t)
    -> hasvalue_like lib (subst t v (mk_utoken a)).
Proof.
  introv wt nia hvl.
  allunfold @hasvalue_like; exrepnd.
  unfold reduces_to in hvl1; exrepnd.
  revert dependent v0.
  revert dependent t.
  revert dependent a.
  induction k; introv wt nia r isvl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    unfold isvalue_like in isvl; repndors; inversion isvl.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_ncan_bterm_cons_success in r1; repnd; subst; GC.
    repndors; exrepnd; subst; allsimpl; GC.
    + apply reduces_in_atmost_k_steps_implies_reduces_to in r0.
      apply reduces_in_atmost_k_step_fresh_id in r0; tcsp.
    + apply reduces_in_atmost_k_steps_implies_reduces_to in r0.
      apply reduces_to_if_isvalue_like in r0; eauto 4 with slow.
    + repnd; subst.
      pose proof (compute_step_subst_utoken lib t x [(v,mk_utoken (get_fresh_atom t))]) as h.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp h hyp); try (apply get_fresh_atom_prop); eauto 3 with slow.
      { apply nr_ut_sub_cons; eauto 3 with slow.
        intro i; apply get_fresh_atom_prop. }
      exrepnd.
      pose proof (h0 [(v,mk_utoken a)]) as q; clear h0; allsimpl.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
      allrw disjoint_singleton_l.
      repeat (autodimp q hyp); exrepnd.
      allrw @fold_subst.

      assert (wf_term x) as wfx.
      { eapply compute_step_preserves_wf;[exact r3|].
        apply wf_term_subst; eauto with slow. }

      assert (!LIn v (free_vars x)) as nivx.
      { intro j; apply compute_step_preserves in r3; repnd;
        [|apply nt_wf_subst; eauto 3 with slow].
        rw subvars_prop in r2; apply r2 in j; clear r2.
        apply eqset_free_vars_disjoint in j; allsimpl.
        allrw in_app_iff; allrw in_remove_nvars; allsimpl; boolvar; allsimpl; tcsp. }

      pose proof (IHk a (subst_utokens x [(get_fresh_atom t, mk_var v)])) as q; clear IHk.
      repeat (autodimp q hyp).
      { apply wf_subst_utokens; eauto 3 with slow. }
      { intro j; apply get_utokens_subst_utokens_subset in j; allsimpl.
        unfold get_utokens_utok_ren in j; allsimpl; allrw app_nil_r.
        rw in_remove in j; repnd.
        apply alphaeq_preserves_utokens in h1; rw h1 in j.
        apply get_utokens_subst in j; boolvar; allsimpl; allrw in_app_iff; tcsp; allsimpl.
        repndors; tcsp. }

      pose proof (q v0) as ih; clear q.
      repeat (autodimp ih hyp); exrepnd.

      pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom t) v) as aeq1.
      repeat (autodimp aeq1 hyp).

      pose proof (alpha_eq_ren_utokens
                    (subst (subst_utokens x [(get_fresh_atom t, mk_var v)]) v
                           (mk_utoken (get_fresh_atom t)))
                    x [(get_fresh_atom t, a)] aeq1) as aeq2.
      rw @subst_ren_utokens in aeq2; allsimpl; fold_terms.
      unfold ren_atom in aeq2; allsimpl; boolvar; tcsp.
      rw @ren_utokens_trivial in aeq2;
        [|simpl; apply disjoint_singleton_l; intro i;
          apply get_utokens_subst_utokens_subset in i; allsimpl;
          unfold get_utokens_utok_ren in i; allsimpl; rw app_nil_r in i;
          rw in_remove in i; repnd; GC;
          apply alphaeq_preserves_utokens in h1; rw h1 in i;
          apply get_utokens_subst in i; allsimpl; boolvar; allrw app_nil_r;
          allrw in_app_iff; repndors; tcsp].

      clear aeq1.

      pose proof (alpha_eq_ren_utokens
                    x (subst w v (mk_utoken (get_fresh_atom t)))
                    [(get_fresh_atom t, a)] h1) as aeq3.
      rw @subst_ren_utokens in aeq3; allsimpl; fold_terms.
      unfold ren_atom in aeq3; allsimpl; boolvar; tcsp.
      rw (ren_utokens_trivial [(get_fresh_atom t, a)] w) in aeq3;
        [|simpl; apply disjoint_singleton_l; intro i; apply h4 in i;
          apply get_fresh_atom_prop in i; sp]; GC.

      eapply alpha_eq_trans in aeq3;[|exact aeq2]; clear aeq2.
      apply alpha_eq_sym in aeq3.
      eapply alpha_eq_trans in aeq3;[|exact q0]; clear q0.

      dup ih1 as ih2.
      eapply reduces_to_alpha in ih2;
        [|apply nt_wf_subst; eauto 3 with slow;
          apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow
         |apply alpha_eq_sym in aeq3; apply aeq3]; exrepnd.
      rename t2' into s'.

      exists s'; dands; eauto 2 with slow.
      eapply reduces_to_if_split2;[exact q1|]; auto.
Qed.

Lemma alphaeq_preserves_wf_term_inv {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2 -> wf_term t2 -> wf_term t1.
Proof.
  introv aeq wf; apply alpha_eq_sym in aeq; apply alphaeq_preserves_wf_term in aeq; auto.
Qed.

Lemma implies_alpha_eq_mk_lam {o} :
  forall v (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (mk_lam v t1) (mk_lam v t2).
Proof.
  introv aeq.
  unfold mk_fresh.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; cpx.
  apply alpha_eq_bterm_congr; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
