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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sovar_alpha.
Require Export list_tacs.

Lemma get_utokens_swap {o} :
  forall s (t : @NTerm o),
    get_utokens (swap s t) = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma get_utokens_cswap {o} :
  forall s (t : @NTerm o),
    get_utokens (cswap s t) = get_utokens t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; auto.
  apply app_if; auto.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl.
  eapply ind; eauto.
Qed.

Lemma swapbvars_remove_nvars :
  forall vs1 vs2 l vs,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> swapbvars (mk_swapping vs1 vs2) (remove_nvars l vs)
       = remove_nvars (swapbvars (mk_swapping vs1 vs2) l)
                      (swapbvars (mk_swapping vs1 vs2) vs).
Proof.
  induction vs; introv norep disj; simpl.
  - allrw remove_nvars_nil_r; simpl; auto.
  - allrw remove_nvars_cons_r; boolvar; tcsp; try (rw <- IHvs; auto); allsimpl; tcsp.
    + provefalse.
      allrw in_swapbvars.
      destruct Heqb0.
      exists a; sp.
    + provefalse.
      allrw in_swapbvars; exrepnd.
      apply swapvars_eq in Heqb1; auto; subst; tcsp.
Qed.

Lemma free_vars_swap {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars (swap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (free_vars t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw flat_map_map; unfold compose.
  rw @swapbvars_flat_map.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  rw swapbvars_remove_nvars; auto.
  erewrite ind; eauto.
Qed.

Lemma free_vars_cswap {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars (cswap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (free_vars t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw flat_map_map; unfold compose.
  rw @swapbvars_flat_map.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  rw swapbvars_remove_nvars; auto.
  erewrite ind; eauto.
Qed.

Lemma subvars_d :
  forall vs1 vs2, decidable (subvars vs1 vs2).
Proof.
  introv.
  unfold decidable, subvars, assert.
  destruct (sub_vars vs1 vs2); sp.
  right; sp.
Defined.

Fixpoint bound_vars_ncl {p} (t : @NTerm p) : list NVar :=
  match t with
    | vterm v => []
    | oterm op bts => flat_map bound_vars_bterm_ncl bts
  end
 with bound_vars_bterm_ncl {p} (bt : BTerm) :=
  match bt with
  | bterm lv nt =>
    if subvars_d (free_vars nt) lv
    then []
    else lv ++ bound_vars_ncl nt
  end.

Lemma bound_vars_ncl_swap {o} :
  forall (t : @NTerm o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> bound_vars_ncl (swap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (bound_vars_ncl t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; allsimpl.
  rw @free_vars_swap; auto.
  boolvar; allsimpl; tcsp.

  - destruct n.
    allrw subvars_prop; introv j.
    pose proof (s (swapvar (mk_swapping vs1 vs2) x)) as h.
    autodimp h hyp.
    { allrw in_swapbvars.
      exists x; dands; auto. }
    allrw in_swapbvars; exrepnd.
    apply swapvars_eq in h0; subst; auto.

  - destruct n.
    allrw subvars_prop; introv j.
    allrw in_swapbvars; exrepnd; subst.
    applydup s in j1.
    eexists; dands; eauto.

  - rw swapbvars_app; f_equal.
    apply (ind t l); auto.
Qed.

Lemma bound_vars_ncl_cswap {o} :
  forall (t : @NTerm o) (vs1 vs2 : list NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> bound_vars_ncl (cswap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (bound_vars_ncl t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; allsimpl.
  rw @free_vars_cswap; auto.
  boolvar; allsimpl; tcsp.

  - destruct n.
    allrw subvars_prop; introv j.
    pose proof (s (swapvar (mk_swapping vs1 vs2) x)) as h.
    autodimp h hyp.
    { allrw in_swapbvars.
      exists x; dands; auto. }
    allrw in_swapbvars; exrepnd.
    apply swapvars_eq in h0; subst; auto.

  - destruct n.
    allrw subvars_prop; introv j.
    allrw in_swapbvars; exrepnd; subst.
    applydup s in j1.
    eexists; dands; eauto.

  - rw swapbvars_app; f_equal.
    apply (ind t l); auto.
Qed.

Lemma sub_free_vars_swap_sub {o} :
  forall vs1 vs2 (sub : @Sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_free_vars (swap_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (sub_free_vars sub).
Proof.
  induction sub; introv norep disj; allsimpl; auto.
  destruct a.
  rw swapbvars_app; f_equal; tcsp.
  rw @free_vars_swap; auto.
Qed.

Lemma sub_free_vars_cswap_sub {o} :
  forall vs1 vs2 (sub : @Sub o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_free_vars (cswap_sub (mk_swapping vs1 vs2) sub)
       = swapbvars (mk_swapping vs1 vs2) (sub_free_vars sub).
Proof.
  induction sub; introv norep disj; allsimpl; auto.
  destruct a.
  rw swapbvars_app; f_equal; tcsp.
  rw @free_vars_cswap; auto.
Qed.

Lemma alphaeq_oterm_implies_combine {o} :
  forall op bs (t : @NTerm o),
    alphaeq (oterm op bs) t
    -> {bs' : list BTerm
        & t = oterm op bs'
        # length bs = length bs'
        # (forall b1 b2 : BTerm,
             LIn (b1, b2) (combine bs bs')
             -> alphaeqbt b1 b2)}.
Proof.
  introv aeq.
  apply alphaeq_eq in aeq.
  apply alpha_eq_oterm_implies_combine in aeq; exrepnd.
  exists bs'; dands; auto.
  introv i.
  apply aeq0 in i.
  apply alphaeqbt_eq; auto.
Qed.

Lemma alphaeq_oterm_combine {o} :
  forall op (bs1 bs2 : list (@BTerm o)),
    alphaeq (oterm op bs1) (oterm op bs2)
    <=>
    (length bs1 = length bs2
     # (forall b1 b2 : BTerm,
          LIn (b1, b2) (combine bs1 bs2) -> alphaeqbt b1 b2)).
Proof.
  introv.
  rw @alphaeq_eq.
  rw @alpha_eq_oterm_combine.
  split; intro k; exrepnd; dands; auto; introv i; apply k in i;
  apply alphaeqbt_eq; auto.
Qed.

Lemma disjoint_swapbvars3 :
  forall bvs vs vs1 vs2 : list NVar,
    disjoint vs1 vs2
    -> no_repeats vs2
    -> disjoint vs2 bvs
    -> disjoint (remove_nvars vs1 bvs) vs
    -> disjoint vs2 vs
    -> length vs1 = length vs2
    -> disjoint vs (swapbvars (mk_swapping vs1 vs2) bvs).
Proof.
  introv d1 norep d2 d3 d4 len i j.
  apply disjoint_sym in d3.
  applydup d3 in i as k.
  rw in_remove_nvars in k.
  rw in_swapbvars in j; exrepnd; subst.
  apply disjoint_sym in d2.
  applydup d2 in j1 as q.
  destruct (in_deq _ deq_nvar v' vs1) as [d|d].
  - pose proof (swapvar_in vs1 vs2 v') as h.
    repeat (autodimp h hyp).
    apply d4 in h; sp.
  - rw swapvar_not_in in i; auto.
    rw swapvar_not_in in k; auto.
Qed.

Lemma map_combine_left :
  forall (T1 T2 T3 : tuniv)
         (f : T1 -> T3) (l1 : list T1) (l2 : list T2),
    map (fun x => (f (fst x), snd x)) (combine l1 l2)
    = combine (map f l1) l2.
Proof.
  induction l1; introv; allsimpl; auto.
  destruct l2; allsimpl; auto.
  rw IHl1; auto.
Qed.

Lemma alphaeq_cswap_disj_free_vars {o} :
  forall (t : @NTerm o) vs1 vs2,
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint (free_vars t) vs1
    -> disjoint (allvars t) vs2
    -> disjoint vs1 vs2
    -> alphaeq (cswap (mk_swapping vs1 vs2) t) t.
Proof.
  nterm_ind1s t as [v|op bs ind] Case;
  introv len norep d1 d2 d3; allsimpl; eauto 3 with slow.

  - Case "vterm".
    allrw disjoint_singleton_l.
    rw swapvar_not_in; eauto with slow.

  - Case "oterm".
    apply alphaeq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    rw <- map_combine_left in i; rw in_map_iff in i; exrepnd; cpx.
    rw in_combine_same in i1; repnd; subst; allsimpl.
    destruct a as [l t]; allsimpl.
    pose proof (fresh_vars (length l)
                           ((swapbvars (mk_swapping vs1 vs2) l)
                              ++ l
                              ++ vs1
                              ++ vs2
                              ++ (free_vars t)
                              ++ (allvars (cswap (mk_swapping vs1 vs2) t))
                              ++ (allvars t))) as fv; exrepnd.
    allrw disjoint_app_r; repnd.

    apply (aeqbt _ lvn); allsimpl; allrw length_swapbvars; auto;
    allrw disjoint_app_r; tcsp.
    disj_flat_map; allsimpl; allrw disjoint_app_l; repnd.

    rw @cswap_cswap.
    rw mk_swapping_app; auto.
    rw <- @cswap_app_cswap; eauto with slow.
    rw <- mk_swapping_app; auto.
    rw <- @cswap_cswap.
    apply (ind t _ l); allrw @osize_cswap; eauto 3 with slow.

    + rw @free_vars_cswap; eauto with slow.
      apply disjoint_sym.
      apply disjoint_swapbvars3; eauto with slow.

    + apply disjoint_sym.
      apply disjoint_allvars_cswap; eauto with slow.
Qed.
