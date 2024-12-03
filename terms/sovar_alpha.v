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


Require Export sovar.
Require Export alphaeq_sub.


Lemma range_combine {o} :
  forall (ts : list (@NTerm o)) vs,
    length vs = length ts
    -> range (combine vs ts) = ts.
Proof.
  induction ts; destruct vs; introv len; allsimpl; cpx.
  rw IHts; sp.
Qed.

Lemma swap_apply_list {o} :
  forall ts (t : @NTerm o) s,
    swap s (apply_list t ts) = apply_list (swap s t) (map (swap s) ts).
Proof.
  induction ts; simpl; introv; auto.
Qed.

Fixpoint so_swap {p} (l : swapping) (t : @SOTerm p) : SOTerm :=
  match t with
  | sovar v ts =>
    if bnull ts
    then sovar (swapvar l v) []
    else sovar v (map (so_swap l) ts)
  | soterm o bts => soterm o (map (so_swapbt l) bts)
  end
with so_swapbt {p} (l : swapping) (bt : SOBTerm) :=
       match bt with
       | sobterm vs t => sobterm (swapbvars l vs) (so_swap l t)
       end.

(*
Lemma soterm2nterm_so_swap {o} :
  forall (t : @SOTerm o) s,
    soterm2nterm (so_swap s t) = swap s (soterm2nterm t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv.

  - Case "sovar".
    rw @swap_apply_list; simpl.
    allrw map_map; unfold compose.
    f_equal.
    apply eq_maps; introv i.
    eapply ind in i; eauto.

  - Case "soterm".
    apply f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; allsimpl.
    f_equal.
    eapply ind in i; eauto.
Qed.
*)

Lemma wf_soterm_so_swap {o} :
  forall (t : @SOTerm o) s,
    wf_soterm t <=> wf_soterm (so_swap s t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; allrw @wf_sovar; tcsp.
    split; introv k i; allsimpl.
    + rw in_map_iff in i; exrepnd; subst.
        apply ind; auto.
    + pose proof (k (so_swap s t)) as h; autodimp h hyp.
      rw in_map_iff; eexists; dands; eauto.
      apply ind in h; tcsp.

  - Case "soterm".
    allrw @wf_soterm_iff; split; intro k; repnd; dands.
    + rw <- k0.
      rw map_map; unfold compose; apply eq_maps; introv i.
      destruct x; simpl.
      rw length_swapbvars; auto.
    + introv i.
      rw in_map_iff in i; exrepnd; subst.
      destruct a; allsimpl; ginv.
      dup i1 as i.
      eapply ind in i; rw <- i.
      apply k in i1; auto.
    + rw <- k0.
      rw map_map; unfold compose; apply eq_maps; introv i.
      destruct x; simpl.
      rw length_swapbvars; auto.
    + introv i.
      pose proof (k (swapbvars s vs) (so_swap s t)) as h; autodimp h hyp.
      rw in_map_iff; eexists; dands; eauto.
      dup i as j.
      eapply ind in i; rw <- i in h; auto.
Qed.

Inductive so_alphaeq_vs {p} (l : list NVar) : @SOTerm p -> @SOTerm p -> Type :=
  | soaeqv :
      forall v ts1 ts2,
        length ts1 = length ts2
        -> (forall t1 t2, LIn (t1,t2) (combine ts1 ts2) -> so_alphaeq_vs l t1 t2)
        -> so_alphaeq_vs l (sovar v ts1) (sovar v ts2)
  | soaeqo :
      forall o bts1 bts2,
        length bts1 = length bts2
        -> (forall b1 b2,
              LIn (b1,b2) (combine bts1 bts2)
              -> so_alphaeqbt_vs l b1 b2)
        -> so_alphaeq_vs l (soterm o bts1) (soterm o bts2)
with so_alphaeqbt_vs {p} (l : list NVar) : @SOBTerm p -> @SOBTerm p -> Type :=
 | soaeqbt :
     forall vs vs1 vs2 t1 t2,
       length vs = length vs1
       -> length vs = length vs2
       -> disjoint vs (l ++ vs1 ++ vs2 ++ all_fo_vars t1 ++ all_fo_vars t2)
       -> no_repeats vs
       -> so_alphaeq_vs l (so_swap (mk_swapping vs1 vs) t1) (so_swap (mk_swapping vs2 vs) t2)
       -> so_alphaeqbt_vs l (sobterm vs1 t1) (sobterm vs2 t2).
Hint Constructors so_alphaeq_vs.
Hint Constructors so_alphaeqbt_vs.

Definition so_alphaeq {p} := @so_alphaeq_vs p [].
Definition so_alphaeqbt {p} := @so_alphaeqbt_vs p [].

Definition alphaeq_sk {o} (sk1 sk2 : @sosub_kind o) :=
  alphaeqbt (sk2bterm sk1) (sk2bterm sk2).

Lemma alphaeq_sk_iff_alphaeq_bterm {o} :
  forall vs1 vs2 (t1 t2 : @NTerm o),
    alphaeqbt (bterm vs1 t1) (bterm vs2 t2)
    <=> alphaeq_sk (sosk vs1 t1) (sosk vs2 t2).
Proof. sp. Qed.

Lemma symm_rel_alphaeq_sk {o} :
  symm_rel (@alphaeq_sk o).
Proof.
  unfold alphaeq_sk, symm_rel; introv h.
  apply alphaeqbt_eq.
  apply alpha_eq_bterm_sym.
  apply alphaeqbt_eq; auto.
Qed.
Hint Immediate symm_rel_alphaeq_sk.

Lemma alphaeq_sk_eq_length {o} :
  forall (a b : @sosub_kind o),
    alphaeq_sk a b -> length (sosk_vs a) = length (sosk_vs b).
Proof.
  introv aeq.
  invertsn aeq; auto.
  destruct a, b; allsimpl; ginv; lia.
Qed.

Definition default_soterm {o} : @SOTerm o := soterm (Can NAxiom) [].
Definition default_sobterm {o} : @SOBTerm o := sobterm [] default_soterm.
Definition default_sk {o} : @sosub_kind o := sosk [] mk_axiom.

Definition bin_rel_sk {p} := binrel_list (@default_sk p).

Lemma binrel_list_sym  :
  forall T (def : T) R,
    symm_rel R
    -> symm_rel (binrel_list def R).
Proof.
  unfold binrel_list; introv sr h; allsimpl; repnd; dands; auto.
  introv k; rw <- h0 in k; apply h in k.
  apply sr; auto.
Qed.

Lemma bin_rel_sk_sym {o} :
  forall R, symm_rel R -> symm_rel (@bin_rel_sk o R).
Proof.
  unfold bin_rel_sk; introv sr h.
  apply binrel_list_sym; auto.
Qed.

Lemma bin_rel_sk_cons {o} :
  forall (sk1 sk2 : @sosub_kind o) sks1 sks2,
    bin_rel_sk alphaeq_sk (sk1 :: sks1) (sk2 :: sks2)
    <=> (bin_rel_sk alphaeq_sk sks1 sks2 # alphaeq_sk sk1 sk2).
Proof.
  introv; unfold bin_rel_sk, binrel_list; simpl.
  split; intro k; repnd; cpx; dands; auto.
  - introv i.
    pose proof (k (S n)) as h; autodimp h hyp; lia.
  - pose proof (k 0) as h; autodimp h hyp; lia.
  - introv i.
    destruct n; cpx.
Qed.

Lemma alphaeq_sosub_kind_if_alphaeq_sosub_find {o} :
  forall (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk1 sk2 : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk alphaeq_sk sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk1
    -> sosub_find (combine vs sks2) sv = Some sk2
    -> alphaeq_sk sk1 sk2.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  apply binrel_list_cons in aeq; repnd.
  fold (@bin_rel_sk o) in aeq0.
  applydup @alphaeq_sk_eq_length in aeq; allsimpl.

  destruct s; destruct s0; boolvar; allsimpl; cpx;
  try (complete (provefalse; apply n1; sp)).

  apply IHvs with (sks1 := sks1) (sks2 := sks2) (sv := sv); auto.
Qed.

Lemma false_if_alphaeq_sosub_find {o} :
  forall (vs : list NVar) (sks1 sks2 : list (@sosub_kind o)) (sk : sosub_kind) (sv : sovar_sig),
    length vs = length sks1
    -> length vs = length sks2
    -> bin_rel_sk alphaeq_sk sks1 sks2
    -> sosub_find (combine vs sks1) sv = Some sk
    -> sosub_find (combine vs sks2) sv = None
    -> False.
Proof.
  induction vs; introv len1 len2 aeq f1 f2; allsimpl; cpx.
  destruct sks1; destruct sks2; allsimpl; cpx.
  apply binrel_list_cons in aeq; repnd.
  fold (@bin_rel_sk o) in aeq0.
  applydup @alphaeq_sk_eq_length in aeq; allsimpl.

  destruct s; destruct s0; boolvar; allsimpl; cpx;
  try (complete (provefalse; apply n1; sp)).

  eapply IHvs in f1; eauto.
Qed.

Lemma alphaeq_apply_list {o} :
  forall ts1 ts2 (t1 t2 : @NTerm o),
    alphaeq t1 t2
    -> bin_rel_nterm alpha_eq ts1 ts2
    -> alphaeq (apply_list t1 ts1) (apply_list t2 ts2).
Proof.
  induction ts1; introv aeq brel; destruct ts2; allsimpl; tcsp.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - unfold bin_rel_nterm, binrel_list in brel; repnd; allsimpl; cpx.
  - apply binrel_list_cons in brel; repnd.
    apply IHts1; auto.
    apply alphaeq_eq.
    apply alphaeq_eq in aeq.
    prove_alpha_eq4.
    introv h; destruct n0.
    + apply alphaeqbt_nilv2; auto.
    + destruct n0; sp.
      apply alphaeqbt_nilv2; auto.
Qed.

Lemma sosize_so_swap {p} :
  forall (t : @SOTerm p) l,
    sosize (so_swap l t) = sosize t.
Proof.
  soterm_ind1 t as [v ts Hind | o bts Hind] Case; introv; simpl; auto; tcsp.
  - boolvar; subst; simpl; auto.
    f_equal; f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    apply Hind; sp.
  - f_equal; f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    eapply Hind; eauto.
Qed.

Lemma sosize_so_swap_le {o} :
  forall (t : @SOTerm o) sw,
    sosize (so_swap sw t) <= sosize t.
Proof.
  introv; rw @sosize_so_swap; sp.
Qed.

Lemma disjoint_all_fo_vars_so_swap {p} :
  forall (t : @SOTerm p) vs vs1 vs2,
    length vs1 = length vs2
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs (all_fo_vars t)
    -> disjoint vs (all_fo_vars (so_swap (mk_swapping vs1 vs2) t)).
Proof.
  soterm_ind1s t as [v ts Hind | o lbt Hind] Case;
  introv len disj1 disj2 disj3; allsimpl; tcsp.

  - Case "sovar".
    boolvar; subst; simpl.
    + allrw disjoint_cons_r; repnd; dands; auto.
      intro k; apply in_swapvar_disj_iff2 in k; auto.
    + allsimpl; allrw disjoint_cons_r; repnd.
      dands; auto.
      rw flat_map_map; unfold compose.
      allrw disjoint_flat_map_r; introv i.
      eapply Hind; eauto.

  - Case "soterm".
    rw flat_map_map.
    rw disjoint_flat_map_r in disj3.
    apply disjoint_flat_map_r; introv i.
    applydup disj3 in i as d.
    destruct x; unfold compose; allsimpl.
    allrw disjoint_app_r; repnd.
    dands; try (complete (eapply Hind; eauto)).
    apply disjoint_swapbvars; auto.
Qed.

Lemma so_swap_so_swap {p} :
  forall s1 s2 (t : @SOTerm p),
    so_swap s1 (so_swap s2 t) = so_swap (s2 ++ s1) t.
Proof.
  soterm_ind1 t as [v ts Hind | o lbt Hind] Case; simpl; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; boolvar; allsimpl; auto; tcsp;
    try (complete (rw swapvar_swapvar; auto));
    try (complete (destruct ts; allsimpl; tcsp)).
    f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    apply Hind; auto.

  - Case "soterm".
    f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    apply Hind in i.
    rw i.
    rw swapbvars_swapbvars; auto.
Qed.

Lemma so_swap_app_so_swap {p} :
  forall (t : @SOTerm p) vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> length vs2 = length vs4
    -> no_repeats vs3
    -> no_repeats vs4
    -> disjoint vs3 vs1
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs3 (all_fo_vars t)
    -> disjoint vs4 (all_fo_vars t)
    -> disjoint vs2 vs4
    -> disjoint vs1 vs4
    -> so_swap (mk_swapping (vs1 ++ vs2) (vs3 ++ vs4)) t
       = so_swap
           (mk_swapping (vs2 ++ swapbvars (mk_swapping vs2 vs4) vs1)
                        (vs4 ++ vs3))
           t.
Proof.
  soterm_ind1s t as [v ts Hind | o lbt Hind] Case;
  introv len1 len2 norep2 norep3;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  tcsp.

  - Case "sovar".
    allsimpl; boolvar; subst; allsimpl.
    + allrw disjoint_singleton_r; repnd.
      rw swapvar_app_swap; auto.
    + allrw disjoint_cons_r; repnd.
      allrw disjoint_flat_map_r.
      apply f_equal.
      apply eq_maps; introv i.
      apply Hind; auto.

  - Case "soterm".
    simpl.
    f_equal.
    apply eq_maps; introv i.
    destruct x; simpl.
    allsimpl.
    allrw disjoint_flat_map_r.
    applydup disj4 in i as d1.
    applydup disj5 in i as d2.
    allsimpl; allrw disjoint_app_r; repnd.

    rw <- swapbvars_app_swap; auto.

    f_equal.
    eapply Hind; eauto.
Qed.

Lemma so_alphaeq_add_so_swap {p} :
  forall vs vs1 vs2 (t1 t2 : @SOTerm p),
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs2 (vs1 ++ all_fo_vars t1 ++ all_fo_vars t2)
    -> so_alphaeq_vs (vs1 ++ vs2 ++ vs) t1 t2
    -> so_alphaeq_vs
         (vs1 ++ vs2 ++ vs)
         (so_swap (mk_swapping vs1 vs2) t1)
         (so_swap (mk_swapping vs1 vs2) t2).
Proof.
  soterm_ind1s t1 as [v1 ts1 Hind | o1 lbt1 Hind] Case; introv len norep2 disj aeq; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? e imp| ]; clear aeq; subst; allsimpl; auto.
    boolvar; subst; allsimpl; tcsp;
    try (complete (destruct ts2; allsimpl; cpx));
    try (complete (destruct ts1; allsimpl; cpx)).
    constructor; [allrw map_length; complete auto|].
    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; cpx; allsimpl.
    applydup in_combine in i1; repnd.
    apply Hind; auto.
    repeat (first [ progress (allrw disjoint_app_r)
                  | progress (allrw disjoint_cons_r)
                  | progress (allrw disjoint_flat_map_r)
           ]); repnd.
    dands; auto.

  - Case "soterm".
    allsimpl.
    inversion aeq as [| ? ? ? eqlens aeqbts e1 oeq]; subst; clear aeq.
    allsimpl.
    apply soaeqo; allrw map_length; auto.
    introv lt.
    rw <- @map_combine in lt; rw in_map_iff in lt; exrepnd; cpx; allsimpl.
    applydup aeqbts in lt1 as aeq; repnd.
    destruct a0 as [bvs1 t1].
    destruct a  as [bvs2 t2].
    allsimpl.
    applydup in_combine in lt1; repnd.
    inversion aeq as [? ? ? ? ? leneq1 leneq2 d n a]; subst; clear aeq.
    allrw disjoint_app_r; repnd.
    allrw disjoint_flat_map_r.
    applydup disj1 in lt2.
    applydup disj in lt0.
    allsimpl; allrw disjoint_app_r; repnd.

    eapply Hind in a; eauto; allrw @sosize_so_swap; auto;
    try (complete (allrw disjoint_app_r; dands; auto;
                   apply disjoint_all_fo_vars_so_swap; auto;
                   try (apply disjoint_sym; auto))).

    repeat (rw @so_swap_so_swap in a).
    repeat (rw mk_swapping_app in a; auto).

    apply @soaeqbt with (vs := vs0); auto;
    try (complete (rw length_swapbvars; lia)).

    allrw disjoint_app_r; repnd.
    pose proof (disjoint_swapbvars bvs1 vs0 vs1 vs2) as h1;
      repeat (autodimp h1 hyp); try lia.
    pose proof (disjoint_swapbvars bvs2 vs0 vs1 vs2) as h2;
      repeat (autodimp h2 hyp); try lia.
    pose proof (disjoint_all_fo_vars_so_swap t1 vs0 vs1 vs2) as h3;
      repeat (autodimp h3 hyp); try lia.
    pose proof (disjoint_all_fo_vars_so_swap t2 vs0 vs1 vs2) as h4;
      repeat (autodimp h4 hyp); try lia.

    allrw @so_swap_so_swap.
    repeat (rw mk_swapping_app;[|complete lia]).

    rw <- @so_swap_app_so_swap; auto; try (complete (apply disjoint_sym; auto)).
    rw <- @so_swap_app_so_swap; auto; try (complete (apply disjoint_sym; auto)).
Qed.

Lemma so_swap_disj_chain {p} :
  forall (t : @SOTerm p) vs1 vs vs2,
    length vs = length vs1
    -> length vs = length vs2
    -> no_repeats vs
    -> no_repeats vs2
    -> disjoint vs (vs1 ++ vs2 ++ all_fo_vars t)
    -> disjoint vs2 (vs1 ++ all_fo_vars t)
    -> so_swap (mk_swapping (vs1 ++ vs) (vs ++ vs2)) t
       = so_swap (mk_swapping vs1 vs2) t.
Proof.
  soterm_ind1s t as [v ts Hind | o lbt Hind] Case;
  introv len1 len2 norep1 norep2 disj1 disj2;
  allsimpl; tcsp.

  - Case "sovar".
    allrw disjoint_app_r; allrw disjoint_cons_r; allrw disjoint_flat_map_r; repnd.
    rw swapvar_disj_chain; auto;
    try (complete (allrw disjoint_app_r; allrw disjoint_singleton_r; sp)).
    boolvar; subst; allsimpl; tcsp.
    f_equal.
    apply eq_maps; introv i.
    apply Hind; auto; allrw disjoint_app_r; sp.

  - Case "soterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x; allsimpl.
    allrw disjoint_app_r; repnd.
    allrw disjoint_flat_map_r.
    applydup disj1 in i; applydup disj2 in i; allsimpl.
    allrw disjoint_app_r; repnd.
    erewrite Hind; eauto; allrw disjoint_app_r; auto.
    rw swapbvars_disj_chain; auto; allrw disjoint_app_r; auto.
Qed.

Lemma so_alphaeq_vs_implies_less {p} :
  forall (t1 t2 : @SOTerm p) l1 l2,
    so_alphaeq_vs l1 t1 t2
    -> subvars l2 l1
    -> so_alphaeq_vs l2 t1 t2.
Proof.
  soterm_ind1s t1 as [v1 ts1 Hind | o1 lbt1 Hind] Case; introv aeq sv; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? e imp | ]; clear aeq; subst; auto.
    constructor; auto.
    introv i.
    applydup imp in i.
    apply in_combine in i; repnd.
    eapply Hind; eauto.

  - Case "soterm".
    inversion aeq as [| ? ? ? len aeqbts]; subst; clear aeq.
    constructor; auto.
    introv i.
    applydup aeqbts in i as h.
    destruct b1 as [vs1 t1].
    destruct b2 as [vs2 t2].
    inversion h as [? ? ? ? ? len1 len2 disj norep a]; subst.
    applydup in_combine in i; repnd.

    pose proof (Hind
                  t1
                  (so_swap (mk_swapping vs1 vs) t1)
                  vs1
                  i1) as a1.

    autodimp a1 hyp; try (complete (rw @sosize_so_swap; auto)).

    pose proof (a1 (so_swap (mk_swapping vs2 vs) t2)
                   l1
                   l2
                   a
                   sv) as a2;
      clear a1.

    apply @soaeqbt with (vs := vs); auto; try lia.
    allrw disjoint_app_r; repnd; dands; auto.

    unfold disjoint; introv x y.
    rw subvars_prop in sv.
    apply disj0 in x.
    apply sv in y; auto.
Qed.

Lemma so_alphaeq_implies_alphaeq_vs {p} :
  forall t1 t2 : @SOTerm p, so_alphaeq t1 t2 -> forall l, so_alphaeq_vs l t1 t2.
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1 | o1 lbt1 ind1] Case; introv aeq; introv; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? len imp |]; clear aeq; subst; auto.
    constructor; auto.
    introv i.
    applydup imp in i.
    apply ind1; auto.
    apply in_combine in i; sp.

  - Case "soterm".
    inversion aeq as [| ? ? ? len aeqbts]; subst; clear aeq.
    constructor; auto.
    introv i.
    applydup aeqbts in i as h.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    inversion h as [? ? ? ? ? len1 len2 disj norep a]; subst.

    pose proof (fresh_vars (length vs)
                           (l ++ vs
                              ++ l1
                              ++ l2
                              ++ all_fo_vars t1
                              ++ all_fo_vars t2))
      as Hfresh.
    destruct Hfresh as [l' d]; repnd.

    apply @soaeqbt with (vs := l'); auto; try lia.
    allrw disjoint_app_r; sp.

    applydup in_combine in i; repnd.
    pose proof (ind1
                  t1
                  (so_swap (mk_swapping l1 vs) t1)
                  l1
                  i1) as a1.

    autodimp a1 hyp.
    rw @sosize_so_swap; auto.

    pose proof (a1 (so_swap (mk_swapping l2 vs) t2)
                   a
                   (vs ++ l' ++ l)) as a2;
      clear a1.

    allsimpl.

    assert (disjoint l' vs) as disj1 by (allrw disjoint_app_r; sp).
    assert (disjoint l' (all_fo_vars (so_swap (mk_swapping l1 vs) t1)))
      as disj2 by (allrw disjoint_app_r; repnd;
                   apply disjoint_all_fo_vars_so_swap; auto).
    assert (disjoint l' (all_fo_vars (so_swap (mk_swapping l2 vs) t2)))
      as disj3 by (allrw disjoint_app_r; repnd;
                   apply disjoint_all_fo_vars_so_swap; auto).

    applydup @so_alphaeq_add_so_swap in a2; auto;
    try (complete (allrw disjoint_app_r; auto)).

    allrw @so_swap_so_swap.
    repeat (rw mk_swapping_app in a0; try lia).

    rw @so_swap_disj_chain in a0; auto;
    try (complete (allrw disjoint_app_r; sp; try (complete (apply disjoint_sym; auto)))).

    rw @so_swap_disj_chain in a0; auto;
    try (complete (allrw disjoint_app_r; sp; try (complete (apply disjoint_sym; auto)))).

    apply @so_alphaeq_vs_implies_less with (l1 := vs ++ l' ++ l); auto.
    rw app_assoc; apply subvars_app_trivial_r.
Qed.

Lemma so_alphaeq_vs_implies_more {p} :
  forall (t1 t2 : @SOTerm p) l1 l2,
    so_alphaeq_vs l1 t1 t2
    -> subvars l1 l2
    -> so_alphaeq_vs l2 t1 t2.
Proof.
  introv aeq sv.
  apply @so_alphaeq_vs_implies_less with (l2 := []) in aeq; auto.
  apply so_alphaeq_implies_alphaeq_vs; auto.
Qed.

Lemma so_alphaeq_all {p} :
  forall t1 t2 : @SOTerm p, so_alphaeq t1 t2 <=> (forall l, so_alphaeq_vs l t1 t2).
Proof.
  introv; split; intro k.
  - introv; apply so_alphaeq_implies_alphaeq_vs; auto.
  - pose proof (k []); auto.
Qed.

Lemma so_alphaeq_exists {p} :
  forall t1 t2 : @SOTerm p, so_alphaeq t1 t2 <=> {l : list NVar & so_alphaeq_vs l t1 t2}.
Proof.
  introv; split; intro k.
  - exists ([] : list NVar); auto.
  - exrepnd; apply so_alphaeq_vs_implies_less with (l1 := l); auto.
Qed.

Lemma so_alphaeqbt_vs_implies_more {p} :
  forall (t1 t2 : @SOBTerm p) l1 l2,
    so_alphaeqbt_vs l1 t1 t2
    -> subvars l1 l2
    -> so_alphaeqbt_vs l2 t1 t2.
Proof.
  introv aeq sv.
  pose proof (so_alphaeq_vs_implies_more (soterm Exc [t1]) (soterm Exc [t2]) l1 l2) as h.
  autodimp h hyp.
  - constructor; simpl; auto.
    introv k; sp; cpx.
  - autodimp h hyp.
    inversion h as [ |? ? ? ? imp]; subst; allsimpl; GC.
    apply imp; sp.
Qed.

Definition swap_sub {o} (sw : swapping) (sub : @Sub o) : Sub :=
  map (fun x =>
         match x with
           | (v,t) => (swapvar sw v,swap sw t)
         end)
      sub.

Definition cswap_sub {o} (sw : swapping) (sub : @Sub o) : Sub :=
  map (fun x =>
         match x with
           | (v,t) => (swapvar sw v,cswap sw t)
         end)
      sub.

Lemma sub_find_some_implies_swap {o} :
  forall (sub : @Sub o) v t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_find sub v = Some t
    -> sub_find
         (swap_sub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v)
       = Some (swap (mk_swapping vs1 vs2) t).
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
  provefalse.
  destruct Heqb0.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sub_find_some_implies_cswap {o} :
  forall (sub : @Sub o) v t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_find sub v = Some t
    -> sub_find
         (cswap_sub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v)
       = Some (cswap (mk_swapping vs1 vs2) t).
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
  provefalse.
  destruct Heqb0.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sub_find_none_implies_swap {o} :
  forall (sub : @Sub o) v vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_find sub v = None
    -> sub_find
         (swap_sub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v)
       = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
  provefalse.
  destruct Heqb0.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sub_find_none_implies_cswap {o} :
  forall (sub : @Sub o) v vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_find sub v = None
    -> sub_find
         (cswap_sub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v)
       = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
  provefalse.
  destruct Heqb0.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sub_filter_swap_sub {o} :
  forall (sub : @Sub o) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_filter
         (swap_sub (mk_swapping vs1 vs2) sub)
         (swapbvars (mk_swapping vs1 vs2) vs)
       = swap_sub (mk_swapping vs1 vs2) (sub_filter sub vs).
Proof.
  induction sub; introv norep disj; simpl; auto.
  destruct a; boolvar; simpl; tcsp.
  - provefalse.
    apply in_swapbvars in Heqb; exrepnd.
    apply swapvars_eq in Heqb1; auto; subst; tcsp.
  - provefalse.
    rw in_swapbvars in Heqb.
    destruct Heqb.
    eexists; dands; eauto.
  - apply eq_cons; auto.
Qed.

Lemma sub_filter_cswap_sub {o} :
  forall (sub : @Sub o) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sub_filter
         (cswap_sub (mk_swapping vs1 vs2) sub)
         (swapbvars (mk_swapping vs1 vs2) vs)
       = cswap_sub (mk_swapping vs1 vs2) (sub_filter sub vs).
Proof.
  induction sub; introv norep disj; simpl; auto.
  destruct a; boolvar; simpl; tcsp.
  - provefalse.
    apply in_swapbvars in Heqb; exrepnd.
    apply swapvars_eq in Heqb1; auto; subst; tcsp.
  - provefalse.
    rw in_swapbvars in Heqb.
    destruct Heqb.
    eexists; dands; eauto.
  - apply eq_cons; auto.
Qed.

Lemma swap_sub_combine {o} :
  forall (ts : list (@NTerm o)) vs vs1 vs2,
    swap_sub (mk_swapping vs1 vs2) (combine vs ts)
    = combine (swapbvars (mk_swapping vs1 vs2) vs)
              (map (swap (mk_swapping vs1 vs2)) ts).
Proof.
  induction ts; destruct vs; introv; simpl; auto.
  apply eq_cons; auto.
Qed.

Lemma cswap_sub_combine {o} :
  forall (ts : list (@NTerm o)) vs vs1 vs2,
    cswap_sub (mk_swapping vs1 vs2) (combine vs ts)
    = combine (swapbvars (mk_swapping vs1 vs2) vs)
              (map (cswap (mk_swapping vs1 vs2)) ts).
Proof.
  induction ts; destruct vs; introv; simpl; auto.
  apply eq_cons; auto.
Qed.

Lemma lsubst_aux_swap_swap {o} :
  forall (t : @NTerm o) vs1 vs2 sub,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> swap (mk_swapping vs1 vs2) (lsubst_aux t sub)
       = lsubst_aux
           (swap (mk_swapping vs1 vs2) t)
           (swap_sub (mk_swapping vs1 vs2) sub).
Proof.
  nterm_ind1 t as [v|op bts Hind] Case; introv norep disj; simpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as p; destruct p; symmetry in Heqp.

    + apply (sub_find_some_implies_swap sub v n vs1 vs2) in Heqp; auto.
      rw Heqp; auto.

    + apply (sub_find_none_implies_swap sub v vs1 vs2) in Heqp; auto.
      rw Heqp; auto.

  - Case "oterm".
    f_equal.
    repeat (rw map_map); unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    rw @sub_filter_swap_sub; auto.
    eapply Hind; eauto.
Qed.

Lemma lsubst_aux_cswap_cswap {o} :
  forall (t : @NTerm o) vs1 vs2 sub,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> cswap (mk_swapping vs1 vs2) (lsubst_aux t sub)
       = lsubst_aux
           (cswap (mk_swapping vs1 vs2) t)
           (cswap_sub (mk_swapping vs1 vs2) sub).
Proof.
  nterm_ind1 t as [v|op bts Hind] Case; introv norep disj; simpl; auto.

  - Case "vterm".
    remember (sub_find sub v) as p; destruct p; symmetry in Heqp.

    + apply (sub_find_some_implies_cswap sub v n vs1 vs2) in Heqp; auto.
      rw Heqp; auto.

    + apply (sub_find_none_implies_cswap sub v vs1 vs2) in Heqp; auto.
      rw Heqp; auto.

  - Case "oterm".
    f_equal.
    repeat (rw map_map); unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    rw @sub_filter_cswap_sub; auto.
    eapply Hind; eauto.
Qed.

Definition swapsk {o} (sw : swapping) (sk : @sosub_kind o) : sosub_kind :=
  match sk with
    | sosk vs t => sosk (swapbvars sw vs) (swap sw t)
  end.

Definition cswapsk {o} (sw : swapping) (sk : @sosub_kind o) : sosub_kind :=
  match sk with
    | sosk vs t => sosk (swapbvars sw vs) (cswap sw t)
  end.

Definition swap_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) =>
             (if bnull (sosk_vs sk) then swapvar sw v else v,swapsk sw sk)
         end)
      sub.

Definition cswap_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) =>
             (if bnull (sosk_vs sk) then swapvar sw v else v,cswapsk sw sk)
         end)
      sub.

Definition swap_all_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) => (swapvar sw v,swapsk sw sk)
         end)
      sub.

Definition cswap_all_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) => (swapvar sw v,cswapsk sw sk)
         end)
      sub.

Definition swap_range_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) => (v,swapsk sw sk)
         end)
      sub.

Definition cswap_range_sosub {o} (sw : swapping) (sub : @SOSub o) : SOSub :=
  map (fun x =>
         match x with
           | (v,sk) => (v,cswapsk sw sk)
         end)
      sub.


Lemma sosub_find_some_implies_swap_0 {o} :
  forall (sub : @SOSub o) v t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,0) = Some (sosk [] t)
    -> sosub_find
         (swap_sosub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v, 0)
       = Some (sosk [] (swap (mk_swapping vs1 vs2) t)).
Proof.
  Opaque sovar_sig_dec.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; try subst; simpl in *; cpx;
    ginv; tcsp;
      allrw length_swapbvars; allsimpl; tcsp; GC;
        try (complete (destruct l; allsimpl; cpx)).
  provefalse; destruct n1.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_find_some_implies_cswap_0 {o} :
  forall (sub : @SOSub o) v t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,0) = Some (sosk [] t)
    -> sosub_find
         (cswap_sosub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v, 0)
       = Some (sosk [] (cswap (mk_swapping vs1 vs2) t)).
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; allsimpl; tcsp; GC;
  try (complete (destruct l; allsimpl; cpx)).
  provefalse; destruct n1.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_find_some_implies_swap_S {o} :
  forall (sub : @SOSub o) v n vs t vs1 vs2,
    n > 0
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = Some (sosk vs t)
    -> sosub_find (swap_sosub (mk_swapping vs1 vs2) sub) (v, n)
       = Some (sosk (swapbvars (mk_swapping vs1 vs2) vs)
                    (swap (mk_swapping vs1 vs2) t)).
Proof.
  induction sub; introv gt norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; allsimpl; tcsp; inversion gt.
Qed.

Lemma sosub_find_some_implies_cswap_S {o} :
  forall (sub : @SOSub o) v n vs t vs1 vs2,
    n > 0
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = Some (sosk vs t)
    -> sosub_find (cswap_sosub (mk_swapping vs1 vs2) sub) (v, n)
       = Some (sosk (swapbvars (mk_swapping vs1 vs2) vs)
                    (cswap (mk_swapping vs1 vs2) t)).
Proof.
  induction sub; introv gt norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; allsimpl; tcsp; inversion gt.
Qed.

Lemma sosub_find_some_implies_swap_all {o} :
  forall (sub : @SOSub o) v n vs t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = Some (sosk vs t)
    -> sosub_find (swap_all_sosub (mk_swapping vs1 vs2) sub)
                  (swapvar (mk_swapping vs1 vs2) v, n)
       = Some (sosk (swapbvars (mk_swapping vs1 vs2) vs)
                    (swap (mk_swapping vs1 vs2) t)).
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; allsimpl; tcsp.
  provefalse; destruct n2.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_find_none_implies_swap_0 {o} :
  forall (sub : @SOSub o) v vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,0) = None
    -> sosub_find
         (swap_sosub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v, 0)
       = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp; allsimpl; GC;
  try (complete (destruct l; allsimpl; cpx)).
  provefalse; destruct n1.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_find_none_implies_cswap_0 {o} :
  forall (sub : @SOSub o) v vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,0) = None
    -> sosub_find
         (cswap_sosub (mk_swapping vs1 vs2) sub)
         (swapvar (mk_swapping vs1 vs2) v, 0)
       = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp; allsimpl; GC;
  try (complete (destruct l; allsimpl; cpx)).
  provefalse; destruct n1.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_find_none_implies_swap_S {o} :
  forall (sub : @SOSub o) v n vs1 vs2,
    n > 0
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = None
    -> sosub_find (swap_sosub (mk_swapping vs1 vs2) sub) (v, n) = None.
Proof.
  induction sub; introv gt norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp; allsimpl; inversion gt.
Qed.

Lemma sosub_find_none_implies_swap_all {o} :
  forall (sub : @SOSub o) v n vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = None
    -> sosub_find (swap_all_sosub (mk_swapping vs1 vs2) sub)
                  (swapvar (mk_swapping vs1 vs2) v, n)
       = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp; allsimpl.
  provefalse; destruct n2.
  f_equal.
  eapply swapvars_eq; [|idtac|complete eauto]; auto.
Qed.

Lemma sosub_filter_swap_sosub {o} :
  forall (sub : @SOSub o) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_filter
         (swap_sosub (mk_swapping vs1 vs2) sub)
         (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs))
       = swap_sosub (mk_swapping vs1 vs2) (sosub_filter sub (vars2sovars vs)).
Proof.
  induction sub; introv norep disj; simpl; auto.
  destruct a; destruct s; simpl;
  repeat (progress (boolvar; try (subst); allsimpl)); tcsp; GC.
  - provefalse.
    allrw in_map_iff; exrepnd; allunfold var2sovar; cpx.
    rw in_swapbvars in l0; exrepnd.
    apply swapvars_eq in l1; auto; subst; tcsp.
    destruct n1; eexists; dands; eauto.
  - provefalse.
    allrw in_map_iff; exrepnd; allunfold var2sovar; cpx.
    allrw length_swapbvars; destruct l; allsimpl; cpx.
  - provefalse.
    allrw in_map_iff; exrepnd.
    allunfold var2sovar; cpx.
    destruct n1; eexists; dands; eauto.
    rw in_swapbvars; eexists; eauto.
  - provefalse.
    allrw in_map_iff; exrepnd.
    allunfold var2sovar; cpx.
    destruct l; cpx.
  - apply eq_cons; auto.
  - apply eq_cons; auto.
Qed.

Lemma sosub_filter_cswap_sosub {o} :
  forall (sub : @SOSub o) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_filter
         (cswap_sosub (mk_swapping vs1 vs2) sub)
         (vars2sovars (swapbvars (mk_swapping vs1 vs2) vs))
       = cswap_sosub (mk_swapping vs1 vs2) (sosub_filter sub (vars2sovars vs)).
Proof.
  induction sub; introv norep disj; simpl; auto.
  destruct a; destruct s; simpl;
  repeat (progress (boolvar; try (subst); allsimpl)); tcsp; GC.
  - provefalse.
    allrw in_map_iff; exrepnd; allunfold var2sovar; cpx.
    rw in_swapbvars in l0; exrepnd.
    apply swapvars_eq in l1; auto; subst; tcsp.
    destruct n1; eexists; dands; eauto.
  - provefalse.
    allrw in_map_iff; exrepnd; allunfold var2sovar; cpx.
    allrw length_swapbvars; destruct l; allsimpl; cpx.
  - provefalse.
    allrw in_map_iff; exrepnd.
    allunfold var2sovar; cpx.
    destruct n1; eexists; dands; eauto.
    rw in_swapbvars; eexists; eauto.
  - provefalse.
    allrw in_map_iff; exrepnd.
    allunfold var2sovar; cpx.
    destruct l; cpx.
  - apply eq_cons; auto.
  - apply eq_cons; auto.
Qed.

Fixpoint filter_out_fo_vars (l : list sovar_sig) : list sovar_sig :=
  match l with
    | [] => []
    | (v,0) :: vs => filter_out_fo_vars vs
    | (v,S n) :: vs => (v,S n) :: filter_out_fo_vars vs
  end.

Lemma subsovars_filter_out_fo_vars :
  forall l, subsovars (filter_out_fo_vars l) l.
Proof.
  induction l; simpl; auto.
  destruct a; destruct n0; auto.
  - apply subsovars_cons_weak_r; auto.
  - apply subsovars_cons_lr; auto.
Qed.

Lemma in_filter_out_fo_vars :
  forall v n l,
    n > 0
    -> (LIn (v, n) (filter_out_fo_vars l) <=> LIn (v, n) l).
Proof.
  induction l; introv k; split; intro i; allsimpl; tcsp;
  destruct a; destruct n1; tcsp.
  - apply IHl in i; auto.
  - simpl in i; dorn i; cpx.
    apply IHl in i; auto.
  - dorn i; cpx; try lia.
    apply IHl; auto.
  - dorn i; cpx; simpl.
    right; apply IHl; auto.
Qed.

Lemma in_filter_out_fo_vars2 :
  forall v n l,
    LIn (v, S n) (filter_out_fo_vars l) <=> LIn (v, S n) l.
Proof.
  introv; apply in_filter_out_fo_vars; lia.
Qed.

Lemma filter_out_fo_vars_app :
  forall l1 l2,
    filter_out_fo_vars (l1 ++ l2)
    = filter_out_fo_vars l1 ++ filter_out_fo_vars l2.
Proof.
  induction l1; introv; simpl; auto.
  destruct a; destruct n0; auto.
  apply eq_cons; auto.
Qed.

Lemma filter_out_fo_vars_flat_map :
  forall {A} (x : A) f l,
    LIn x l
    -> subsovars (filter_out_fo_vars (f x)) (filter_out_fo_vars (flat_map f l)).
Proof.
  induction l; introv i; allsimpl; tcsp.
  dorn i; subst; auto; rw filter_out_fo_vars_app.
  - apply subsovars_app_weak_r1; auto.
  - apply subsovars_app_weak_r2; auto.
Qed.

Lemma subvars_filter_out_fo_vars_flat_map :
  forall {A} f (l : list A) vs,
    subsovars (filter_out_fo_vars (flat_map f l)) vs
    <=> (forall x, LIn x l -> subsovars (filter_out_fo_vars (f x)) vs).
Proof.
  induction l; introv; split; introv k; allsimpl; tcsp.
  - rw filter_out_fo_vars_app in k; rw subsovars_app_l in k; repnd.
    introv i; dorn i; subst; tcsp.
    rw IHl in k; apply k; auto.
  - rw filter_out_fo_vars_app; rw subsovars_app_l; dands; auto.
    rw IHl; introv i.
    apply k; sp.
Qed.

Definition cover_so_vars {o} (t : @SOTerm o) (sub : @SOSub o) :=
  subsovars
    (filter_out_fo_vars (so_free_vars t))
    (filter_out_fo_vars (sodom sub)).

Lemma cover_so_vars_sovar {o} :
  forall v (ts : list (@SOTerm o)) sub,
    cover_so_vars (sovar v ts) sub
    <=>
    ((!null ts -> LIn (v,length ts) (sodom sub))
     # (forall t, LIn t ts -> cover_so_vars t sub)).
Proof.
  introv; unfold cover_so_vars; simpl; boolvar;
  destruct ts; allsimpl; cpx; allsimpl; GC.
  - rw null_nil_iff.
    split; intro k; repnd; dands; tcsp.
  - rw subsovars_cons_l; split; intro k; repnd; dands; auto.
    + intro h.
      pose proof (subsovars_filter_out_fo_vars (sodom sub)) as sv.
      rw subsovars_prop in sv; apply sv in k0; auto.
    + rw filter_out_fo_vars_app in k.
      rw subsovars_app_l in k; repnd.
      introv i; dorn i; subst; auto.
      pose proof (filter_out_fo_vars_flat_map t so_free_vars ts i) as sv.
      eapply subsovars_trans; [exact sv|]; auto.
    + autodimp k0 hyp.
      apply in_filter_out_fo_vars; auto; lia.
    + rw filter_out_fo_vars_app.
      rw subsovars_app_l; dands; tcsp.
      rw @subvars_filter_out_fo_vars_flat_map; introv i.
      apply k; sp.
Qed.

Lemma filter_out_fo_vars_remove_fo_vars :
  forall fovs sovs,
    filter_out_fo_vars (remove_so_vars (vars2sovars fovs) sovs)
    = filter_out_fo_vars sovs.
Proof.
  induction sovs; simpl.
  - rw remove_so_vars_nil_r; simpl; auto.
  - destruct a; destruct n0; simpl;
    rw remove_so_vars_cons_r; boolvar; simpl; auto.
    + allrw in_map_iff; exrepnd.
      allunfold var2sovar; cpx.
    + apply eq_cons; auto.
Qed.

Lemma cover_so_vars_soterm {o} :
  forall op (bs : list (@SOBTerm o)) sub,
    cover_so_vars (soterm op bs) sub
    <=>
    (forall vs t, LIn (sobterm vs t) bs -> cover_so_vars t sub).
Proof.
  introv; unfold cover_so_vars; simpl; split; intro k.
  - introv i.
    rw @subvars_filter_out_fo_vars_flat_map in k.
    apply k in i; simpl in i.
    rw filter_out_fo_vars_remove_fo_vars in i; auto.
  - rw @subvars_filter_out_fo_vars_flat_map; introv i.
    destruct x; simpl.
    rw filter_out_fo_vars_remove_fo_vars.
    eapply k; eauto.
Qed.

Lemma cover_so_vars_sosub_filter {o} :
  forall (sub : @SOSub o) t vs,
    cover_so_vars t (sosub_filter sub (vars2sovars vs))
    <=> cover_so_vars t sub.
Proof.
  introv; unfold cover_so_vars.
  rw @sodom_sosub_filter.
  rw filter_out_fo_vars_remove_fo_vars; sp.
Qed.

(*
(* vs2 can be disjoint from whatever we want *)
Lemma sosub_aux_swap_swap {p} :
  forall (t : @SOTerm p) vs1 vs2 sub,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> cover_so_vars t sub
    -> swap (mk_swapping vs1 vs2) (sosub_aux sub t)
       = sosub_aux (swap_sosub (mk_swapping vs1 vs2) sub)
                   (so_swap (mk_swapping vs1 vs2) t).
Proof.
  soterm_ind1s t as [v ts ind | o lbt Hind] Case;
  introv norep disj cov; tcsp.

  - Case "sovar".
    simpl.
    remember (sosub_find sub (v,length ts)) as f;
      symmetry in Heqf; destruct f;
      boolvar; subst; allsimpl;
      try (destruct s);
      try (rw map_length).

    + applydup @sosub_find_some in Heqf; repnd.
      destruct l; allsimpl; cpx; GC.
      dup Heqf as e.
      eapply sosub_find_some_implies_swap_0 in e; eauto.
      rw e; clear e; simpl.
      rw @lsubst_aux_swap_swap; auto.

    + dup Heqf as e.
      eapply sosub_find_some_implies_swap_S in e; eauto;
      try (complete (destruct ts; allsimpl; sp; apply gt_Sn_O)).
      rw e; clear e.
      rw @lsubst_aux_swap_swap; auto.
      rw @swap_sub_combine.
      f_equal; f_equal.
      repeat (rw map_map); unfold compose.
      apply eq_maps; introv i.
      apply ind; auto.
      rw @cover_so_vars_sovar in cov; repnd; apply cov; auto.

    + eapply sosub_find_none_implies_swap_0 in Heqf; eauto.
      rw Heqf; clear Heqf; auto.

    + apply sosub_find_none in Heqf.
      rw @cover_so_vars_sovar in cov; repnd.
      autodimp cov0 hyp; tcsp.
      rw null_iff_nil; auto.

  - Case "soterm".
    simpl.
    f_equal.
    repeat (rw map_map); unfold compose; apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    rw @sosub_filter_swap_sosub; auto.
    eapply Hind; eauto.
    rw @cover_so_vars_soterm in cov.
    apply cov in i.
    rw @cover_so_vars_sosub_filter; auto.
Qed.
*)

Lemma sosub_aux_cswap_cswap {p} :
  forall (t : @SOTerm p) vs1 vs2 sub,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> cover_so_vars t sub
    -> cswap (mk_swapping vs1 vs2) (sosub_aux sub t)
       = sosub_aux (cswap_sosub (mk_swapping vs1 vs2) sub)
                   (so_swap (mk_swapping vs1 vs2) t).
Proof.
  soterm_ind1s t as [v ts ind | o lbt Hind] Case;
  introv norep disj cov; tcsp.

  - Case "sovar".
    simpl.
    remember (sosub_find sub (v,length ts)) as f;
      symmetry in Heqf; destruct f;
      boolvar; subst; allsimpl;
      try (destruct s);
      try (rw map_length).

    + applydup @sosub_find_some in Heqf; repnd.
      destruct l; allsimpl; cpx; GC.
      dup Heqf as e.
      eapply sosub_find_some_implies_cswap_0 in e; eauto.
      rw e; clear e; simpl.
      rw @lsubst_aux_cswap_cswap; auto.

    + dup Heqf as e.
      eapply sosub_find_some_implies_cswap_S in e; eauto;
        try (complete (destruct ts; allsimpl; sp; apply Nat.lt_0_succ)).
      rw e; clear e.
      rw @lsubst_aux_cswap_cswap; auto.
      rw @cswap_sub_combine.
      f_equal; f_equal.
      repeat (rw map_map); unfold compose.
      apply eq_maps; introv i.
      apply ind; auto.
      rw @cover_so_vars_sovar in cov; repnd; apply cov; auto.

    + eapply sosub_find_none_implies_cswap_0 in Heqf; eauto.
      rw Heqf; clear Heqf; auto.

    + apply sosub_find_none in Heqf.
      rw @cover_so_vars_sovar in cov; repnd.
      autodimp cov0 hyp; tcsp.
      rw null_iff_nil; auto.

  - Case "soterm".
    simpl.
    f_equal.
    repeat (rw map_map); unfold compose; apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    rw @sosub_filter_cswap_sosub; auto.
    eapply Hind; eauto.
    rw @cover_so_vars_soterm in cov.
    apply cov in i.
    rw @cover_so_vars_sosub_filter; auto.
Qed.

Lemma in_swap_range_sosub_implies {o} :
  forall (sub : @SOSub o) sw v vs t,
    LIn (v,sosk vs t) (swap_range_sosub sw sub)
    -> LIn (v,length vs) (sodom sub).
Proof.
  introv i.
  rw in_map_iff in i; exrepnd; cpx.
  destruct a; allsimpl; ginv.
  rw length_swapbvars.
  eapply in_sodom_if in i1; eauto.
Qed.

Lemma sosub_find_some_implies_swap2 {o} :
  forall (sub : @SOSub o) v n vs t vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = Some (sosk vs t)
    -> sosub_find (swap_range_sosub (mk_swapping vs1 vs2) sub) (v,n)
       = Some (sosk (swapbvars (mk_swapping vs1 vs2) vs)
                    (swap (mk_swapping vs1 vs2) t)).
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
Qed.

Lemma sosub_find_none_implies_swap2 {o} :
  forall (sub : @SOSub o) v n vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> sosub_find sub (v,n) = None
    -> sosub_find (swap_range_sosub (mk_swapping vs1 vs2) sub) (v,n) = None.
Proof.
  induction sub; introv norep disj f; allsimpl; cpx.
  destruct a; destruct s; simpl; boolvar; cpx; ginv; tcsp;
  allrw length_swapbvars; tcsp.
Qed.

Lemma sosub_filter_swap_range_sosub {o} :
  forall (sub : @SOSub o) vs vs1 vs2,
    sosub_filter (swap_range_sosub (mk_swapping vs1 vs2) sub) vs
    = swap_range_sosub (mk_swapping vs1 vs2) (sosub_filter sub vs).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; simpl; boolvar; simpl; tcsp;
  allrw length_swapbvars; tcsp.
  apply eq_cons; auto.
Qed.

Lemma sosub_filter_cswap_range_sosub {o} :
  forall (sub : @SOSub o) vs vs1 vs2,
    sosub_filter (cswap_range_sosub (mk_swapping vs1 vs2) sub) vs
    = cswap_range_sosub (mk_swapping vs1 vs2) (sosub_filter sub vs).
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s; simpl; boolvar; simpl; tcsp;
  allrw length_swapbvars; tcsp.
  apply eq_cons; auto.
Qed.

Lemma swap_range_sosub_eq {o} :
  forall (sub : @SOSub o) vs1 vs2,
    disjoint vs1 (sovars2vars (sodom sub))
    -> disjoint vs2 (sovars2vars (sodom sub))
    -> swap_range_sosub (mk_swapping vs1 vs2) sub
       = swap_sosub (mk_swapping vs1 vs2) sub.
Proof.
  introv disj1 disj2.
  unfold swap_range_sosub, swap_sosub.
  apply eq_maps; introv i.
  destruct x; destruct s.
  boolvar; auto.
  destruct l; allsimpl; cpx; GC.
  allrw disjoint_map_r.
  eapply in_sodom_if in i; eauto.
  applydup disj1 in i.
  applydup disj2 in i.
  allsimpl.
  rw swapvar_not_in; auto.
Qed.

(*
Lemma sosub_aux_swap_swap2 {o} :
  forall (t : @SOTerm o) sub vs1 vs2,
    disjoint vs2 (vs1 ++ sovars2vars (sodom sub))
    -> disjoint vs1 (sovars2vars (sodom sub))
    -> no_repeats vs2
    -> cover_so_vars t sub
    -> swap (mk_swapping vs1 vs2) (sosub_aux sub t)
       = sosub_aux
           (swap_range_sosub (mk_swapping vs1 vs2) sub)
           (so_swap (mk_swapping vs1 vs2) t).
Proof.
  introv disj1 disj2 norep cov.
  allrw disjoint_app_r; repnd.
  rw (sosub_aux_swap_swap t vs1 vs2 sub); eauto with slow.
  f_equal.
  rw @swap_range_sosub_eq; auto.
Qed.
*)

Fixpoint get_fo_vars (l : list sovar_sig) : list NVar :=
  match l with
    | [] => []
    | (v,0) :: vs => v :: get_fo_vars vs
    | _ :: vs => get_fo_vars vs
  end.

Lemma get_fo_vars_app :
  forall vs1 vs2, get_fo_vars (vs1 ++ vs2) = get_fo_vars vs1 ++ get_fo_vars vs2.
Proof.
  induction vs1; introv; simpl; auto.
  destruct a; destruct n0; simpl; auto.
  rw IHvs1; auto.
Qed.

Lemma in_get_fo_vars :
  forall v vs, LIn v (get_fo_vars vs) <=> LIn (v,0) vs.
Proof.
  induction vs; split; introv i; allsimpl; tcsp;
  destruct a; destruct n0; allsimpl; tcsp;
  try (dorn i; subst; cpx);
  try (complete (try right; apply IHvs; auto)).
Qed.

Lemma swap_range_sosub_eq2 {o} :
  forall (sub : @SOSub o) vs1 vs2,
    disjoint vs1 (get_fo_vars (sodom sub))
    -> disjoint vs2 (get_fo_vars (sodom sub))
    -> swap_range_sosub (mk_swapping vs1 vs2) sub
       = swap_sosub (mk_swapping vs1 vs2) sub.
Proof.
  introv disj1 disj2.
  apply eq_maps; introv i.
  destruct x; destruct s.
  boolvar; auto.
  destruct l; allsimpl; cpx; GC.
  eapply in_sodom_if in i; eauto; allsimpl.
  apply in_get_fo_vars in i.
  apply disjoint_sym in disj1.
  apply disjoint_sym in disj2.
  applydup disj1 in i.
  applydup disj2 in i.
  rw swapvar_not_in; auto.
Qed.

Lemma cswap_range_sosub_eq2 {o} :
  forall (sub : @SOSub o) vs1 vs2,
    disjoint vs1 (get_fo_vars (sodom sub))
    -> disjoint vs2 (get_fo_vars (sodom sub))
    -> cswap_range_sosub (mk_swapping vs1 vs2) sub
       = cswap_sosub (mk_swapping vs1 vs2) sub.
Proof.
  introv disj1 disj2.
  apply eq_maps; introv i.
  destruct x; destruct s.
  boolvar; auto.
  destruct l; allsimpl; cpx; GC.
  eapply in_sodom_if in i; eauto; allsimpl.
  apply in_get_fo_vars in i.
  apply disjoint_sym in disj1.
  apply disjoint_sym in disj2.
  applydup disj1 in i.
  applydup disj2 in i.
  rw swapvar_not_in; auto.
Qed.

(*
Lemma sosub_aux_swap_swap3 {o} :
  forall (t : @SOTerm o) sub vs1 vs2,
    disjoint vs2 (vs1 ++ get_fo_vars (sodom sub))
    -> disjoint vs1 (get_fo_vars (sodom sub))
    -> no_repeats vs2
    -> cover_so_vars t sub
    -> swap (mk_swapping vs1 vs2) (sosub_aux sub t)
       = sosub_aux
           (swap_range_sosub (mk_swapping vs1 vs2) sub)
           (so_swap (mk_swapping vs1 vs2) t).
Proof.
  introv disj1 disj2 norep cov.
  allrw disjoint_app_r; repnd.
  rw (sosub_aux_swap_swap t vs1 vs2 sub); eauto with slow.
  f_equal.
  rw @swap_range_sosub_eq2; auto.
Qed.
*)

Lemma sosub_aux_cswap_cswap3 {o} :
  forall (t : @SOTerm o) sub vs1 vs2,
    disjoint vs2 (vs1 ++ get_fo_vars (sodom sub))
    -> disjoint vs1 (get_fo_vars (sodom sub))
    -> no_repeats vs2
    -> cover_so_vars t sub
    -> cswap (mk_swapping vs1 vs2) (sosub_aux sub t)
       = sosub_aux
           (cswap_range_sosub (mk_swapping vs1 vs2) sub)
           (so_swap (mk_swapping vs1 vs2) t).
Proof.
  introv disj1 disj2 norep cov.
  allrw disjoint_app_r; repnd.
  rw (sosub_aux_cswap_cswap t vs1 vs2 sub); eauto with slow.
  f_equal.
  rw @cswap_range_sosub_eq2; auto.
Qed.

(*
Lemma lsubst_aux_alpha_congr2 {p} :
  forall (t1 t2 : @NTerm p) vs1 vs2 ts1 ts2,
    alpha_eq_bterm (bterm vs1 t1) (bterm vs2 t2)
    -> bin_rel_nterm alpha_eq ts1 ts2 (*enforces that the lengths are equal*)
    -> alpha_eq (lsubst_aux t1 (combine vs1 ts1)) (lsubst_aux t2 (combine vs2 ts2)).
Proof.
  introv aeq aeqs.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst.

  introv Hal Hbr Hl. unfold apply_bterm.
  destruct bt1 as [lv1 nt1]. destruct bt2 as [lv2 nt2];allsimpl.
  invertsna Hal Hal.
  remember (change_bvars_alpha (lv++(flat_map free_vars lnt1)) nt1) as X99.
  revert HeqX99. add_changebvar_spec nt1' Hnt1'. intro H99. clear dependent X99.
  repnd. clear Heqnt1'.
  remember (change_bvars_alpha (lv++(flat_map free_vars lnt2)) nt2) as X99.
  revert HeqX99. add_changebvar_spec nt2' Hnt2'. intro H99. clear dependent X99.
  repnd. clear Heqnt2'.
  unfold num_bvars in Hl. allsimpl. duplicate Hbr.
  destruct Hbr as [Hll X99]. clear X99.
  alpharws Hnt1'.
  alpharws Hnt2'.
  alpharwh Hnt1' Hal3.
  alpharwhs Hnt2' Hal3.
  eapply lsubst_alpha_congr with (lvi:=lv) in Hal3; eauto.
  Focus 2. spc;fail. Focus 2. spc;fail.

  rewrite lsubst_nest_same in Hal3; spc; spcls;disjoint_reasoningv.
  - rewrite lsubst_nest_same in Hal3; spc; spcls;disjoint_reasoningv.
    alpharw_rev  Hnt2'. trivial.
  - alpharw_rev  Hnt1'. trivial.
Qed.
*)

Lemma disjoint_bound_vars_prop1 {o} :
  forall (sub : @SOSub o) v vs t ts,
    disjoint (bound_vars_in_sosub sub) (free_vars_sosub sub)
    -> disjoint (bound_vars_in_sosub sub) (flat_map all_fo_vars ts)
    -> LIn (v, sosk vs t) sub
    -> disjoint (bound_vars t) (flat_map (fun x => free_vars (sosub_aux sub x)) ts).
Proof.
  introv disj1 disj2 insub.
  apply disjoint_flat_map_r; introv i.
  allrw disjoint_flat_map_l.
  applydup disj1 in insub; allsimpl.
  applydup disj2 in insub; allsimpl.
  pose proof (isprogram_sosub_aux_free_vars x sub) as h.
  eapply subvars_disjoint_r;[eauto|]; clear h.
  rw disjoint_app_r; dands; auto.
  apply disjoint_map_r; introv k.
  rw in_remove_so_vars in k; repnd.
  destruct x0; simpl.
  apply so_free_vars_in_all_fo_vars in k0.
  rw disjoint_flat_map_r in insub1.
  apply insub1 in i.
  apply disjoint_sym in i.
  apply i in k0; auto.
Qed.

(*
Lemma swap_sosub_combine {o} :
  forall sw (sks : list (@sosub_kind o)) vs,
    swap_sosub sw (combine vs sks)
    = combine (swapbvars sw vs) (map (swapsk sw) sks).
Proof.
  induction sks; destruct vs; allsimpl; auto.
  apply eq_cons; auto.
Qed.
*)

Lemma swap_range_sosub_combine {o} :
  forall sw (sks : list (@sosub_kind o)) vs,
    swap_range_sosub sw (combine vs sks)
    = combine vs (map (swapsk sw) sks).
Proof.
  induction sks; destruct vs; allsimpl; auto.
  apply eq_cons; auto.
Qed.

Lemma cswap_range_sosub_combine {o} :
  forall sw (sks : list (@sosub_kind o)) vs,
    cswap_range_sosub sw (combine vs sks)
    = combine vs (map (cswapsk sw) sks).
Proof.
  induction sks; destruct vs; allsimpl; auto.
  apply eq_cons; auto.
Qed.

Lemma get_fo_vars_remove_so_vars :
  forall fovs sovs,
    get_fo_vars (remove_so_vars (vars2sovars fovs) sovs)
    = remove_nvars fovs (get_fo_vars sovs).
Proof.
  induction sovs; simpl.
  - rw remove_so_vars_nil_r.
    rw remove_nvars_nil_r; auto.
  - rw remove_so_vars_cons_r.
    destruct a; destruct n0; boolvar; tcsp;
    rw remove_nvars_cons_r; boolvar; simpl; tcsp.
    + allrw in_map_iff; exrepnd.
      allunfold var2sovar; cpx.
    + allrw in_map_iff; exrepnd.
      allunfold var2sovar; cpx.
      provefalse; destruct n0.
      eexists; eauto.
    + apply eq_cons; auto.
Qed.

Lemma disjoint_get_fo_vars_remove :
  forall fovs sovs,
    disjoint fovs (get_fo_vars (remove_so_vars (vars2sovars fovs) sovs)).
Proof.
  introv.
  rw get_fo_vars_remove_so_vars.
  introv i j.
  rw in_remove_nvars in j; sp.
Qed.

Lemma subvars_sovars2vars_prop2 :
  forall vs1 vs2,
    subsovars vs1 vs2
    -> subvars (get_fo_vars vs1) (sovars2vars vs2).
Proof.
  introv k.
  rw subvars_prop; introv i.
  allrw in_sovars2vars; exrepnd.
  allrw in_get_fo_vars.
  rw subsovars_prop in k.
  apply k in i.
  eexists; eauto.
Qed.

Lemma alphaeq_sks_implies_eq_sodom_combine {o} :
  forall (sks1 sks2 : list (@sosub_kind o)) vs,
    bin_rel_sk alphaeq_sk sks1 sks2
    -> sodom (combine vs sks1) = sodom (combine vs sks2).
Proof.
  induction sks1; destruct sks2; introv aeqs; allsimpl; auto.
  - inversion aeqs; allsimpl; sp.
  - inversion aeqs; allsimpl; sp.
  - destruct vs; allsimpl; auto.
    destruct a; destruct s.
    rw @bin_rel_sk_cons in aeqs; repnd.
    erewrite IHsks1; eauto.
    inversion aeqs; subst.
    apply eq_cons; auto.
    f_equal; lia.
Qed.

Lemma swapvar_implies3 :
  forall (vs1 vs2 : list NVar) (v : NVar),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> length vs1 = length vs2
    -> LIn v vs1
    -> LIn (swapvar (mk_swapping vs1 vs2) v) vs2.
Proof.
  induction vs1; destruct vs2; introv norep disj len i; allsimpl; cpx; GC; tcsp.
  allrw no_repeats_cons; repnd.
  allrw disjoint_cons_l; allrw disjoint_cons_r; allsimpl.
  allrw not_over_or; repnd.
  unfold oneswapvar; boolvar; dorn i; subst; tcsp; GC;
  rw swapvar_not_in; auto.
Qed.

Lemma disjoint_get_fo_vars_flat_map_r :
  forall {T} (l : list T) f vs,
    disjoint vs (get_fo_vars (flat_map f l))
    <=>
    (forall x, LIn x l -> disjoint vs (get_fo_vars (f x))).
Proof.
  induction l; simpl; introv; split; intro k; tcsp.
  - introv i; dorn i; subst; tcsp.
    + allrw get_fo_vars_app.
      allrw disjoint_app_r; sp.
    + allrw get_fo_vars_app.
      allrw disjoint_app_r; repnd.
      rw IHl in k; apply k; auto.
  - rw get_fo_vars_app.
    rw disjoint_app_r; dands; auto.
    apply IHl; introv i.
    apply k; sp.
Qed.

Lemma disjoint_swapbvars2 :
  forall bvs vs1 vs2 : list NVar,
    disjoint vs1 vs2
    -> no_repeats vs2
    -> disjoint vs2 bvs
    -> length vs1 = length vs2
    -> disjoint vs1 (swapbvars (mk_swapping vs1 vs2) bvs).
Proof.
  induction bvs; introv disj1 norep disj2 len; allsimpl; auto.
  rw disjoint_cons_r in disj2; repnd.
  rw disjoint_cons_r; dands; auto.
  pose proof (in_deq NVar deq_nvar a vs1) as h; dorn h.
  * pose proof (swapvar_implies3 vs1 vs2 a norep disj1 len h) as k.
    rw disjoint_sym in disj1; apply disj1 in k; tcsp.
  * rw swapvar_not_in; sp.
Qed.

Lemma free_fo_vars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    disjoint vs1 vs2
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> disjoint vs1 (get_fo_vars (so_free_vars (so_swap (mk_swapping vs1 vs2) t))).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl;
  introv disj1 disj2 norep len; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl.
    + allrw disjoint_singleton_r.
      pose proof (in_deq NVar deq_nvar v vs1) as h; dorn h.
      * pose proof (swapvar_implies3 vs1 vs2 v norep disj1 len h) as k.
        rw disjoint_sym in disj1; apply disj1 in k; tcsp.
      * rw swapvar_not_in; sp.
    + rw map_length.
      allrw disjoint_cons_r; repnd.
      rw <- length0 in n.
      destruct (length ts); cpx.
      apply disjoint_get_fo_vars_flat_map_r; introv k.
      rw in_map_iff in k; exrepnd; subst.
      apply ind; auto.
      allrw disjoint_flat_map_r.
      apply disj0; auto.

  - Case "soterm".
    apply disjoint_get_fo_vars_flat_map_r; introv k.
    rw in_map_iff in k; exrepnd; subst.
    destruct a; simpl.
    rw get_fo_vars_remove_so_vars.
    pose proof (ind s l k1 vs1 vs2) as h; repeat (autodimp h hyp).
    + allrw disjoint_flat_map_r.
      apply disj2 in k1; simpl in k1.
      allrw disjoint_app_r; sp.
    + introv i j.
      apply h in i.
      rw in_remove_nvars in j; sp.
Qed.

Lemma fo_bound_vars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    disjoint vs1 vs2
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> disjoint vs1 (fo_bound_vars (so_swap (mk_swapping vs1 vs2) t)).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl;
  introv disj1 disj2 norep len; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw disjoint_flat_map_r; introv i.
    rw in_map_iff in i; exrepnd; subst.
    apply ind; auto.
    allrw disjoint_cons_r; allrw disjoint_flat_map_r; repnd.
    apply disj0; auto.

  - Case "soterm".
    rw flat_map_map; unfold compose.
    rw disjoint_flat_map_r; introv i.
    destruct x; simpl.
    rw disjoint_app_r; dands; auto.
    + apply disjoint_swapbvars2; auto.
      rw disjoint_flat_map_r in disj2.
      apply disj2 in i; simpl in i.
      rw disjoint_app_r in i; sp.
    + eapply ind; eauto.
      rw disjoint_flat_map_r in disj2.
      apply disj2 in i; simpl in i.
      rw disjoint_app_r in i; sp.
Qed.

Lemma sosub_find_sosub_filter {o} :
  forall (sub : @SOSub o) vs v,
    !LIn v vs
    -> sosub_find (sosub_filter sub vs) v
       = sosub_find sub v.
Proof.
  induction sub; introv i; simpl; auto.
  destruct v; destruct a; destruct s;
  boolvar; simpl; cpx;
  boolvar; simpl; cpx.
Qed.

Lemma sosub_filter_swap {o} :
  forall (sub : @SOSub o) vs1 vs2,
    sosub_filter (sosub_filter sub vs1) vs2
    = sosub_filter (sosub_filter sub vs2) vs1.
Proof.
  induction sub; introv; simpl; auto.
  destruct a; destruct s;
  boolvar; simpl; tcsp;
  boolvar; simpl; tcsp.
  rw IHsub; auto.
Qed.

Fixpoint fovars {p} (t : @SOTerm p) : list NVar :=
  match t with
  | sovar v ts =>
    if bnull ts
    then v :: flat_map fovars ts
    else flat_map fovars ts
  | soterm op bs => flat_map fovars_bterm bs
  end
with fovars_bterm {p} (bt : @SOBTerm p) : list NVar :=
       match bt with
       | sobterm lv nt => lv ++ fovars nt
       end.

Lemma fovars_subvars_all_fo_vars {o} :
  forall t : @SOTerm o,
    subvars (fovars t) (all_fo_vars t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    apply subvars_cons_r.
    apply subvars_flat_map2; auto.

  - Case "soterm".
    apply subvars_flat_map2; introv i.
    destruct x; simpl.
    apply subvars_app_l; dands.
    + apply subvars_app_weak_l; auto.
    + apply subvars_app_weak_r; auto.
      eapply ind; eauto.
Qed.

Lemma get_fo_vars_flat_map :
  forall {T} f (l : list T),
    get_fo_vars (flat_map f l)
    = flat_map (fun x => get_fo_vars (f x)) l.
Proof.
  induction l; simpl; auto.
  rw get_fo_vars_app.
  rw IHl; auto.
Qed.

Lemma flat_map_app_f :
  forall {A B} (f g : A -> list B) (l : list A),
    eqset
      (flat_map f l ++ flat_map g l)
      (flat_map (fun x => f x ++ g x) l).
Proof.
  induction l; simpl; auto.
  allunfold @eqset; introv; split; intro i; allrw in_app_iff.
  - rw <- IHl; allrw in_app_iff; sp.
  - rw <- IHl in i; allrw in_app_iff; sp.
Qed.

Lemma eqvars_is_eqset :
  forall l1 l2,
    eqvars l1 l2 <=> eqset l1 l2.
Proof.
  introv; rw eqvars_prop; unfold eqset; sp.
Qed.

Lemma implies_eqvars_flat_map :
  forall {A} f g (l : list A),
    (forall x, LIn x l -> eqvars (f x) (g x))
    -> eqvars (flat_map f l) (flat_map g l).
Proof.
  induction l; introv h; allsimpl; auto.
  apply eqvars_app; auto.
Qed.

Lemma eqvars_remove_nvars_app :
  forall vs1 vs2 vs3,
    eqvars (remove_nvars vs1 vs2 ++ vs1 ++ vs3)
           (vs1 ++ vs2 ++ vs3).
Proof.
  introv; rw eqvars_prop; introv; split; intro i;
  allrw in_app_iff; allrw in_remove_nvars; sp.
  destruct (in_deq NVar deq_nvar x vs1); sp.
Qed.

Lemma fovars_eqvars {o} :
  forall (t : @SOTerm o),
    eqvars
      (fovars t)
      (get_fo_vars (so_free_vars t) ++ fo_bound_vars t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; simpl; auto.
    rw <- length0 in n.
    destruct (length ts); tcsp.
    rw @get_fo_vars_flat_map.
    pose proof (flat_map_app_f
                  (fun t : SOTerm => get_fo_vars (so_free_vars t))
                  fo_bound_vars
                  ts) as e.
    rw <- eqvars_is_eqset in e.
    eapply eqvars_trans;[|apply eqvars_sym; exact e].
    apply implies_eqvars_flat_map; auto.

  - Case "soterm".
    rw @get_fo_vars_flat_map.
    pose proof (flat_map_app_f
                  (fun t => get_fo_vars (so_free_vars_bterm t))
                  fo_bound_vars_bterm
                  lbt) as e.
    rw <- eqvars_is_eqset in e.
    eapply eqvars_trans;[|apply eqvars_sym; exact e].
    apply implies_eqvars_flat_map; auto.
    introv i; destruct x; simpl.
    rw get_fo_vars_remove_so_vars.
    pose proof (eqvars_remove_nvars_app
                  l (get_fo_vars (so_free_vars s))
                  (fo_bound_vars s)) as h.
    eapply eqvars_trans; [|apply eqvars_sym; exact h].
    apply eqvars_app; auto.
    eapply ind; eauto.
Qed.

Lemma fo_free_vars_in_fovars {o} :
  forall (t : @SOTerm o) v,
    LIn (v, 0) (so_free_vars t)
    -> LIn v (fovars t).
Proof.
  introv i.
  pose proof (fovars_eqvars t) as h.
  rw eqvars_prop in h.
  apply h.
  rw in_app_iff.
  left.
  rw in_get_fo_vars; auto.
Qed.

Lemma disjoint_bound_vars_prop2 {o} :
  forall (sub : @SOSub o) v vs t ts,
    disjoint (bound_vars_in_sosub sub) (free_vars_sosub sub)
    -> disjoint (bound_vars_in_sosub sub) (flat_map fovars ts)
    -> LIn (v, sosk vs t) sub
    -> (forall u, LIn u ts -> cover_so_vars u sub)
    -> disjoint (bound_vars t) (flat_map (fun x => free_vars (sosub_aux sub x)) ts).
Proof.
  introv disj1 disj2 insub cov.
  apply disjoint_flat_map_r; introv i.
  allrw disjoint_flat_map_l.
  applydup disj1 in insub; allsimpl.
  applydup disj2 in insub; allsimpl.
  pose proof (isprogram_sosub_aux_free_vars x sub) as h.
  eapply subvars_disjoint_r;[eauto|]; clear h.
  rw disjoint_app_r; dands; auto.
  applydup cov in i.
  apply disjoint_map_r; introv k.
  rw in_remove_so_vars in k; repnd.
  destruct x0; simpl.
  unfold cover_so_vars in i0.
  destruct n0.
  - rw disjoint_flat_map_r in insub1.
    apply insub1 in i.
    apply disjoint_sym in i.
    apply fo_free_vars_in_fovars in k0.
    apply i in k0; auto.
  - rw subsovars_prop in i0.
    pose proof (i0 (n,S n0)) as h; autodimp h hyp.
    + apply in_filter_out_fo_vars; auto; lia.
    + rw in_filter_out_fo_vars2 in h; tcsp.
Qed.

Lemma disjoint_bound_vars_prop3 {o} :
  forall (sub : @SOSub o) v vs t ts,
    disjoint (bound_vars_sosub sub) (free_vars_sosub sub)
    -> disjoint (bound_vars_sosub sub) (flat_map fovars ts)
    -> LIn (v, sosk vs t) sub
    -> (forall u, LIn u ts -> cover_so_vars u sub)
    -> disjoint (bound_vars t) (flat_map (fun x => free_vars (sosub_aux sub x)) ts).
Proof.
  introv disj1 disj2 insub cov.
  eapply disjoint_bound_vars_prop2; eauto;
  eapply subvars_disjoint_l;[|eauto|idtac|eauto];
  apply subvars_bound_vars_in_sosub_bound_vars_sosub.
Qed.

Lemma disjoint_fovars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    disjoint vs1 vs2
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> length vs1 = length vs2
    -> disjoint vs1 (fovars (so_swap (mk_swapping vs1 vs2) t)).
Proof.
  introv disj1 disj2 norep len.
  eapply eqvars_disjoint_r;
    [apply eqvars_sym;apply fovars_eqvars|].
  rw disjoint_app_r; dands.
  - apply free_fo_vars_so_swap; auto.
  - apply fo_bound_vars_so_swap; auto.
Qed.

Lemma sosub_aux_sosub_filter {o} :
  forall (t : @SOTerm o) (sub : @SOSub o) l,
    disjoint l (fovars t)
    -> sosub_aux (sosub_filter sub (vars2sovars l)) t
       = sosub_aux sub t.
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv disj; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl.
    + rw disjoint_singleton_r in disj; repnd.
      rw @sosub_find_sosub_filter;
        [|rw in_map_iff; unfold var2sovar; intro k; exrepnd; complete cpx].
      remember (sosub_find sub (v, 0)) as f;
        symmetry in Heqf; destruct f; auto.
    + rw @sosub_find_sosub_filter;
        [|rw in_map_iff; unfold var2sovar; intro k; exrepnd;
          cpx; destruct ts; allsimpl; complete cpx].
      remember (sosub_find sub (v, length ts)) as f;
        symmetry in Heqf; destruct f.
      * destruct s.
        f_equal; f_equal.
        apply eq_maps; introv i.
        apply ind; auto.
        rw disjoint_flat_map_r in disj; apply disj; auto.
      * f_equal.
        apply eq_maps; introv i.
        apply ind; auto.
        rw disjoint_flat_map_r in disj; apply disj; auto.

  - Case "soterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x; simpl.
    f_equal.
    rw @sosub_filter_swap.
    eapply ind; eauto.
    rw disjoint_flat_map_r in disj.
    apply disj in i; simpl in i.
    rw disjoint_app_r in i; sp.
Qed.

Lemma disjoint_swap :
  forall vs1 vs2 l1 l2,
    disjoint vs1 vs2
    -> no_repeats vs2
    -> disjoint l1 l2
    -> disjoint
         (swapbvars (mk_swapping vs1 vs2) l1)
         (swapbvars (mk_swapping vs1 vs2) l2).
Proof.
  introv disj1 norep disj2 i j.
  allrw in_swapbvars; exrepnd; subst.
  apply swapvars_eq in i0; subst; auto.
  apply disj2 in j1; auto.
Qed.

Lemma fo_bound_var_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    fo_bound_vars (so_swap (mk_swapping vs1 vs2) t)
    = swapbvars (mk_swapping vs1 vs2) (fo_bound_vars t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; simpl; auto.
    unfold swapbvars; rw map_flat_map.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    apply ind; auto.

  - Case "soterm".
    unfold swapbvars; rw map_flat_map.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    rw map_app.
    erewrite ind; eauto.
Qed.

Lemma swapbvars_app :
  forall sw vs1 vs2,
    swapbvars sw (vs1 ++ vs2) = swapbvars sw vs1 ++ swapbvars sw vs2.
Proof.
  introv; unfold swapbvars; rw map_app; auto.
Qed.

Lemma swapbvars_flat_map :
  forall {A} sw f (l : list A),
    swapbvars sw (flat_map f l)
    = flat_map (fun a => swapbvars sw (f a)) l.
Proof.
  introv; unfold swapbvars.
  rw map_flat_map; unfold compose; auto.
Qed.

Lemma fovars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2,
    fovars (so_swap (mk_swapping vs1 vs2) t)
    = swapbvars (mk_swapping vs1 vs2) (fovars t).
Proof.
  soterm_ind t as [ v ts ind | op lbt ind ] Case; simpl; introv; tcsp.

  - Case "sovar".
    boolvar; subst; simpl; boolvar; simpl; auto; cpx.
    + destruct ts; allsimpl; cpx.
    + rw flat_map_map; unfold compose.
      rw @swapbvars_flat_map.
      apply eq_flat_maps; introv i.
      apply ind; auto.

  - Case "soterm".
    rw @swapbvars_flat_map.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.
    rw swapbvars_app.
    apply app_if; auto.
    eapply ind; eauto.
Qed.

Lemma free_vars_sosub_kind_swapsk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_sosub_kind (swapsk (mk_swapping vs1 vs2) sk)
       = swapbvars (mk_swapping vs1 vs2) (free_vars_sosub_kind sk).
Proof.
  introv norep disj.
  destruct sk; simpl.
  unfold free_vars_sosub_kind; simpl.

  revert l.
  nterm_ind n as [v|op bs ind] Case; simpl; introv; auto.

  - Case "vterm".
    repeat (rw remove_nvars_cons_r); boolvar; simpl;
    allrw remove_nvars_nil_r; auto; provefalse.
    + rw in_map_iff in Heqb; exrepnd.
      apply swapvars_eq in Heqb1; subst; sp.
    + destruct Heqb.
      rw in_map_iff.
      eexists; eauto.

  - Case "oterm".
    repeat (rw remove_nvars_flat_map); unfold compose.
    unfold swapbvars; rw map_flat_map; unfold compose.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x; simpl.
    repeat (rw remove_nvars_app_l).
    unfold swapbvars; rw <- map_app.
    eapply ind; eauto.
Qed.

Lemma free_vars_sosub_kind_cswapsk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_sosub_kind (cswapsk (mk_swapping vs1 vs2) sk)
       = swapbvars (mk_swapping vs1 vs2) (free_vars_sosub_kind sk).
Proof.
  introv norep disj.
  destruct sk; simpl.
  unfold free_vars_sosub_kind; simpl.

  revert l.
  nterm_ind n as [v|op bs ind] Case; simpl; introv; auto.

  - Case "vterm".
    repeat (rw remove_nvars_cons_r); boolvar; simpl;
    allrw remove_nvars_nil_r; auto; provefalse.
    + rw in_map_iff in Heqb; exrepnd.
      apply swapvars_eq in Heqb1; subst; sp.
    + destruct Heqb.
      rw in_map_iff.
      eexists; eauto.

  - Case "oterm".
    repeat (rw remove_nvars_flat_map); unfold compose.
    unfold swapbvars; rw map_flat_map; unfold compose.
    rw flat_map_map; unfold compose.
    apply eq_flat_maps; introv i; destruct x; simpl.
    repeat (rw remove_nvars_app_l).
    unfold swapbvars; rw <- map_app.
    eapply ind; eauto.
Qed.

Lemma free_vars_sosub_kind_swapsks {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> flat_map free_vars_sosub_kind (map (swapsk (mk_swapping vs1 vs2)) sks)
       = swapbvars (mk_swapping vs1 vs2) (flat_map free_vars_sosub_kind sks).
Proof.
  induction sks; introv norep disj; simpl; auto.
  rw IHsks; auto; clear IHsks.
  rw swapbvars_app.
  rw @free_vars_sosub_kind_swapsk; auto.
Qed.

Lemma free_vars_sk_swapsks {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> flat_map free_vars_sk (map (swapsk (mk_swapping vs1 vs2)) sks)
       = swapbvars (mk_swapping vs1 vs2) (flat_map free_vars_sk sks).
Proof.
  induction sks; introv norep disj; simpl; auto.
  rw IHsks; auto; clear IHsks.
  rw swapbvars_app.
  allrw @free_vars_sk_is_free_vars_sosub_kind.
  rw @free_vars_sosub_kind_swapsk; auto.
Qed.

Lemma free_vars_sk_cswapsks {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> flat_map free_vars_sk (map (cswapsk (mk_swapping vs1 vs2)) sks)
       = swapbvars (mk_swapping vs1 vs2) (flat_map free_vars_sk sks).
Proof.
  induction sks; introv norep disj; simpl; auto.
  rw IHsks; auto; clear IHsks.
  rw swapbvars_app.
  allrw @free_vars_sk_is_free_vars_sosub_kind.
  rw @free_vars_sosub_kind_cswapsk; auto.
Qed.

Lemma bound_vars_swap {o} :
  forall (t : @NTerm o) vs1 vs2,
    bound_vars (swap (mk_swapping vs1 vs2) t)
    = swapbvars (mk_swapping vs1 vs2) (bound_vars t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl.
  rw swapbvars_app.
  apply app_if; auto.
  eapply ind; eauto.
Qed.

Lemma bound_vars_cswap {o} :
  forall (t : @NTerm o) vs1 vs2,
    bound_vars (cswap (mk_swapping vs1 vs2) t)
    = swapbvars (mk_swapping vs1 vs2) (bound_vars t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  rw @swapbvars_flat_map.
  rw flat_map_map; unfold compose.
  apply eq_flat_maps; introv i; destruct x; simpl.
  rw swapbvars_app.
  apply app_if; auto.
  eapply ind; eauto.
Qed.

Lemma bound_vars_in_sk_swapsk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    bound_vars_in_sk (swapsk (mk_swapping vs1 vs2) sk)
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_in_sk sk).
Proof.
  destruct sk; introv; simpl.
  apply bound_vars_swap; auto.
Qed.

Lemma bound_vars_sk_swapsk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    bound_vars_sk (swapsk (mk_swapping vs1 vs2) sk)
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_sk sk).
Proof.
  destruct sk; introv; simpl.
  rw swapbvars_app.
  apply app_if; auto.
  apply bound_vars_swap; auto.
Qed.

Lemma bound_vars_sk_cswapsk {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    bound_vars_sk (cswapsk (mk_swapping vs1 vs2) sk)
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_sk sk).
Proof.
  destruct sk; introv; simpl.
  rw swapbvars_app.
  apply app_if; auto.
  apply bound_vars_cswap; auto.
Qed.

Lemma bound_vars_in_sosub_combine_map_swapsk {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2 vs,
    bound_vars_in_sosub (combine vs (map (swapsk (mk_swapping vs1 vs2)) sks))
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_in_sosub (combine vs sks)).
Proof.
  induction sks; destruct vs; introv; allsimpl; auto.
  rw IHsks; clear IHsks.
  rw swapbvars_app.
  apply app_if; auto.
  apply bound_vars_in_sk_swapsk; auto.
Qed.

Lemma bound_vars_sosub_combine_map_swapsk {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2 vs,
    bound_vars_sosub (combine vs (map (swapsk (mk_swapping vs1 vs2)) sks))
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_sosub (combine vs sks)).
Proof.
  induction sks; destruct vs; introv; allsimpl; auto.
  rw IHsks; clear IHsks.
  rw swapbvars_app.
  apply app_if; auto.
  apply bound_vars_sk_swapsk; auto.
Qed.

Lemma bound_vars_sosub_combine_map_cswapsk {o} :
  forall (sks : list (@sosub_kind o)) vs1 vs2 vs,
    bound_vars_sosub (combine vs (map (cswapsk (mk_swapping vs1 vs2)) sks))
    = swapbvars (mk_swapping vs1 vs2) (bound_vars_sosub (combine vs sks)).
Proof.
  induction sks; destruct vs; introv; allsimpl; auto.
  rw IHsks; clear IHsks.
  rw swapbvars_app.
  apply app_if; auto.
  apply bound_vars_sk_cswapsk; auto.
Qed.

Lemma free_vars_sosub_combine_map_swapsk {o} :
  forall (sks : list (@sosub_kind o)) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_sosub (combine vs (map (swapsk (mk_swapping vs1 vs2)) sks))
       = swapbvars (mk_swapping vs1 vs2) (free_vars_sosub (combine vs sks)).
Proof.
  induction sks; destruct vs; introv norep disj; allsimpl; auto.
  rw IHsks; auto; clear IHsks.
  rw swapbvars_app.
  apply app_if; auto.
  allrw @free_vars_sk_is_free_vars_sosub_kind.
  apply free_vars_sosub_kind_swapsk; auto.
Qed.

Lemma free_vars_sosub_combine_map_cswapsk {o} :
  forall (sks : list (@sosub_kind o)) vs vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> free_vars_sosub (combine vs (map (cswapsk (mk_swapping vs1 vs2)) sks))
       = swapbvars (mk_swapping vs1 vs2) (free_vars_sosub (combine vs sks)).
Proof.
  induction sks; destruct vs; introv norep disj; allsimpl; auto.
  rw IHsks; auto; clear IHsks.
  rw swapbvars_app.
  apply app_if; auto.
  allrw @free_vars_sk_is_free_vars_sosub_kind.
  apply free_vars_sosub_kind_cswapsk; auto.
Qed.

Lemma implies_subvars_flat_map_r :
  forall {A} f (l : list A) k a,
    LIn a l
    -> subvars k (f a)
    -> subvars k (flat_map f l).
Proof.
  introv i s.
  allrw subvars_prop; introv h.
  rw lin_flat_map.
  eexists; eauto.
Qed.

Lemma in_sodom_iff {o}:
  forall (sub : @SOSub o) v k,
    LIn (v, k) (sodom sub)
   <=> {vs : list NVar
        & {t : NTerm
        & LIn (v, sosk vs t) sub
        # k = length vs}}.
Proof.
  induction sub; introv; simpl; split; intro h; exrepnd; tcsp;
  destruct a; subst.
  - dorn h; cpx.
    + exists l n; sp.
    + apply IHsub in h; exrepnd; subst.
      exists vs t; sp.
  - dorn h0; cpx; ginv; tcsp.
    right; apply IHsub.
    exists vs t; sp.
Qed.

Lemma select_map :
  forall {A B} (l : list A) (f : A -> B) n,
    select n (map f l) = option_map f (select n l).
Proof.
  induction l; introv; simpl; auto.
  - destruct n; simpl; auto.
  - destruct n; simpl; auto.
Qed.

Lemma cover_so_vars_so_swap {o} :
  forall (t : @SOTerm o) vs1 vs2 vs sks,
    cover_so_vars t (combine vs sks)
    -> cover_so_vars
         (so_swap (mk_swapping vs1 vs2) t)
         (combine vs (map (swapsk (mk_swapping vs1 vs2)) sks)).
Proof.
  soterm_ind1s t as [ v ts ind | op lbt ind ] Case; simpl; introv cov; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto;
    allrw @cover_so_vars_sovar; repnd; dands; allsimpl; tcsp; introv k.

    + rw null_nil_iff in k; provefalse; sp.

    + rw null_map in k.
      apply cov0 in k; clear cov0.
      rw map_length.
      allrw @in_sodom_iff; exrepnd.
      exists (swapbvars (mk_swapping vs1 vs2) vs0)
             (swap (mk_swapping vs1 vs2) t).
      rw length_swapbvars; dands; auto.

      allrw in_combine_sel_iff; exrepnd.
      exists n0; rw map_length; dands; auto.
      rw @select_map; rw <- k2; simpl; auto.

    + rw in_map_iff in k; exrepnd; subst.
      applydup cov in k1.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm; introv i.
    rw in_map_iff in i; exrepnd.
    destruct a; allsimpl; ginv.
    applydup cov in i1.
    eapply ind; eauto.
Qed.

Lemma cover_so_vars_so_swapc {o} :
  forall (t : @SOTerm o) vs1 vs2 vs sks,
    cover_so_vars t (combine vs sks)
    -> cover_so_vars
         (so_swap (mk_swapping vs1 vs2) t)
         (combine vs (map (cswapsk (mk_swapping vs1 vs2)) sks)).
Proof.
  soterm_ind1s t as [ v ts ind | op lbt ind ] Case; simpl; introv cov; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto;
    allrw @cover_so_vars_sovar; repnd; dands; allsimpl; tcsp; introv k.

    + rw null_nil_iff in k; provefalse; sp.

    + rw null_map in k.
      apply cov0 in k; clear cov0.
      rw map_length.
      allrw @in_sodom_iff; exrepnd.
      exists (swapbvars (mk_swapping vs1 vs2) vs0)
             (cswap (mk_swapping vs1 vs2) t).
      rw length_swapbvars; dands; auto.

      allrw in_combine_sel_iff; exrepnd.
      exists n0; rw map_length; dands; auto.
      rw @select_map; rw <- k2; simpl; auto.

    + rw in_map_iff in k; exrepnd; subst.
      applydup cov in k1.
      apply ind; auto.

  - Case "soterm".
    allrw @cover_so_vars_soterm; introv i.
    rw in_map_iff in i; exrepnd.
    destruct a; allsimpl; ginv.
    applydup cov in i1.
    eapply ind; eauto.
Qed.

Lemma bound_vars_in_sosub_combine {o} :
  forall (sks : list (@sosub_kind o)) vs,
    length vs = length sks
    -> bound_vars_in_sosub (combine vs sks)
       = flat_map bound_vars_in_sk sks.
Proof.
  induction sks; destruct vs; introv len; allsimpl; cpx.
  rw IHsks; sp.
Qed.

Lemma bound_vars_sosub_combine {o} :
  forall (sks : list (@sosub_kind o)) vs,
    length vs = length sks
    -> bound_vars_sosub (combine vs sks)
       = flat_map bound_vars_sk sks.
Proof.
  induction sks; destruct vs; introv len; allsimpl; cpx.
  rw IHsks; sp.
Qed.

Lemma free_vars_sosub_combine {o} :
  forall (sks : list (@sosub_kind o)) vs,
    length vs = length sks
    -> free_vars_sosub (combine vs sks)
       = flat_map free_vars_sk sks.
Proof.
  induction sks; destruct vs; introv len; allsimpl; cpx.
  rw IHsks; auto.
Qed.

Lemma swapbvars_trivial :
  forall vs1 vs2 l,
    disjoint l vs1
    -> disjoint l vs2
    -> swapbvars (mk_swapping vs1 vs2) l = l.
Proof.
  induction l; introv d1 d2; allsimpl; auto.
  allrw disjoint_cons_l; repnd.
  rw IHl; auto.
  rw swapvar_not_in; auto.
Qed.

Lemma eq_map_l :
  forall A (f : A -> A) (l : list A),
    (forall x,  LIn x l -> f x = x)
    -> map f l = l.
Proof.
  induction l; intro h; allsimpl; tcsp.
  rw IHl; auto.
  rw h; auto.
Qed.

Lemma cswap_trivial {o} :
  forall (t : @NTerm o) vs1 vs2,
    disjoint (allvars t) vs1
    -> disjoint (allvars t) vs2
    -> cswap (mk_swapping vs1 vs2) t = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv d1 d2; allsimpl; auto.

  - Case "vterm".
    allrw disjoint_singleton_l.
    rw swapvar_not_in; auto.

  - Case "oterm".
    f_equal.
    allrw disjoint_flat_map_l.
    apply eq_map_l; introv i.
    destruct x; allsimpl.
    applydup d1 in i.
    applydup d2 in i.
    allsimpl; allrw disjoint_app_l; repnd.
    rw swapbvars_trivial; auto.
    f_equal.
    eapply ind; eauto.
Qed.

Lemma cswapsk_trivial {o} :
  forall (sk : @sosub_kind o) vs1 vs2,
    disjoint (bound_vars_sk sk) vs1
    -> disjoint (bound_vars_sk sk) vs2
    -> disjoint (free_vars_sk sk) vs1
    -> disjoint (free_vars_sk sk) vs2
    -> cswapsk (mk_swapping vs1 vs2) sk = sk.
Proof.
  destruct sk; introv d1 d2 d3 d4; allsimpl.
  allrw disjoint_app_l; repnd.
  rw swapbvars_trivial; auto.
  f_equal.
  pose proof (allvars_eq_all_vars n) as e.
  apply eqvars_sym in e.
  apply disjoint_sym in d3; apply disjoint_sym in d4.
  apply disjoint_sym in d0; apply disjoint_sym in d5.
  apply cswap_trivial.
  - eapply eqvars_disjoint;[eauto|].
    rw disjoint_app_l; dands; auto.
    introv a b.
    applydup d3 in b.
    applydup d0 in b.
    rw in_remove_nvars in b0; sp.
  - eapply eqvars_disjoint;[eauto|].
    rw disjoint_app_l; dands; auto.
    introv a b.
    applydup d4 in b.
    applydup d5 in b.
    rw in_remove_nvars in b0; sp.
Qed.

Lemma sosub_aux_alpha_congr {p} :
  forall (t1 t2 : @SOTerm p) (vs : list NVar) (ts1 ts2 : list sosub_kind),
    let sub1 := combine vs ts1 in
    let sub2 := combine vs ts2 in
    so_alphaeq t1 t2
    -> length vs = length ts1
    -> length vs = length ts2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t1)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t2)
    (* These 2 disjoints we can always assume because they are ensured by sosub *)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t1)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t2)
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> bin_rel_sk alphaeq_sk ts1 ts2
    -> alphaeq (sosub_aux sub1 t1) (sosub_aux sub2 t2).
Proof.
  soterm_ind1s t1 as [ v1 ts1 ind1 | op1 lbt1 ind1 ] Case; simpl;
  introv aeq len1 len2 d1 d2 d3 d4 cov1 cov2 ask; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? len imp |]; subst; clear aeq; simpl.
    remember (sosub_find (combine vs ts0) (v1, length ts1)) as o;
      destruct o; symmetry in Heqo;
      remember (sosub_find (combine vs ts2) (v1, length ts4)) as q;
      destruct q; symmetry in Heqq;
      try (destruct s); try (destruct s0).

    + rw len in Heqo.

      pose proof (apply_bterm_alpha_congr
                    (bterm l n)
                    (bterm l0 n0)
                    (map (sosub_aux (combine vs ts0)) ts1)
                    (map (sosub_aux (combine vs ts2)) ts4)) as h.
      unfold apply_bterm in h; simpl in h.

      revert h.
      change_to_lsubst_aux4.

      * introv h; apply alphaeq_eq; apply h; clear h; auto.

        {
          apply alphaeqbt_eq.
          apply alphaeq_sk_iff_alphaeq_bterm.
          eapply alphaeq_sosub_kind_if_alphaeq_sosub_find;
            [|idtac|idtac|exact Heqo|exact Heqq]; auto.
        }

        {
          apply bin_rel_nterm_if_combine; allrw map_length; auto.
          introv i.
          rw <- @map_combine in i.
          rw in_map_iff in i; exrepnd; cpx; allsimpl.
        }

        {
          rw map_length; unfold num_bvars; simpl; auto.
          apply sosub_find_some in Heqo; sp; lia.
        }

      * apply alphaeq_eq; apply h; clear h; auto.

        {
          apply alphaeqbt_eq.
          apply alphaeq_sk_iff_alphaeq_bterm.
          eapply alphaeq_sosub_kind_if_alphaeq_sosub_find;
            [|idtac|idtac|exact Heqo|exact Heqq]; auto.
        }

        {
          apply bin_rel_nterm_if_combine; allrw map_length; auto.
          introv i.
          rw <- @map_combine in i.
          rw in_map_iff in i; exrepnd; cpx; allsimpl.
          applydup imp in i1.
          applydup in_combine in i1; repnd.
          apply alphaeq_eq.
          apply ind1; auto.

          {
            rw disjoint_flat_map_r in d1.
            apply d1 in i3; auto.
          }

          {
            rw disjoint_flat_map_r in d2.
            apply d2 in i2; auto.
          }

          {
            rw disjoint_app_r; dands; auto.
            rw disjoint_flat_map_r in d3.
            apply d3 in i3; auto.
          }

          {
            rw disjoint_app_r; dands; auto.
            boolvar.
            {
              rw disjoint_cons_r in d4; repnd.
              rw disjoint_flat_map_r in d7.
              apply d7 in i2; auto.
            }
            {
              rw disjoint_flat_map_r in d4.
              apply d4 in i2; auto.
            }
          }

          {
            rw @cover_so_vars_sovar in cov1; repnd.
            apply cov1; auto.
          }

          {
            rw @cover_so_vars_sovar in cov2; repnd.
            apply cov2; auto.
          }
        }

        {
          unfold num_bvars; simpl.
          apply sosub_find_some in Heqo; repnd; lia.
        }

      * clear h; allsimpl; clear d.
        apply sosub_find_some in Heqq; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        {
          boolvar; auto.
          allrw disjoint_cons_r; sp.
        }
        {
          allrw @cover_so_vars_sovar; sp.
        }

      * clear h; allsimpl; clear d.
        apply sosub_find_some in Heqq; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        {
          boolvar; auto.
          allrw disjoint_cons_r; sp.
        }
        {
          allrw @cover_so_vars_sovar; sp.
        }

      * clear h; allsimpl; clear d.
        apply sosub_find_some in Heqo; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        allrw @cover_so_vars_sovar; sp.

      * clear h; allsimpl; clear d.
        apply sosub_find_some in Heqo; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        allrw @cover_so_vars_sovar; sp.

      * clear h; allsimpl.
        apply sosub_find_some in Heqq; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        allrw @cover_so_vars_sovar; sp.
        {
          boolvar; auto.
          allrw disjoint_cons_r; sp.
        }
        {
          allrw @cover_so_vars_sovar; sp.
        }

      * clear h; allsimpl.
        apply sosub_find_some in Heqq; repnd.
        rw @range_combine;[|rw map_length; lia].
        allrw disjoint_cons_r; repnd.
        rw flat_map_map; unfold compose.
        eapply disjoint_bound_vars_prop3; eauto.
        allrw @cover_so_vars_sovar; sp.
        {
          boolvar; auto.
          allrw disjoint_cons_r; sp.
        }
        {
          allrw @cover_so_vars_sovar; sp.
        }

    + rw len in Heqo.
      eapply false_if_alphaeq_sosub_find in Heqo; eauto; sp.

    + rw len in Heqo.
      eapply false_if_alphaeq_sosub_find in Heqo; eauto; sp.
      apply bin_rel_sk_sym; auto.

    + apply alphaeq_apply_list; auto.
      * apply alphaeq_eq; auto.
      * apply bin_rel_nterm_if_combine; allrw map_length; auto.
        introv i.
        rw <- @map_combine in i.
        rw in_map_iff in i; exrepnd; cpx; allsimpl.
        applydup imp in i1.
        applydup in_combine in i1; repnd.
        apply alphaeq_eq.
        apply ind1; auto.

        {
          introv i j; apply d1 in i.
          destruct i; rw lin_flat_map; eexists; eauto.
        }

        {
          introv i j; apply d2 in i.
          destruct i; rw lin_flat_map; eexists; eauto.
        }

        {
          allrw disjoint_app_r; repnd; dands; auto.
          boolvar; subst; allsimpl; cpx.
          rw disjoint_flat_map_r in d3; apply d3 in i3; auto.
        }

        {
          allrw disjoint_app_r; repnd; dands; auto.
          boolvar; subst; allsimpl; cpx.
          rw disjoint_flat_map_r in d4; apply d4 in i2; auto.
        }

        {
          rw @cover_so_vars_sovar in cov1; repnd.
          apply cov1; auto.
        }

        {
          rw @cover_so_vars_sovar in cov2; repnd.
          apply cov2; auto.
        }

  - Case "soterm".
    inversion aeq as [ |? ? ? len imp]; subst; clear aeq; simpl.
    constructor; try (complete (repeat (rw map_length); auto)).
    introv i.
    rw map_length in i.
    repeat (rw @selectbt_map_sosub_b_aux).
    assert (LIn (selectsobt lbt1 n, selectsobt bts2 n) (combine lbt1 bts2))
      as j by (apply in_combine_sel_iff; exists n; dands; auto; try lia;
               apply selectsobt_as_select; auto; try lia).
    remember (selectsobt lbt1 n) as bt1.
    remember (selectsobt bts2 n) as bt2.
    clear Heqbt1 Heqbt2.
    applydup imp in j.
    destruct bt1, bt2; simpl.

    apply so_alphaeqbt_vs_implies_more
    with (l2 := vs
                ++
                allvars (sosub_aux (sosub_filter (combine vs ts1) (vars2sovars l)) s)
                ++
                allvars (sosub_aux (sosub_filter (combine vs ts2) (vars2sovars l0)) s0)
                ++
                bound_vars_sosub (combine vs ts1)
                ++
                bound_vars_sosub (combine vs ts2)
                ++
                free_vars_sosub (combine vs ts1)
                ++
                free_vars_sosub (combine vs ts2)) in j0; auto.

    inversion j0 as [? ? ? ? ? le1 le2 disj norep aeq]; subst; clear j0.
    apply (aeqbt [] vs0); auto; simpl.

    + eapply subvars_disjoint_r;[|complete eauto].
      repeat (rw subvars_app_l); dands.

      * apply subvars_app_weak_r.
        apply subvars_app_weak_l; auto.

      * apply subvars_app_weak_r.
        apply subvars_app_weak_r.
        apply subvars_app_weak_l; auto.

      * apply subvars_app_weak_l.
        apply subvars_app_weak_r.
        apply subvars_app_weak_l; auto.

      * apply subvars_app_weak_l.
        apply subvars_app_weak_r.
        apply subvars_app_weak_r.
        apply subvars_app_weak_l; auto.

    + assert (disjoint l vs0 # disjoint l0 vs0 # disjoint vs vs0)
        as disjl by (allrw disjoint_app_r; sp; apply disjoint_sym; auto); repnd.

      applydup in_combine in j; repnd.
      simpl in d2.
      rw disjoint_flat_map_r in d1; applydup d1 in j1 as disjb1.
      rw disjoint_flat_map_r in d2; applydup d2 in j0 as disjb2.
      simpl in disjb1, disjb2.
      rw disjoint_app_r in disjb1; rw disjoint_app_r in disjb2; repnd.

      apply so_alphaeq_vs_implies_less with (l2 := []) in aeq; auto.

      repeat (rw @sosub_aux_cswap_cswap3; auto);
        [
        | allrw disjoint_app_r; sp;
          rw @sodom_sosub_filter;
          apply subvars_disjoint_r with (l2 := sovars2vars (sodom (combine vs ts2)));
          [ apply subvars_sovars2vars_prop2;
            apply subsovars_remove_so_vars
          | rewrite @sovars2vars_sodom_combine; auto
          ]
        | rw @sodom_sosub_filter; complete (apply disjoint_get_fo_vars_remove)
        | rw @cover_so_vars_soterm in cov2;
          apply cover_so_vars_sosub_filter;
          eapply cov2; eauto
        | allrw disjoint_app_r; sp;
          rw @sodom_sosub_filter;
          apply subvars_disjoint_r with (l2 := sovars2vars (sodom (combine vs ts2)));
          [ apply subvars_sovars2vars_prop2;
            erewrite alphaeq_sks_implies_eq_sodom_combine; eauto;
            apply subsovars_remove_so_vars
          | rewrite @sovars2vars_sodom_combine; auto
          ]
        | rw @sodom_sosub_filter; complete (apply disjoint_get_fo_vars_remove)
        | rw @cover_so_vars_soterm in cov1;
          apply cover_so_vars_sosub_filter;
          eapply cov1; eauto
        ].

      repeat (rw <- @sosub_filter_cswap_range_sosub; auto).
      repeat (rw @cswap_range_sosub_combine).

      repeat (rw @sosub_aux_sosub_filter; auto);
      [
      | apply disjoint_fovars_so_swap; auto; allrw disjoint_app_r; repnd; complete auto
      | apply disjoint_fovars_so_swap; auto; allrw disjoint_app_r; repnd; complete auto
      ].

      pose proof (ind1
                    s
                    (so_swap (mk_swapping l vs0) s)
                    l
                    j1
                    (sosize_so_swap_le s (mk_swapping l vs0))
                    (so_swap (mk_swapping l0 vs0) s0)
                    vs
                    (map (cswapsk (mk_swapping l vs0)) ts1)
                    (map (cswapsk (mk_swapping l0 vs0)) ts2)
                 ) as h; simpl in h.
      repeat (autodimp h hyp); try (rw map_length; complete auto).

      * rw @fo_bound_var_so_swap.
        rw @free_vars_sosub_combine; [|rw map_length; complete auto].
        rewrite free_vars_sk_cswapsks; auto.
        apply disjoint_swap; auto.
        rw @free_vars_sosub_combine in disjb1; auto.

      * rw @fo_bound_var_so_swap.
        rw @free_vars_sosub_combine; [|rw map_length; complete auto].
        rewrite free_vars_sk_cswapsks; auto.
        apply disjoint_swap; auto.
        rw @free_vars_sosub_combine in disjb2; auto.

      * rw @bound_vars_sosub_combine_map_cswapsk.
        rw @free_vars_sosub_combine_map_cswapsk; auto.
        rw @fovars_so_swap.
        rw <- swapbvars_app.
        apply disjoint_swap; auto.
        eapply subvars_disjoint_r;[|exact d3].
        apply subvars_app_l; dands; auto.
        {
          apply subvars_app_weak_l; auto.
        }
        {
          apply subvars_app_weak_r.
          eapply implies_subvars_flat_map_r; eauto; simpl.
          apply subvars_app_weak_r; auto.
        }

      * rw @bound_vars_sosub_combine_map_cswapsk.
        rw @free_vars_sosub_combine_map_cswapsk; auto.
        rw @fovars_so_swap.
        rw <- swapbvars_app.
        apply disjoint_swap; auto.
        eapply subvars_disjoint_r;[|exact d4].
        apply subvars_app_l; dands; auto.
        {
          apply subvars_app_weak_l; auto.
        }
        {
          apply subvars_app_weak_r.
          eapply implies_subvars_flat_map_r; eauto; simpl.
          apply subvars_app_weak_r; auto.
        }

      * rw @cover_so_vars_soterm in cov1.
        apply cov1 in j1.
        apply cover_so_vars_so_swapc; auto.

      * rw @cover_so_vars_soterm in cov2.
        apply cov2 in j0.
        apply cover_so_vars_so_swapc; auto.

      * allsimpl.
        rw disjoint_app_r in d3; rw disjoint_app_r in d4; repnd.
        rw disjoint_flat_map_r in d3; rw disjoint_flat_map_r in d4.
        applydup d3 in j1.
        applydup d4 in j0.
        simpl in j2, j3.
        rw disjoint_app_r in j2; rw disjoint_app_r in j3; repnd.
        rw @bound_vars_sosub_combine in j4; auto.
        rw @bound_vars_sosub_combine in j5; auto.

        unfold bin_rel_sk, binrel_list.
        allrw map_length.
        unfold bin_rel_sk, binrel_list in ask; repnd.
        dands; auto; introv x.
        applydup ask in x.

        assert (default_sk = cswapsk (mk_swapping l vs0) (@default_sk p))
          as e1 by sp.
        rw e1; clear e1; rw map_nth; simpl; fold (@mk_axiom p); fold (@default_sk p).
        assert (default_sk = cswapsk (mk_swapping l0 vs0) (@default_sk p))
          as e2 by sp.
        rw e2; clear e2; rw map_nth; simpl; fold (@mk_axiom p); fold (@default_sk p).

        pose proof (nth_in _ n0 ts1 default_sk) as i1.
        pose proof (nth_in _ n0 ts2 default_sk) as i2.
        autodimp i1 hyp; autodimp i2 hyp; try lia.
        remember (nth n0 ts1 default_sk) as sk1.
        remember (nth n0 ts2 default_sk) as sk2.
        clear Heqsk1 Heqsk2.

        rw @free_vars_sosub_combine in disjb3; auto.
        rw @free_vars_sosub_combine in disjb0; auto.
        rw disjoint_flat_map_l in j5.
        rw disjoint_flat_map_l in j4.
        rw disjoint_flat_map_l in disjb3.
        rw disjoint_flat_map_l in disjb0.
        applydup j5 in i1.
        applydup j4 in i2.
        applydup disjb3 in i1.
        applydup disjb0 in i2.
        repeat (rw @cswapsk_trivial; auto).

        {
          allrw disjoint_app_r; repnd.
          rw @bound_vars_sosub_combine in disj8; auto.
          rw disjoint_flat_map_r in disj8.
          applydup disj8 in i2.
          apply disjoint_sym; auto.
        }

        {
          allrw disjoint_app_r; repnd.
          rw @free_vars_sosub_combine in disj0; auto.
          rw disjoint_flat_map_r in disj0.
          applydup disj0 in i2.
          apply disjoint_sym; auto.
        }

        {
          allrw disjoint_app_r; repnd.
          rw @bound_vars_sosub_combine in disj7; auto.
          rw disjoint_flat_map_r in disj7.
          applydup disj7 in i1.
          apply disjoint_sym; auto.
        }

        {
          allrw disjoint_app_r; repnd.
          rw @free_vars_sosub_combine in disj9; auto.
          rw disjoint_flat_map_r in disj9.
          applydup disj9 in i1.
          apply disjoint_sym; auto.
        }
Qed.

Lemma sosub_change_bvars_alpha_combine {o} :
  forall (sks : list (@sosub_kind o)) vs l,
    sosub_change_bvars_alpha l (combine vs sks)
    = combine vs (map (sk_change_bvars_alpha l) sks).
Proof.
  induction sks; destruct vs; introv; allsimpl; auto.
  rw IHsks; auto.
Qed.

Lemma free_vars_sk_change_bvars_alpha {o} :
  forall (sk : @sosub_kind o) vs,
    free_vars_sk (sk_change_bvars_alpha vs sk)
    = free_vars_sk sk.
Proof.
  destruct sk; introv; simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd.
  allrw disjoint_app_r; repnd.
  pose proof (free_vars_lsubst_aux_var_ren (change_bvars_alpha vs n) l f []) as h.
  repeat (autodimp h hyp); allrw app_nil_r.
  rw h; rw @free_vars_change_bvars_alpha; auto.
Qed.

Lemma allvars_range_sosub_combine {o} :
  forall (sks : list (@sosub_kind o)) vs,
    length vs = length sks
    -> allvars_range_sosub (combine vs sks)
       = flat_map allvars_sk sks.
Proof.
  induction sks; destruct vs; introv len; allsimpl; tcsp.
  rw IHsks; auto.
Qed.

Lemma free_vars_subvars_allvars_sk {o} :
  forall sk : @sosub_kind o,
    subvars (free_vars_sk sk) (allvars_sk sk).
Proof.
  destruct sk; simpl.
  rw subvars_prop; introv i.
  rw in_remove_nvars in i; rw in_app_iff; repnd; right.
  pose proof (allvars_eq_all_vars n) as e.
  rw eqvars_prop in e; apply e; rw in_app_iff; sp.
Qed.

Lemma sodom_combine_sk_change_bvars_alpha {o} :
  forall (sks : list (@sosub_kind o)) vs l,
    sodom (combine vs (map (sk_change_bvars_alpha l) sks))
    = sodom (combine vs sks).
Proof.
  induction sks; destruct vs; introv; allsimpl; auto.
  destruct a; rw IHsks.
  simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd; allrw; sp.
Qed.

Lemma cover_so_vars_sk_change_bvars_alpha {o} :
  forall (t : @SOTerm o) vs sks l,
    cover_so_vars t (combine vs sks)
    <=> cover_so_vars t (combine vs (map (sk_change_bvars_alpha l) sks)).
Proof.
  introv.
  unfold cover_so_vars.
  rw @sodom_combine_sk_change_bvars_alpha; sp.
Qed.

Lemma alphaeq_sk_trans {o} :
  forall sk1 sk2 sk3 : @sosub_kind o,
    alphaeq_sk sk1 sk2
    -> alphaeq_sk sk2 sk3
    -> alphaeq_sk sk1 sk3.
Proof.
  destruct sk1, sk2, sk3; introv aeq1 aeq2.
  allunfold @alphaeq_sk; allsimpl.
  allrw @alphaeqbt_eq.
  eapply alpha_eq_bterm_trans; eauto.
Qed.

Lemma alphaeq_sk_sym {o} :
  forall (sk1 sk2 : @sosub_kind o),
    alphaeq_sk sk1 sk2 -> alphaeq_sk sk2 sk1.
Proof.
  introv aeq.
  destruct sk1, sk2.
  allunfold @alphaeq_sk; allsimpl.
  apply alphaeqbt_eq.
  apply alphaeqbt_eq in aeq.
  apply alpha_eq_bterm_sym; auto.
Qed.

Lemma alphaeq_sk_change_bvars_alpha {o} :
  forall (sk : @sosub_kind o) l,
    alphaeq_sk sk (sk_change_bvars_alpha l sk).
Proof.
  destruct sk; introv.
  unfold alphaeq_sk; simpl.
  match goal with
    | [ |- context[fresh_distinct_vars ?a ?b] ] =>
      remember (fresh_distinct_vars a b) as f
  end.
  apply fresh_distinct_vars_spec1 in Heqf; repnd.
  rw disjoint_app_r in Heqf1; repnd.

  pose proof (btchange_alpha_aux l (change_bvars_alpha l0 n) f) as h;
    repeat (autodimp h hyp); eauto with slow.
  revert h.
  change_to_lsubst_aux4; introv h.
  apply alphaeqbt_eq.
  eapply alpha_eq_bterm_trans;[|exact h].
  apply alpha_eq_bterm_congr.

  pose proof (change_bvars_alpha_spec n l0) as k; simpl in k; repnd; auto.
Qed.

Lemma so_alphaeq_vs_iff {p} :
  forall l (t1 t2 : @SOTerm p),
    so_alphaeq_vs l t1 t2
    <=> so_alphaeq t1 t2.
Proof.
  introv; split; intro k.
  - apply so_alphaeq_exists; eexists; eauto.
  - rw @so_alphaeq_all in k; sp.
Qed.

Lemma so_alphaeq_add_so_swap2 {p} :
  forall vs1 vs2 (t1 t2 : @SOTerm p),
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs2 (vs1 ++ all_fo_vars t1 ++ all_fo_vars t2)
    -> so_alphaeq t1 t2
    -> so_alphaeq
         (so_swap (mk_swapping vs1 vs2) t1)
         (so_swap (mk_swapping vs1 vs2) t2).
Proof.
  introv len norep2 disj aeq.
  rw <- (@so_alphaeq_vs_iff p (vs1 ++ vs2 ++ [])).
  apply so_alphaeq_add_so_swap; auto.
  apply so_alphaeq_vs_iff; auto.
Qed.

Lemma alphaeq_vs_trans {o} :
  forall (t1 t2 t3 : @NTerm o) vs,
    alphaeq_vs vs t1 t2
    -> alphaeq_vs vs t2 t3
    -> alphaeq_vs vs t1 t3.
Proof.
  introv aeq1 aeq2.
  apply alphaeq_all.
  eapply alphaeq_trans; apply alphaeq_exists; eexists; eauto.
Qed.

Lemma alphaeq_vs_sym {o} :
  forall (t1 t2 : @NTerm o) vs,
    alphaeq_vs vs t1 t2
    -> alphaeq_vs vs t2 t1.
Proof.
  introv aeq.
  apply alphaeq_all.
  eapply alphaeq_sym; apply alphaeq_exists; eexists; eauto.
Qed.

Lemma alphaeq_vs_refl {o} :
  forall (t : @NTerm o) vs,
    alphaeq_vs vs t t.
Proof.
  introv.
  apply alphaeq_all.
  eapply alphaeq_refl; apply alphaeq_exists; eexists; eauto.
Qed.

Lemma so_alphaeq_vs_trans {o} :
  forall (t1 t2 t3 : @SOTerm o) vs,
    so_alphaeq_vs vs t1 t2
    -> so_alphaeq_vs vs t2 t3
    -> so_alphaeq_vs vs t1 t3.
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1 | op1 bs1 ind1] Case;
  introv aeq1 aeq2; allsimpl; tcsp.

  - Case "sovar".
    inversion aeq1 as [? ? ? len1 imp1 |]; subst; clear aeq1.
    inversion aeq2 as [? ? ? len2 imp2 |]; subst; clear aeq2.
    constructor; try lia.
    introv i.
    rw in_combine_sel_iff in i; exrepnd.

    pose proof (nth_select1 n ts1 default_soterm i1) as h1.
    pose proof (nth_select1 n ts3 default_soterm i2) as h2.
    rw h1 in i3; rw h2 in i0; cpx; clear h1 h2.

    pose proof (imp1 (nth n ts1 default_soterm) (nth n ts2 default_soterm)) as h1.
    pose proof (imp2 (nth n ts2 default_soterm) (nth n ts3 default_soterm)) as h2.
    autodimp h1 hyp.
    {
      apply in_combine_sel_iff; exists n; dands; auto; try lia;
      symmetry; apply nth_select1; auto; lia.
    }
    autodimp h2 hyp.
    {
      apply in_combine_sel_iff; exists n; dands; auto; try lia;
      symmetry; apply nth_select1; auto; lia.
    }

    eapply ind1; eauto.
    apply nth_in; auto.

  - Case "soterm".
    inversion aeq1 as [ |? ? ? len1 imp1]; subst; clear aeq1.
    inversion aeq2 as [ |? ? ? len2 imp2]; subst; clear aeq2.
    constructor; try lia.
    introv i.
    destruct b1, b2.
    rw in_combine_sel_iff in i; exrepnd.

    pose proof (nth_select1 n bs1  default_sobterm i1) as h1.
    pose proof (nth_select1 n bts0 default_sobterm i2) as h2.
    rw h1 in i3; rw h2 in i0; cpx; clear h1 h2.

    pose proof (imp1 (nth n bs1  default_sobterm) (nth n bts2 default_sobterm)) as h1; clear imp1.
    pose proof (imp2 (nth n bts2 default_sobterm) (nth n bts0 default_sobterm)) as h2; clear imp2.
    autodimp h1 hyp.
    {
      apply in_combine_sel_iff; exists n; dands; auto; try lia;
      symmetry; apply nth_select1; auto; lia.
    }
    autodimp h2 hyp.
    {
      apply in_combine_sel_iff; exists n; dands; auto; try lia;
      symmetry; apply nth_select1; auto; lia.
    }

    pose proof (nth_in _ n bs1 default_sobterm i1) as j1.
    pose proof (nth_in _ n bts0 default_sobterm i2) as j2.
    rw <- i3 in h1; rw <- i3 in j1; clear i3.
    rw <- i0 in h2; rw <- i0 in j2; clear i0.
    remember (nth n bts2 default_sobterm) as b; clear Heqb.

    inversion h1 as [? ? ? ? ? l1 l2 disj1 norep1 aeq1]; subst; clear h1.

    assert (subvars vs (vs
                          ++ (vs0
                                ++ l
                                ++ all_fo_vars s
                                ++ all_fo_vars t2
                                ++ all_fo_vars (so_swap (mk_swapping l vs0) s)
                                ++ all_fo_vars (so_swap (mk_swapping vs2 vs0) t2)
                             )
                       )
           ) as sv by (apply subvars_app_weak_l; auto).
    eapply so_alphaeqbt_vs_implies_more in h2;[|exact sv].

    inversion h2 as [? ? ? ? ? l3 l4 disj2 norep2 aeq2]; subst; clear h2.
    apply (soaeqbt vs vs1); auto;
    try lia;
    try (complete (allrw disjoint_app_r; sp)).

    apply so_alphaeq_vs_iff in aeq1.
    apply so_alphaeq_vs_iff in aeq2.

    apply (so_alphaeq_add_so_swap2 vs0 vs1) in aeq1; auto;
    try lia;
    try (complete (allrw disjoint_app_r; sp)).

    repeat (rw @so_swap_so_swap in aeq1).
    repeat (rw mk_swapping_app in aeq1; auto).

    rw @so_swap_disj_chain in aeq1; auto;
    try lia;
    try (complete (allrw disjoint_app_r; sp; eauto with slow)).

    rw @so_swap_disj_chain in aeq1; auto;
    try lia;
    try (complete (allrw disjoint_app_r; sp; eauto with slow)).

    apply so_alphaeq_vs_iff.
    eapply ind1;[exact j1|idtac|exact aeq1|exact aeq2].
    rw @sosize_so_swap; auto.
Qed.

Lemma so_alphaeq_trans {o} :
  forall (t1 t2 t3 : @SOTerm o),
    so_alphaeq t1 t2
    -> so_alphaeq t2 t3
    -> so_alphaeq t1 t3.
Proof.
  introv aeq1 aeq2.
  pose proof (so_alphaeq_vs_trans t1 t2 t3 []); sp.
Qed.

Fixpoint soren_filter (ren : soren) (vars : list sovar_sig) : soren :=
  match ren with
    | nil => nil
    | (sov,v) :: xs =>
      if memsovar sov vars
      then soren_filter xs vars
      else (sov,v) :: soren_filter xs vars
  end.

Fixpoint so_rename {p} (ren : soren) (t : @SOTerm p) :=
  match t with
    | sovar v ts =>
      sovar
        (sovar2var (rename_sovar ren (v,length ts)))
        (map (so_rename ren) ts)
    | soterm o bs => soterm o (map (so_rename_bt ren) bs)
  end
with so_rename_bt {p} ren bt :=
       match bt with
         | sobterm vs t =>
           sobterm vs (so_rename (soren_filter ren (vars2sovars vs)) t)
       end.

Lemma swapvar_is_rename_var :
  forall v vs1 vs2,
    !LIn v vs2
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> swapvar (mk_swapping vs1 vs2) v
       = rename_var (mk_swapping vs1 vs2) v.
Proof.
  induction vs1; destruct vs2; introv ni norep disj;
  unfold rename_var; allsimpl; auto.
  allrw not_over_or; repnd.
  allrw disjoint_cons_l.
  allrw disjoint_cons_r; allsimpl; repnd.
  allrw not_over_or; repnd.
  allrw no_repeats_cons; repnd.
  unfold oneswapvar.
  boolvar; tcsp.
  apply swapvar_not_in; auto.
Qed.

Lemma in_combine_swap :
  forall {A} (l1 l2 : list A) a1 a2,
    length l1 = length l2
    -> LIn (a1, a2) (combine l1 l2)
    -> LIn (a2, a1) (combine l2 l1).
Proof.
  induction l1; destruct l2; introv len i; allsimpl; cpx.
  dorn i; cpx.
Qed.

Lemma so_alphaeq_vs_sym {o} :
  forall (t1 t2 : @SOTerm o) vs,
    so_alphaeq_vs vs t1 t2 -> so_alphaeq_vs vs t2 t1.
Proof.
  soterm_ind1s t1 as [v ts ind | op bs ind] Case; introv aeq; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? len imp |]; subst; clear aeq.
    constructor; auto.
    introv i.
    apply in_combine_swap in i; auto.
    applydup imp in i.
    apply ind; auto.
    apply in_combine in i; sp.

  - Case "soterm".
    inversion aeq as [ |? ? ? len imp]; subst; clear aeq.
    constructor; auto.
    introv i.
    apply in_combine_swap in i; auto.
    applydup imp in i.
    destruct b1, b2.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep ae]; subst; clear i0.
    apply (soaeqbt vs vs0); auto;
    try lia;
    try (complete (allrw disjoint_app_r; sp)).
    apply in_combine in i; repnd.
    eapply ind; eauto.
    rw @sosize_so_swap; auto.
Qed.

Lemma so_alphaeq_refl {o} :
  forall t : @SOTerm o, so_alphaeq t t.
Proof.
  soterm_ind1s t as [v ts ind | op bs ind] Case; auto; tcsp.

  - Case "sovar".
    constructor; auto.
    introv i.
    apply in_combine_sel_iff in i; exrepnd.
    rw <- i3 in i0; ginv; apply ind; auto.
    symmetry in i3; apply select_in in i3; auto.

  - Case "soterm".
    constructor; auto.
    introv i.
    apply in_combine_sel_iff in i; exrepnd.
    rw <- i3 in i0; ginv.
    symmetry in i3; apply select_in in i3; auto.
    destruct b1.
    pose proof (fresh_vars (length l) (l ++ all_fo_vars s)) as h; exrepnd.
    apply (soaeqbt [] lvn); allsimpl; auto;
    [allrw disjoint_app_r; complete sp|].
    eapply ind; eauto.
    rw @sosize_so_swap; auto.
Qed.
Hint Immediate so_alphaeq_refl.

Lemma app_combine :
  forall {A} (vs1 vs2 vs3 vs4 : list A),
    length vs1 = length vs2
    -> combine vs1 vs2 ++ combine vs3 vs4
       = combine (vs1 ++ vs3) (vs2 ++ vs4).
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  rw IHvs1; auto.
Qed.

Lemma foren_find_app :
  forall v ren1 ren2,
    foren_find (ren1 ++ ren2) v
    = match foren_find ren1 v with
        | Some w => Some w
        | None => foren_find ren2 v
      end.
Proof.
  induction ren1; simpl; sp.
  destruct a0; destruct v; boolvar; cpx.
Qed.

Lemma foren_find_none :
  forall (ren : foren) v,
    foren_find ren v = None
    -> !LIn v (foren_dom ren).
Proof.
  induction ren; introv k; allsimpl; tcsp.
  destruct a; boolvar; cpx.
  apply IHren in k.
  apply not_over_or; sp.
Qed.

Lemma foren_find_filter_eq :
  forall ren1 ren2 v,
    !LIn v (foren_dom ren1)
    -> foren_find (foren_filter ren2 (foren_dom ren1)) v
       = foren_find ren2 v.
Proof.
  induction ren2; introv ni; allsimpl; auto.
  destruct a; boolvar; simpl; boolvar; tcsp.
Qed.

Lemma rename_var_filter :
  forall ren1 ren2 v,
    rename_var (ren1 ++ ren2) v
    = rename_var (ren1 ++ foren_filter ren2 (foren_dom ren1)) v.
Proof.
  unfold rename_var; introv.
  allrw foren_find_app.
  remember (foren_find ren1 v) as f1; destruct f1; symmetry in Heqf1; auto.
  apply foren_find_none in Heqf1.
  rw foren_find_filter_eq; auto.
Qed.

Lemma foren_vars_app :
  forall ren1 ren2 : foren,
    foren_vars (ren1 ++ ren2) = foren_vars ren1 ++ foren_vars ren2.
Proof.
  induction ren1; introv; allsimpl; auto.
  destruct a; simpl.
  rw IHren1; auto.
Qed.

(*
Lemma fo_change_bvars_alpha_filter {o} :
  forall (t : @SOTerm o) vs ren1 ren2,
    so_alphaeq
      (fo_change_bvars_alpha vs (ren1 ++ ren2) t)
      (fo_change_bvars_alpha vs (ren1 ++ foren_filter ren2 (foren_dom ren1)) t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl.

  - Case "sovar".
    boolvar; subst; allsimpl.
    + rw rename_var_filter; auto.
    + constructor; allrw map_length; auto.
      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx.
      apply in_combine_sel_iff in i1; exrepnd.
      rw <- i3 in i0; ginv.
      symmetry in i3; apply select_in in i3.
      apply ind; simpl; auto.

  - Case "soterm".
    constructor; allrw map_length; auto.
    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; cpx; allsimpl.
    apply in_combine_sel_iff in i1; exrepnd.
    rw <- i3 in i0; ginv.
    symmetry in i3; apply select_in in i3.
    destruct a0; simpl.

    repeat gen_fresh.
    allrw foren_vars_app.
    pose proof (fresh_vars
                  (length f)
                  (f
                     ++ f0
                     ++ vs
                     ++ all_fo_vars s
                     ++ foren_vars ren1
                     ++ foren_vars ren2
                     ++ all_fo_vars (fo_change_bvars_alpha vs (mk_foren l f ++ ren1 ++ ren2) s)
                     ++ all_fo_vars (fo_change_bvars_alpha vs (mk_foren l f0 ++ ren1 ++ foren_filter ren2 (foren_dom ren1)) s)
                  )
               ) as fv; exrepnd.
    apply (soaeqbt [] lvn); simpl; auto; try lia.

    + allrw disjoint_app_r; sp.

    +

Qed.
*)

Lemma eqvars_move_around :
  forall vs1 v vs2,
    eqvars (v :: vs1 ++ vs2) (vs1 ++ v :: vs2).
Proof.
  introv; rw eqvars_prop; introv; simpl.
  allrw in_app_iff; allsimpl; split; sp.
Qed.

Lemma foren_vars_mk_swapping :
  forall vs1 vs2,
    length vs1 = length vs2
    -> eqvars (foren_vars (mk_swapping vs1 vs2)) (vs1 ++ vs2).
Proof.
  induction vs1; destruct vs2; introv len; allsimpl; cpx.
  apply eqvars_cons_lr; auto.
  pose proof (eqvars_move_around vs1 n vs2) as eqv.
  eapply eqvars_trans;[|exact eqv].
  apply eqvars_cons_lr; auto.
Qed.

Lemma subvars_eqvars_r :
  forall s1 s2 s3 : list NVar,
    subvars s1 s2 -> eqvars s2 s3 -> subvars s1 s3.
Proof.
  introv sv eqv.
  allrw subvars_prop.
  allrw eqvars_prop.
  introv i.
  apply sv in i.
  apply eqv in i; auto.
Qed.

Lemma swapvar_app :
  forall sw2 sw1 v,
    swapvar (sw1 ++ sw2) v = swapvar sw2 (swapvar sw1 v).
Proof.
  induction sw1; introv; simpl; auto.
  destruct a; simpl.
  rw IHsw1; auto.
Qed.

Lemma mk_swapping_cons :
  forall a b vs1 vs2,
    mk_swapping (a :: vs1) (b :: vs2) = (a,b) :: mk_swapping vs1 vs2.
Proof. sp. Qed.

Lemma swapvar_cons :
  forall a b sw v,
    swapvar ((a,b) :: sw) v = swapvar sw (oneswapvar a b v).
Proof. sp. Qed.

Lemma swapvar_disj_chain2 :
  forall vs1 vs2 vs3 vs4 vs v,
    length vs1 = length vs
    -> length vs2 = length vs3
    -> length vs = length vs4
    -> !LIn v vs
    -> !LIn v vs4
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs vs3
    -> disjoint vs vs4
    -> disjoint vs4 vs1
    -> disjoint vs4 vs2
    -> disjoint vs4 vs3
    -> no_repeats vs
    -> no_repeats vs3
    -> no_repeats vs4
    -> swapvar (mk_swapping (vs1 ++ vs2 ++ vs) (vs ++ vs3 ++ vs4)) v
       = swapvar (mk_swapping (vs1 ++ vs2) (vs4 ++ vs3)) v.
Proof.
  induction vs1; destruct vs; allsimpl;
  introv len1 len2 len3;
  introv ni1 ni2;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  introv norep1 norep2 norep3;
  allrw app_nil_r; cpx; allsimpl; allrw app_nil_r; auto.

  destruct vs4; allsimpl; cpx.

  unfold oneswapvar; boolvar; tcsp; allrw not_over_or; repnd;
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd;
  allsimpl; allrw not_over_or; repnd;
  allrw no_repeats_cons; repnd; tcsp.

  - rw app_assoc.
    rw app_assoc.
    rw <- mk_swapping_app; try (complete (allrw length_app; sp)).
    rw swapvar_app.
    rw (swapvar_not_in n (vs1 ++ vs2) (vs ++ vs3)); try (complete (rw in_app_iff; sp)).
    rw mk_swapping_cons; simpl.
    unfold oneswapvar; boolvar.
    repeat (rw swapvar_not_in); auto; allrw in_app_iff; tcsp.

  - rw app_assoc.
    rw app_assoc.
    rw <- mk_swapping_app; try (complete (allrw length_app; sp)).
    rw swapvar_app.
    rw mk_swapping_cons; simpl.
    unfold oneswapvar; boolvar; auto.

    + provefalse.
      pose proof (swapvar_implies (vs1 ++ vs2) (vs ++ vs3) v) as h.
      rw e in h; simpl in h.
      allrw in_app_iff; sp.

    + provefalse.
      pose proof (swapvar_implies (vs1 ++ vs2) (vs ++ vs3) v) as h.
      rw e in h; simpl in h.
      allrw in_app_iff; sp.

    + rw <- swapvar_app.
      rw mk_swapping_app; try (complete (allrw length_app; sp)).
      allrw <- app_assoc.
      apply IHvs1; auto.
Qed.

Lemma swapbvars_disj_chain2 :
  forall vs1 vs2 vs3 vs4 vs l,
    length vs1 = length vs
    -> length vs2 = length vs3
    -> length vs = length vs4
    -> disjoint vs l
    -> disjoint vs4 l
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs vs3
    -> disjoint vs vs4
    -> disjoint vs4 vs1
    -> disjoint vs4 vs2
    -> disjoint vs4 vs3
    -> no_repeats vs
    -> no_repeats vs3
    -> no_repeats vs4
    -> swapbvars (mk_swapping (vs1 ++ vs2 ++ vs) (vs ++ vs3 ++ vs4)) l
       = swapbvars (mk_swapping (vs1 ++ vs2) (vs4 ++ vs3)) l.
Proof.
  induction l;
  introv len1 len2 len3;
  introv ni1 ni2;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  introv norep1 norep2 norep3;
  allsimpl; auto.
  allrw disjoint_cons_r; repnd.
  rw swapvar_disj_chain2; auto.
  apply eq_cons; auto.
Qed.

Lemma so_swap_disj_chain2 {o} :
  forall (t : @SOTerm o) (vs1 vs2 vs3 vs4 vs : list NVar),
    length vs1 = length vs
    -> length vs2 = length vs3
    -> length vs = length vs4
    -> disjoint vs (all_fo_vars t)
    -> disjoint vs4 (all_fo_vars t)
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs vs3
    -> disjoint vs vs4
    -> disjoint vs4 vs1
    -> disjoint vs4 vs2
    -> disjoint vs4 vs3
    -> no_repeats vs
    -> no_repeats vs3
    -> no_repeats vs4
    -> so_swap (mk_swapping (vs1 ++ vs2 ++ vs) (vs ++ vs3 ++ vs4)) t
       = so_swap (mk_swapping (vs1 ++ vs2) (vs4 ++ vs3)) t.
Proof.
  soterm_ind1s t as [v ts ind | op bs ind] Case;
  introv len1 len2 len3;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7 disj8 disj9;
  introv norep1 norep2 norep3;
  allsimpl; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.

    + allrw disjoint_singleton_r.
      rw swapvar_disj_chain2; auto.

    + f_equal.
      allrw disjoint_cons_r; repnd.
      allrw disjoint_flat_map_r.
      apply eq_maps; introv i.
      applydup disj0 in i.
      applydup disj10 in i.
      apply ind; auto.

  - Case "soterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x; simpl.
    allrw disjoint_flat_map_r.
    applydup disj1 in i.
    applydup disj2 in i.
    allsimpl.
    allrw disjoint_app_r; repnd.
    rw swapbvars_disj_chain2; auto.
    f_equal.
    eapply ind; eauto.
Qed.

Lemma so_alphaeq_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) vs vs1 vs2,
    length vs1 = length vs2
    -> disjoint vs2 vs1
    -> disjoint vs2 vs
    -> disjoint vs2 (all_fo_vars t)
    -> no_repeats vs2
    -> so_alphaeq
         (so_swap (mk_swapping vs1 vs2) t)
         (fo_change_bvars_alpha vs (mk_swapping vs1 vs2) t).
Proof.
  soterm_ind t as [v ts ind | op bs ind] Case;
  introv len disj1 disj2 disj3 norep; simpl; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    + rw disjoint_singleton_r in disj3.
      rw swapvar_is_rename_var; eauto with slow; auto.

    + constructor;[allrw map_length; complete auto|].
      introv i.
      rw <- @map_combine in i.
      rw in_map_iff in i; exrepnd; cpx; allsimpl.
      rw in_combine_sel_iff in i1; exrepnd.
      rw <- i3 in i0; ginv.
      symmetry in i3; apply select_in in i3.
      eapply ind; auto.
      allrw disjoint_cons_r; repnd.
      allrw disjoint_flat_map_r.
      apply disj0; auto.

  - Case "soterm".
    constructor;[allrw map_length; complete auto|].
    introv i.
    rw <- @map_combine in i.
    rw in_map_iff in i; exrepnd; cpx; allsimpl.
    rw in_combine_sel_iff in i1; exrepnd.
    rw <- i3 in i0; ginv.
    symmetry in i3; apply select_in in i3.

    destruct a0; simpl.
    gen_fresh.

    rw @app_combine; auto.

    pose proof (fresh_vars
                  (length l)
                  (l
                     ++ vs1
                     ++ vs2
                     ++ swapbvars (mk_swapping vs1 vs2) l
                     ++ f
                     ++ all_fo_vars (so_swap (mk_swapping vs1 vs2) s)
                     ++ all_fo_vars (fo_change_bvars_alpha vs (mk_swapping (l ++ vs1) (f ++ vs2)) s)
                     ++ all_fo_vars (so_swap (mk_swapping (l ++ vs1) (f ++ vs2)) s)
                     ++ all_fo_vars s)) as h; exrepnd.
    apply (soaeqbt [] lvn); simpl; auto; try lia.

    + rw length_swapbvars; auto.

    + allrw disjoint_app_r; sp; eauto with slow.

    + pose proof (ind s l i3 vs (l ++ vs1) (f ++ vs2)) as h.
      repeat (autodimp h hyp); auto.

      * allrw length_app; lia.

      * allrw disjoint_app_r; allrw disjoint_app_l; sp; eauto with slow.
        {
          rw disjoint_flat_map_r in disj3.
          apply disj3 in i3; simpl in i3; rw disjoint_app_r in i3; sp.
        }
        {
          pose proof (foren_vars_mk_swapping vs1 vs2) as eqv;
          autodimp eqv hyp.
          eapply subvars_disjoint_r;[|exact Heqf1].
          apply eqvars_sym in eqv.
          eapply subvars_eqvars_r;[|exact eqv].
          apply subvars_app_weak_l; auto.
        }

      * allrw disjoint_app_r; allrw disjoint_app_l; sp; eauto with slow.

      * allrw disjoint_app_r; allrw disjoint_app_l; sp; eauto with slow.
        rw disjoint_flat_map_r in disj3.
        apply disj3 in i3; simpl in i3; rw disjoint_app_r in i3; sp.

      * rw no_repeats_app; sp.
        allrw disjoint_app_r; sp.
        pose proof (foren_vars_mk_swapping vs1 vs2) as eqv;
          autodimp eqv hyp.
        eapply subvars_disjoint_r;[|exact Heqf1].
        apply eqvars_sym in eqv.
        eapply subvars_eqvars_r;[|exact eqv].
        apply subvars_app_weak_r; auto.

      * pose proof (so_alphaeq_add_so_swap2
                      f lvn
                      (so_swap (mk_swapping (l ++ vs1) (f ++ vs2)) s)
                      (fo_change_bvars_alpha vs (mk_swapping (l ++ vs1) (f ++ vs2)) s)
                   ) as k.
        repeat (autodimp k hyp); try lia.

        {
          allrw disjoint_app_r; sp.
        }

        eapply so_alphaeq_trans;[|exact k]; clear h k.

        allrw @so_swap_so_swap.
        repeat (rw mk_swapping_app;[|auto; allrw length_app; complete sp]).
        rw <- @so_swap_app_so_swap;
          try (complete (allrw disjoint_app_r; sp; eauto with slow));
          try (complete (allrw disjoint_flat_map_r;
                         apply disj3 in i3; simpl in i3;
                         rw disjoint_app_r in i3; sp; eauto with slow)).

        allrw <- app_assoc.
        rw @so_swap_disj_chain2; auto; try lia; eauto with slow;
          try (complete (allrw disjoint_app_r; sp; eauto with slow));
          try (complete (allrw disjoint_flat_map_r;
                         apply disj3 in i3; simpl in i3;
                         rw disjoint_app_r in i3; sp; eauto with slow)).

        {
          allrw disjoint_app_r; repnd.
          pose proof (foren_vars_mk_swapping vs1 vs2) as eqv;
            autodimp eqv hyp.
          eapply subvars_disjoint_r;[|exact Heqf1].
          apply eqvars_sym in eqv.
          eapply subvars_eqvars_r;[|exact eqv].
          apply subvars_app_weak_l; auto.
        }

        {
          allrw disjoint_app_r; repnd.
          pose proof (foren_vars_mk_swapping vs1 vs2) as eqv;
            autodimp eqv hyp.
          eapply subvars_disjoint_r;[|exact Heqf1].
          apply eqvars_sym in eqv.
          eapply subvars_eqvars_r;[|exact eqv].
          apply subvars_app_weak_r; auto.
        }
Qed.

Lemma swapbvars_nil_l :
  forall l, swapbvars [] l = l.
Proof.
  induction l; allsimpl; auto.
  rw IHl; auto.
Qed.

Lemma so_swap_nil {o} :
  forall t : @SOTerm o, so_swap [] t = t.
Proof.
  soterm_ind t as [v ts ind | op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    boolvar; subst; auto.
    f_equal.
    apply eq_map_l; auto.

  - Case "soterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    rw swapbvars_nil_l; f_equal.
    eapply ind; eauto.
Qed.

Lemma so_alphaeq_fo_change_bvars_alpha2 {o} :
  forall (t : @SOTerm o) vs,
    so_alphaeq t (fo_change_bvars_alpha vs [] t).
Proof.
  introv.
  pose proof (so_alphaeq_fo_change_bvars_alpha t vs [] []) as h.
  repeat (autodimp h hyp).
  allsimpl; rw @so_swap_nil in h; auto.
Qed.

Lemma fo_bound_vars_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) vs ren,
    disjoint vs (fo_bound_vars (fo_change_bvars_alpha vs ren t)).
Proof.
  soterm_ind t as [v ts ind | op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw disjoint_flat_map_r; introv i.
    allrw in_map_iff; exrepnd; subst; auto.

  - Case "soterm".
    rw disjoint_flat_map_r; introv i.
    allrw in_map_iff; exrepnd; subst.
    destruct a; simpl.
    gen_fresh; allrw disjoint_app_r; repnd; dands; eauto with slow.
Qed.

Lemma fo_bound_vars_fo_change_bvars_alpha2 {o} :
  forall (t : @SOTerm o) vs1 vs2 ren,
    subvars vs1 vs2
    -> disjoint vs1 (fo_bound_vars (fo_change_bvars_alpha vs2 ren t)).
Proof.
  introv sv.
  eapply subvars_disjoint_l; eauto.
  apply fo_bound_vars_fo_change_bvars_alpha.
Qed.

Lemma map_rename_sovar_nil :
  forall vs, map (rename_sovar []) vs = vs.
Proof.
  introv; apply eq_map_l; introv i.
  unfold rename_sovar; simpl; auto.
Qed.

Lemma cover_so_vars_fo_change_bvars_alpha {o} :
  forall (t : @SOTerm o) vs sub,
    cover_so_vars (fo_change_bvars_alpha vs [] t) sub
    <=> cover_so_vars t sub.
Proof.
  introv.
  unfold cover_so_vars.
  rw @so_free_vars_fo_change_bvars_alpha; simpl.
  rw map_rename_sovar_nil; sp.
Qed.

Lemma nth_map_sk_change_bvars_alpha {o} :
  forall (sks : list (@sosub_kind o)) vs n,
    nth n (map (sk_change_bvars_alpha vs) sks) default_sk
    = sk_change_bvars_alpha vs (nth n sks default_sk).
Proof.
  introv.
  assert (default_sk = sk_change_bvars_alpha vs (@default_sk o)) as e by auto.
  rw e; rw map_nth; clear e; auto.
Qed.

Inductive alphaeq_sosub {o} : @SOSub o -> @SOSub o -> Type :=
  | aeqsosub_nil : alphaeq_sosub [] []
  | aeqsosub_cons :
      forall v sk1 sk2 sub1 sub2,
        alphaeq_sk sk1 sk2
        -> alphaeq_sosub sub1 sub2
        -> alphaeq_sosub ((v,sk1) :: sub1) ((v,sk2) :: sub2).
Hint Constructors alphaeq_sosub.

Lemma sosub_as_combine {o} :
  forall sub : @SOSub o,
    sub = combine (so_dom sub) (so_range sub).
Proof.
  induction sub; simpl; auto.
  destruct a; simpl; rw <- IHsub; auto.
Qed.

Lemma sosub_change_bvars_alpha_spec {o} :
  forall vars (sub : @SOSub o),
    let sub' := sosub_change_bvars_alpha vars sub in
    disjoint vars (bound_vars_sosub sub')
    # alphaeq_sosub sub sub'.
Proof.
  induction sub; introv; allsimpl; repnd; dands; allsimpl; auto.
  - rw disjoint_app_r; dands; auto.
    apply disjoint_bound_vars_sk; auto.
  - constructor; auto.
    apply alphaeq_sk_change_bvars_alpha.
Qed.

Ltac sosub_change s :=
  match goal with
    | [ |- context[sosub_change_bvars_alpha ?vs ?sub] ] =>
      let h := fresh "h" in
      pose proof (sosub_change_bvars_alpha_spec vs sub) as h;
        simpl in h;
        remember (sosub_change_bvars_alpha vs sub) as s;
        clear_eq s (sosub_change_bvars_alpha vs sub);
        repnd
  end.

Lemma alphaeq_sosub_implies_eq_sodoms {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2 -> sodom sub1 = sodom sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp.
  - inversion aeq.
  - inversion aeq.
  - inversion aeq; subst; clear aeq.
    destruct sk1, sk2; f_equal; auto.
    allapply @alphaeq_sk_eq_length; allsimpl; sp.
Qed.

Lemma alphaeq_sosub_implies_eq_lengths {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2 -> length sub1 = length sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; inversion aeq; tcsp; cpx.
Qed.

Lemma alphaeq_sosub_implies_alphaeq_sk {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> bin_rel_sk alphaeq_sk (so_range sub1) (so_range sub2).
Proof.
  induction sub1; destruct sub2; introv aeq; allsimpl; tcsp.
  - unfold bin_rel_sk, binrel_list; simpl; sp.
  - inversion aeq.
  - inversion aeq.
  - inversion aeq; subst; clear aeq.
    simpl; apply bin_rel_sk_cons; dands; sp.
Qed.

Lemma alpha_eq_bterm_preserves_free_vars {o} :
  forall (bt1 bt2 : @BTerm o),
    alpha_eq_bterm bt1 bt2 -> free_vars_bterm bt1 = free_vars_bterm bt2.
Proof.
  introv aeq.
  pose proof (alphaeq_preserves_free_vars (oterm Exc [bt1]) (oterm Exc [bt2])) as h.
  simpl in h; allrw app_nil_r; apply h.
  constructor; simpl; auto.
  introv i; destruct n; cpx.
Qed.

Lemma alphaeq_sk_preserves_free_vars {o} :
  forall (sk1 sk2 : @sosub_kind o),
    alphaeq_sk sk1 sk2
    -> free_vars_sk sk1 = free_vars_sk sk2.
Proof.
  destruct sk1, sk2; introv aeq.
  apply alphaeq_sk_iff_alphaeq_bterm in aeq.
  apply alphaeqbt_eq in aeq.
  apply alpha_eq_bterm_preserves_free_vars in aeq; allsimpl; auto.
Qed.

Lemma alphaeq_sosub_preserves_free_vars {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> free_vars_sosub sub1 = free_vars_sosub sub2.
Proof.
  induction sub1; destruct sub2; introv aeq; inversion aeq; allsimpl; auto;
  subst; clear aeq.
  f_equal;[|apply IHsub1;auto].
  apply alphaeq_sk_preserves_free_vars; auto.
Qed.

Lemma alphaeq_sosub_trans {o} :
  forall (sub1 sub2 sub3 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> alphaeq_sosub sub2 sub3
    -> alphaeq_sosub sub1 sub3.
Proof.
  induction sub1; destruct sub2, sub3; introv aeq1 aeq2; tcsp;
  inversion aeq1; inversion aeq2; subst; cpx; clear aeq1 aeq2.
  constructor; eauto.
  eapply alphaeq_sk_trans; eauto.
Qed.
Hint Resolve alphaeq_sosub_trans : slow.

Lemma alphaeq_sosub_sym {o} :
  forall (sub1 sub2 : @SOSub o),
    alphaeq_sosub sub1 sub2
    -> alphaeq_sosub sub2 sub1.
Proof.
  induction sub1; destruct sub2; introv aeq; tcsp;
  inversion aeq; subst; cpx; clear aeq.
  constructor; eauto.
  eapply alphaeq_sk_sym; eauto.
Qed.
Hint Resolve alphaeq_sosub_sym : slow.

Lemma alphaeq_sosub_app {o} :
  forall (sub1 sub2 sub3 sub4 :@SOSub o),
    alphaeq_sosub sub1 sub2
    -> alphaeq_sosub sub3 sub4
    -> alphaeq_sosub (sub1 ++ sub3) (sub2 ++ sub4).
Proof.
  induction sub1; destruct sub2; introv aeq1 aeq2; tcsp;
  inversion aeq1; subst; clear aeq1; allsimpl.
  constructor; auto.
Qed.

Lemma alphaeq_sk_iff_alphaeq_bterm2 {o} :
  forall (sk1 sk2 : @sosub_kind o),
    alphaeq_sk sk1 sk2 <=> alpha_eq_bterm (sk2bterm sk1) (sk2bterm sk2).
Proof.
  destruct sk1, sk2.
  pose proof (alphaeq_sk_iff_alphaeq_bterm l l0 n n0) as h; rw <- h.
  rw @alphaeqbt_eq; simpl; sp.
Qed.

Lemma alphaeq_sk_refl {o} :
  forall (sk : @sosub_kind o),
    alphaeq_sk sk sk.
Proof.
  introv.
  apply alphaeq_sk_iff_alphaeq_bterm2.
  apply alphaeqbt_refl.
Qed.

Lemma alphaeq_sosub_refl {o} :
  forall (sub :@SOSub o),
    alphaeq_sosub sub sub.
Proof.
  induction sub; auto.
  destruct a.
  constructor; auto.
  apply alphaeq_sk_refl.
Qed.
Hint Resolve alphaeq_sosub_refl : slow.

Lemma sosub_find_some_if_alphaeq_sosub {o} :
  forall (sub1 sub2 : @SOSub o) v sk,
    alphaeq_sosub sub1 sub2
    -> sosub_find sub1 v = Some sk
    -> {sk' : sosub_kind & alphaeq_sk sk sk' # sosub_find sub2 v = Some sk'}.
Proof.
  induction sub1; destruct sub2; introv aeq sf; allsimpl; tcsp.
  - inversion aeq.
  - destruct a, p; destruct s, s0.
    inversion aeq; subst; clear aeq.
    boolvar; subst; cpx.
    + eexists; dands; eauto.
    + allapply @alphaeq_sk_eq_length; allsimpl.
      destruct n; allrw; sp.
    + allapply @alphaeq_sk_eq_length; allsimpl.
      destruct n; allrw; sp.
Qed.

Lemma eqvars_allvars_sk {o} :
  forall (sk : @sosub_kind o),
    eqvars (allvars_sk sk)
           (free_vars_sk sk ++ bound_vars_sk sk).
Proof.
  destruct sk; simpl.
  rw eqvars_prop; introv; split; intro i;
  allrw in_app_iff; allrw in_remove_nvars.
  - destruct (in_deq _ deq_nvar x l); tcsp.
    dorn i; tcsp.
    pose proof (allvars_eq_all_vars n) as h; rw eqvars_prop in h; apply h in i.
    rw in_app_iff in i; tcsp.
  - dorn i; repnd.
    + right.
      pose proof (allvars_eq_all_vars n) as h; rw eqvars_prop in h; apply h.
      rw in_app_iff; sp.
    + dorn i; tcsp.
      right.
      pose proof (allvars_eq_all_vars n) as h; rw eqvars_prop in h; apply h.
      rw in_app_iff; sp.
Qed.

Lemma eqvars_allvars_range_sosub {o} :
  forall (sub : @SOSub o),
    eqvars
      (allvars_range_sosub sub)
      (free_vars_sosub sub ++ bound_vars_sosub sub).
Proof.
  induction sub; allsimpl; auto.
  pose proof (eqvars_allvars_sk (snd a)) as h; rw eqvars_prop in h.
  rw eqvars_prop in IHsub.
  rw eqvars_prop; introv; split; intro i; allrw in_app_iff.
  - dorn i.
    + apply h in i; allrw in_app_iff; sp.
    + apply IHsub in i; allrw in_app_iff; sp.
  - dorn i; dorn i.
    + left; apply h; allrw in_app_iff; sp.
    + right; apply IHsub; allrw in_app_iff; sp.
    + left; apply h; allrw in_app_iff; sp.
    + right; apply IHsub; allrw in_app_iff; sp.
Qed.

Lemma fo_change_bvars_alpha_spec {o} :
  forall vars (t : @SOTerm o),
    let t' := fo_change_bvars_alpha vars [] t in
    disjoint vars (fo_bound_vars t')
    # so_alphaeq t t'.
Proof.
  introv; simpl.
  pose proof (so_alphaeq_fo_change_bvars_alpha2 t vars) as h1.
  pose proof (fo_bound_vars_fo_change_bvars_alpha t vars []) as h2; sp.
Qed.

Ltac fo_change s :=
  match goal with
    | [ |- context[fo_change_bvars_alpha ?vs [] ?t] ] =>
      let h := fresh "h" in
      pose proof (fo_change_bvars_alpha_spec vs t) as h;
        simpl in h;
        remember (fo_change_bvars_alpha vs [] t) as s;
        clear_eq s (fo_change_bvars_alpha vs [] t);
        repnd
  end.

Lemma unfold_sosub {o} :
  forall (sub : @SOSub o) t,
    {sub' : SOSub
     & {t' : SOTerm
     & alphaeq_sosub sub sub'
     # so_alphaeq t t'
     # disjoint (fo_bound_vars t') (free_vars_sosub sub')
     # disjoint (free_vars_sosub sub') (bound_vars_sosub sub')
     # disjoint (all_fo_vars t') (bound_vars_sosub sub')
     # sosub sub t = sosub_aux sub' t'}}.
Proof.
  introv.
  unfold sosub; boolvar.

  - allrw disjoint_app_l; repnd.
    exists sub t; dands; auto.
    apply alphaeq_sosub_refl.

  - sosub_change sub'.

    applydup @alphaeq_sosub_preserves_free_vars in h as eqfv.
    pose proof (eqvars_allvars_range_sosub sub) as eqv.
    allrw disjoint_app_l; repnd.

    exists sub' t; dands; auto.

    * rw <- eqfv; auto.

    * rw <- eqfv.
      eapply subvars_disjoint_l;[|exact h1].
      eapply subvars_eqvars_r;[|apply eqvars_sym;exact eqv].
      apply subvars_app_weak_l; auto.

  - fo_change t'.
    allrw disjoint_app_l; repnd.

    exists sub t'; dands; eauto with slow.

  - sosub_change sub'.
    fo_change t'.
    allrw disjoint_app_l; repnd.

    applydup @alphaeq_sosub_preserves_free_vars in h as eqfv.
    pose proof (eqvars_allvars_range_sosub sub) as eqv.

    exists sub' t'; dands; eauto with slow.

    * rw <- eqfv; eauto with slow.

    * rw <- eqfv.
      eapply subvars_disjoint_l;[|exact h3].
      eapply subvars_eqvars_r;[|apply eqvars_sym;exact eqv].
      apply subvars_app_weak_l; auto.
Qed.

Lemma eq_sodoms_implies_eq_so_doms {o} :
  forall (sub1 sub2 : @SOSub o),
    sodom sub1 = sodom sub2 -> so_dom sub1 = so_dom sub2.
Proof.
  induction sub1; destruct sub2; introv e; allsimpl; tcsp.
  destruct a; destruct p; destruct s; destruct s0; cpx; allsimpl.
  f_equal.
  apply IHsub1; auto.
Qed.

Lemma sosub_aux_alpha_congr2 {p} :
  forall (t1 t2 : @SOTerm p) (sub1 sub2 : @SOSub p),
    so_alphaeq t1 t2
    -> disjoint (free_vars_sosub sub1) (fo_bound_vars t1)
    -> disjoint (free_vars_sosub sub2) (fo_bound_vars t2)
    -> disjoint (bound_vars_sosub sub1) (free_vars_sosub sub1 ++ fovars t1)
    -> disjoint (bound_vars_sosub sub2) (free_vars_sosub sub2 ++ fovars t2)
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> alphaeq_sosub sub1 sub2
    -> alphaeq (sosub_aux sub1 t1) (sosub_aux sub2 t2).
Proof.
  introv aeqt disj1 disj2 disj3 disj4 cov1 cov2 aeqs.
  pose proof (sosub_aux_alpha_congr
                t1 t2
                (so_dom sub1)
                (so_range sub1) (so_range sub2)) as h; simpl in h.

  allrw @length_so_dom.
  allrw @length_so_range.
  allrw <- @sosub_as_combine.
  applydup @alphaeq_sosub_implies_eq_sodoms in aeqs as ed1.
  applydup @eq_sodoms_implies_eq_so_doms in ed1 as ed2.
  rw ed2 in h.
  allrw <- @sosub_as_combine.

  repeat (autodimp h hyp).

  - apply alphaeq_sosub_implies_eq_lengths; auto.

  - apply alphaeq_sosub_implies_alphaeq_sk; auto.
Qed.

Lemma so_alphaeq_sym {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2 -> so_alphaeq t2 t1.
Proof.
  introv aeq.
  apply so_alphaeq_vs_sym; auto.
Qed.
Hint Resolve so_alphaeq_sym : slow.
Hint Resolve so_alphaeq_trans : slow.
Hint Resolve so_alphaeq_refl : slow.

Lemma cover_so_vars_if_alphaeq_sosub {o} :
  forall (t : @SOTerm o) sub1 sub2,
    cover_so_vars t sub1
    -> alphaeq_sosub sub1 sub2
    -> cover_so_vars t sub2.
Proof.
  introv cov aeq.
  allunfold @cover_so_vars.
  apply alphaeq_sosub_implies_eq_sodoms in aeq; rw <- aeq; auto.
Qed.
Hint Resolve cover_so_vars_if_alphaeq_sosub : slow.

Fixpoint swap_fo_vars (s : swapping) (vs : list sovar_sig) :=
  match vs with
    | [] => []
    | (v,0) :: vs => (swapvar s v,0) :: swap_fo_vars s vs
    | (v,n) :: vs => (v,n) :: swap_fo_vars s vs
  end.

Lemma swap_fo_vars_app :
  forall (l1 l2 : list sovar_sig) s,
    swap_fo_vars s (l1 ++ l2)
    = swap_fo_vars s l1 ++ swap_fo_vars s l2.
Proof.
  induction l1; introv; allsimpl; auto.
  destruct a; destruct n0; simpl; rw IHl1; auto.
Qed.

Lemma swap_fo_vars_flat_map :
  forall {A} (l : list A) (f : A -> list sovar_sig) s,
    swap_fo_vars s (flat_map f l) = flat_map (fun a => swap_fo_vars s (f a)) l.
Proof.
  induction l; introv; allsimpl; auto.
  rw swap_fo_vars_app; rw IHl; auto.
Qed.

Lemma swap_fo_vars_implies_remove_fo_vars :
  forall vs1 vs2 vs l1 l2,
    no_repeats vs
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs (sovars2vars l1)
    -> disjoint vs (sovars2vars l2)
    -> length vs1 = length vs
    -> length vs2 = length vs
    -> swap_fo_vars (mk_swapping vs1 vs) l1 = swap_fo_vars (mk_swapping vs2 vs) l2
    -> remove_so_vars (vars2sovars vs1) l1 = remove_so_vars (vars2sovars vs2) l2.
Proof.
  induction l1; destruct l2;
  introv norep disj1 disj2 disj3 disj4 len1 len2 e;
  allsimpl; auto;
  allrw remove_so_vars_nil_r; allrw remove_so_vars_cons_r; auto.

  - destruct s; destruct n0; cpx.

  - destruct a; destruct n0; cpx.

  - allrw disjoint_cons_r; repnd.
    destruct a, s.
    destruct n0, n2.
    inversion e as [e1].
    allsimpl; boolvar; auto.

    + provefalse.
      allrw in_map_iff; exrepnd.
      allunfold var2sovar; cpx.
      pose proof (swapvar_in vs1 vs a) as h;
        repeat (autodimp h hyp);
        try (complete (apply disjoint_sym; auto)).
      assert (LIn (swapvar (mk_swapping vs2 vs) n1) vs) as k by (allrw <-; auto).
      pose proof (swapvar_implies2 vs2 vs n1) as x; simpl in x; dorn x;[|dorn x]; tcsp.
      * rw x in k; sp.
      * destruct n0; eexists; eauto.

    + provefalse.
      allrw in_map_iff; exrepnd.
      allunfold var2sovar; cpx.
      pose proof (swapvar_in vs2 vs a) as h;
        repeat (autodimp h hyp);
        try (complete (apply disjoint_sym; auto)).
      assert (LIn (swapvar (mk_swapping vs1 vs) n) vs) as k by (allrw; auto).
      pose proof (swapvar_implies2 vs1 vs n) as x; simpl in x; dorn x;[|dorn x]; tcsp.
      * rw x in k; sp.
      * destruct n0; eexists; eauto.

    + rw (IHl1 l2); auto; f_equal; f_equal.
      allrw in_map_iff; allunfold var2sovar.
      rw swapvar_not_in in e1; auto;[|introv k; destruct n0; eexists; complete eauto].
      rw swapvar_not_in in e1; auto.
      introv k; destruct n2; eexists; complete eauto.

    + boolvar; allsimpl; cpx.

    + boolvar; allsimpl; cpx.

    + boolvar; allsimpl; cpx.
      * provefalse.
        allrw in_map_iff; exrepnd.
        allunfold var2sovar; cpx.
      * provefalse.
        allrw in_map_iff; exrepnd.
        allunfold var2sovar; cpx.
      * f_equal; auto.
Qed.

Lemma so_free_vars_so_swap {o} :
  forall vs1 vs2 (t : @SOTerm o),
    no_repeats vs2
    -> disjoint vs1 vs2
    -> so_free_vars (so_swap (mk_swapping vs1 vs2) t)
       = swap_fo_vars (mk_swapping vs1 vs2) (so_free_vars t).
Proof.
  soterm_ind t as [v ts ind | op bs ind] Case;
  introv norep disj; allsimpl; tcsp.

  - Case "sovar".
    boolvar; subst; allsimpl; auto.
    rw <- length0 in n.
    remember (length ts) as l; destruct l; cpx.
    rw map_length; f_equal; auto.
    rw flat_map_map; unfold compose.
    rw @swap_fo_vars_flat_map.
    apply eq_flat_maps; introv i.
    apply ind; auto.

  - Case "soterm".
    rw flat_map_map; unfold compose.
    rw @swap_fo_vars_flat_map.
    apply eq_flat_maps; introv i; destruct x; simpl.
    rw (ind s l); auto.
    remember (so_free_vars s) as vars; clear Heqvars.

    induction vars; simpl; auto.
    + allrw remove_so_vars_nil_r; simpl; auto.
    + destruct a; destruct n0; simpl.
      * allrw remove_so_vars_cons_r; simpl.
        boolvar; allrw in_map_iff; exrepnd; cpx; allsimpl; auto.
        { unfold var2sovar in l1; cpx.
          allrw in_swapbvars; exrepnd.
          apply swapvars_eq in l1; auto; subst.
          provefalse.
          destruct n0; eexists; eauto. }
        { allunfold var2sovar; cpx.
          provefalse.
          destruct n0.
          eexists; dands; eauto.
          rw in_swapbvars; eexists; eauto. }
        { rw IHvars; auto. }
      * allrw remove_so_vars_cons_r; simpl; boolvar; simpl; auto.
        { allrw in_map_iff; exrepnd.
          allunfold var2sovar; cpx. }
        { allrw in_map_iff; exrepnd.
          allunfold var2sovar; cpx. }
        { rw IHvars; auto. }
Qed.

Lemma so_alphaeq_preserves_free_vars {o} :
  forall (t1 t2 : @SOTerm o),
    so_alphaeq t1 t2
    -> so_free_vars t1 = so_free_vars t2.
Proof.
  soterm_ind1s t1 as [v1 ts1 ind1 | op1 bs1 ind1] Case; introv aeq; tcsp.

  - Case "sovar".
    inversion aeq as [? ? ? len imp |]; subst; clear aeq.
    simpl; rw len; f_equal.
    apply eq_flat_maps_diff; auto.
    introv i.
    applydup imp in i.
    apply ind1 in i0; auto.
    apply in_combine in i; sp.

  - Case "soterm".
    inversion aeq as [|? ? ? len imp]; subst; clear aeq; simpl.
    apply eq_flat_maps_diff; auto.
    intros b1 b2 i.
    applydup imp in i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    simpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep a]; subst.
    applydup in_combine in i; repnd.
    apply (ind1 t1 _ l1) in a; auto; allrw @sosize_so_swap; auto.

    allsimpl; allrw disjoint_app_r; repnd.

    rw @so_free_vars_so_swap in a; eauto with slow.
    rw @so_free_vars_so_swap in a; eauto with slow.

    apply swap_fo_vars_implies_remove_fo_vars in a; auto.

    + eapply subvars_disjoint_r;[|exact disj2].
      apply sovars2vars_so_free_vars_subvars_all_fo_vars.

    + eapply subvars_disjoint_r;[|exact disj].
      apply sovars2vars_so_free_vars_subvars_all_fo_vars.
Qed.

Lemma cover_so_vars_if_so_alphaeq {o} :
  forall (t1 t2 : @SOTerm o) sub,
    cover_so_vars t1 sub
    -> so_alphaeq t1 t2
    -> cover_so_vars t2 sub.
Proof.
  introv cov aeq.
  allunfold @cover_so_vars.
  apply so_alphaeq_preserves_free_vars in aeq.
  rw <- aeq; auto.
Qed.
Hint Resolve cover_so_vars_if_so_alphaeq : slow.

Lemma alphaeq_sosub_combine {o} :
  forall vs (sks1 sks2 : list (@sosub_kind o)),
    length vs = length sks1
    -> length vs = length sks2
    -> (alphaeq_sosub (combine vs sks1) (combine vs sks2)
        <=> bin_rel_sk alphaeq_sk sks1 sks2).
Proof.
  induction vs; destruct sks1, sks2; introv len1 len2; split; intro k;
  repnd; dands; allsimpl; tcsp; cpx.
  - constructor; simpl; sp.
  - inversion k; subst.
    apply bin_rel_sk_cons; sp.
    apply IHvs; sp.
  - allrw @bin_rel_sk_cons; repnd.
    constructor; sp.
    apply IHvs; sp.
Qed.

Lemma sosub_alpha_congr {p} :
  forall (t1 t2 : @SOTerm p) (vs : list NVar) (ts1 ts2 : list sosub_kind),
    so_alphaeq t1 t2
    -> length vs = length ts1
    -> length vs = length ts2
    -> cover_so_vars t1 (combine vs ts1)
    -> cover_so_vars t2 (combine vs ts2)
    -> bin_rel_sk alphaeq_sk ts1 ts2
    -> alphaeq (sosub (combine vs ts1) t1) (sosub (combine vs ts2) t2).
Proof.
  introv Hal H1l H2l cov1 cov2 Hbr.
  pose proof (fovars_subvars_all_fo_vars t1) as sv1.
  pose proof (fovars_subvars_all_fo_vars t2) as sv2.

  pose proof (unfold_sosub (combine vs ts1) t1) as h1.
  pose proof (unfold_sosub (combine vs ts2) t2) as k1.
  exrepnd.
  rw h1; rw k1.

  apply sosub_aux_alpha_congr2; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.
    pose proof (fovars_subvars_all_fo_vars t'0) as h.
    eapply subvars_disjoint_r;[exact h|]; eauto with slow.

  - rw disjoint_app_r; dands; eauto with slow.
    pose proof (fovars_subvars_all_fo_vars t') as h.
    eapply subvars_disjoint_r;[exact h|]; eauto with slow.

  - eapply alphaeq_sosub_trans;[|exact k0].
    eapply alphaeq_sosub_trans;[apply alphaeq_sosub_sym;exact h0|].
    apply alphaeq_sosub_combine; auto.
Qed.

Lemma sosub_alpha_congr2 {o} :
  forall (t1 t2 : @SOTerm o) (sub1 sub2 : @SOSub o),
    so_alphaeq t1 t2
    -> alphaeq_sosub sub1 sub2
    -> cover_so_vars t1 sub1
    -> cover_so_vars t2 sub2
    -> alphaeq (sosub sub1 t1) (sosub sub2 t2).
Proof.
  introv aeqt aeqs cov1 cov2.
  rw (sosub_as_combine sub1).
  rw (sosub_as_combine sub2).
  applydup @alphaeq_sosub_implies_eq_sodoms in aeqs as ed1.
  applydup @eq_sodoms_implies_eq_so_doms in ed1 as ed2.
  rw ed2.
  apply sosub_alpha_congr; auto.

  - rw <- ed2.
    rw @length_so_dom; rw @length_so_range; auto.

  - rw @length_so_dom; rw @length_so_range; auto.

  - rw <- ed2.
    rw <- @sosub_as_combine; auto.

  - rw <- @sosub_as_combine; auto.

  - apply alphaeq_sosub_implies_alphaeq_sk; auto.
Qed.
