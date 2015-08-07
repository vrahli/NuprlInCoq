Require Export atoms.
Require Export library.
Require Export alphaeq2.
Require Export computation_mark.


Lemma get_utokens_lsubst_subset {o} :
  forall (t : @NTerm o) sub,
    subset
      (get_utokens (lsubst t sub))
      (get_utokens t ++ get_utokens_sub sub).
Proof.
  introv.
  pose proof (unfold_lsubst sub t) as h; exrepnd.
  rw h0.
  apply alphaeq_preserves_utokens in h1; rw h1.
  apply get_utokens_lsubst_aux_subset.
Qed.

Lemma reduces_to_preserves_utokens {o} :
  forall lib (t u : @NTerm o),
    nt_wf t
    -> reduces_to lib t u
    -> subset (get_utokens u) (get_utokens t).
Proof.
  introv wf r; unfold reduces_to in r; exrepnd; revert dependent t.
  induction k; introv wf r.
  - allrw @reduces_in_atmost_k_steps_0; subst; auto.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @preserve_nt_wf_compute_step in r1; auto.
    apply IHk in r0; auto.
    apply compute_step_preserves_utokens in r1; auto.
Qed.

Lemma get_utokens_sub_cons {o} :
  forall v t (sub : @Sub o),
    get_utokens_sub ((v,t) :: sub) = get_utokens t ++ get_utokens_sub sub.
Proof. sp. Qed.

Lemma get_utokens_sub_var_ren {o} :
  forall l1 l2,
    length l1 = length l2
    -> get_utokens_sub (@var_ren o l1 l2) = [].
Proof.
  introv len.
  unfold get_utokens_sub.
  rw @range_var_ren; auto.
  rw flat_map_map; unfold compose.
  clear dependent l1.
  induction l2; simpl; auto.
Qed.
