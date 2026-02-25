Require Export list.

Hint Rewrite diff_nil : fast.
Set Implicit Arguments.
Section AssociationList.
Variables Key Value : Type.
Definition AssocList : Type := list (Key * Value).
Definition ALDom : AssocList -> list Key := map (fun x => fst x).
Definition ALRange : AssocList -> list Value := map (fun x => snd x).

Theorem ALDomCombine :
  forall lv lnt,
    length lv = length lnt
    -> ALDom (combine lv lnt) = lv.
Proof.
  induction lv; sp; simpl; destruct lnt; allsimpl; sp; try lia.
  f_equal; auto.
Qed.

Theorem ALRangeCombine :
  forall lv lnt,
    length lv = length lnt
    -> ALRange (combine lv lnt) = lnt.
Proof.
  induction lv; sp; simpl; destruct lnt; allsimpl; sp; try lia.
  f_equal; auto.
Qed.

Lemma ALInEta : forall sub v t,
  LIn (v,t) sub -> (LIn v (ALDom sub)) # (LIn t (ALRange sub)).
Proof.
  induction sub as [| ? Hind]; introv Hin; auto.
  allsimpl. dorn Hin; subst; auto;[].
  apply IHHind in Hin. repnd.
  split; right; auto.
Qed.

Definition ALMap {TK TV : Type} 
  (fk : Key -> TK)
  (fv : Value -> TV) (al : AssocList):=
map (fun p => (fk (fst p), fv (snd p))) al.

Definition ALMapRange {T : Type} (f : Value -> T) (al : AssocList):=
ALMap (fun x=>x) f al.

Variable DeqKey : (Deq Key).
(** All definitions/lemmas below need decidable equality on Key.
    If not, they should placed before the line above *)
Fixpoint ALFind 
    (al : AssocList) (key : Key): option Value :=
match al with
| nil => None
| (k, v) :: xs => if DeqKey key k 
                  then Some v 
                  else ALFind xs key
end.

Definition ALFindDef 
    (al : AssocList) (key : Key) (def: Value):  Value :=
match (ALFind al key) with
| Some v => v
| None => def
end.

(** Same as [AlFind] above, but the output contains proofs of
    correctness. *)
Lemma ALFind2 :
  forall  (sub: AssocList) (a : Key) ,
    { b: Value & LIn (a,b) sub}
    + !(LIn a (ALDom sub)).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - destruct (DeqKey a a') as [Hc|Hc]; subst.
      + left. exists b'. left; refl.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. right; auto.
          * intro Hf. apply Hr. simpl in Hf. destruct (split sub).
              dorn Hf; sp.
Defined.

Definition ALFindDef2 
    (al : AssocList) (key : Key) (def: Value):  Value :=
match (ALFind2 al key) with
| inl (existT _  v _) => v
| inr _ => def
end.

(** In proofs, it is often convenient to replace
  [ALFindDef] with [ALFindDef2] so that we get some
  correctness hypotheses for free on destruction*)
Lemma ALFindDef2Same : forall
  (key : Key) (def: Value) (al : AssocList),
  ALFindDef al key def=ALFindDef2 al key def.
Proof.
  induction al as [|h th Hind]; auto;[]. destruct h as [k v].
  allunfold ALFindDef. allunfold ALFindDef2.
  simpl. cases_ifd Hd; auto.
  - rw Hdt; auto.
  - unfold ALFindDef2 in Hind.
    rw  Hind.  destruct_head_match; simpl; auto.
    destruct s; auto.
Qed.

Fixpoint ALFilter (sub : AssocList) (keys : list Key) : AssocList :=
  match sub with
  | nil => nil
  | (k, v) :: xs =>
      if (in_deq _ DeqKey k keys)
      then ALFilter xs keys
      else (k, v) :: ALFilter xs keys
  end.

Lemma ALFilter_nil_r :
  forall sub, ALFilter sub [] = sub.
Proof.
  induction sub; simpl; sp.
  rewrite IHsub; auto.
Qed.


Lemma ALDomFilterCommute :
  forall l sub,
    diff DeqKey l (ALDom sub) = ALDom (ALFilter sub l).
Proof.
  induction sub; simpl; sp; allsimpl.
  - apply diff_nil.
  - rewrite diff_cons_r.
    rw memberb_din.
    cases_if; simpl; f_equal; auto.
Qed.

Lemma ALFindSome :
  forall sub : AssocList,
  forall v : Key,
  forall u : Value,
    ALFind sub v = Some u
    -> LIn (v, u) sub.
Proof.
  induction sub; simpl; sp.
  inversion H.
  destruct (DeqKey v a0); cpx.
Qed.

Lemma ALFindNone :
  forall sub v,
    ALFind sub v = None
    -> ! LIn v (ALDom sub).
Proof.
  induction sub; simpl; sp;
  inversion H;
  destruct (DeqKey v a0); cpx.
  apply IHsub in H1. cpx.
Qed.

Lemma ALFindFilterSome :
  forall l v t sub,
    (ALFind (ALFilter sub l) v = Some t)
    <=> (ALFind sub v = Some t # ! LIn v l).
Proof.
  induction sub; simpl; sp; split; introv H; sp; allsimpl.
  - destruct (in_deq Key DeqKey a0 l); allsimpl.
    + rw IHsub in H; sp;case_if as Hd; subst;auto; try contradiction.
    + case_if as Hd; subst; auto; try contradiction.
      rw IHsub in H; exrepnd; auto.
  
  - destruct (in_deq Key DeqKey a0 l); allsimpl.
    + apply IHsub in H; exrepnd; auto.
    + destruct (DeqKey v a0); allsimpl; subst; sp;[].
      rw IHsub in H; exrepnd; auto.

  - destruct (in_deq Key DeqKey a0 l); allsimpl.
    + apply IHsub; split; auto.
      destruct (DeqKey v a0); allsimpl; subst; sp.

    + destruct (DeqKey v a0); allsimpl; subst; sp.
       apply IHsub; split; auto.
Qed.

Lemma ALFindFilterNone :
  forall l v sub,
    (ALFind (ALFilter sub l) v = None)
    <=> (ALFind sub v = None [+] LIn v l).
  induction sub; simpl; sp; split; introv H; sp; allsimpl.
  - destruct (in_deq Key DeqKey a0 l); allsimpl;
    destruct (DeqKey v a0) as [ddd | ddd]; allsimpl;
    subst;
    try(rw IHsub in H); 
    exrepnd; auto;cpx.
  - destruct (in_deq Key DeqKey a0 l); allsimpl;
    destruct (DeqKey v a0) as [ddd | ddd]; allsimpl;
    subst;cpx;apply IHsub; cpx.
  - destruct (in_deq Key DeqKey a0 l); allsimpl;
    destruct (DeqKey v a0) as [ddd | ddd]; allsimpl;
    subst;cpx;apply IHsub; cpx.
Qed.

Lemma ALFilterSwap :
  forall l1 l2 sub,
    ALFilter (ALFilter sub l1) l2
    = ALFilter (ALFilter sub l2) l1.
Proof.
  induction sub; simpl; sp.
  allsimpl; cases_if as H1d; cases_if as H2d;
  allsimpl; try (rw H1d); try (rw H2d);
  cpx; try (rw IHsub); cpx.
Qed.

Lemma ALFilterAppR :
  forall sub vs1 vs2,
    ALFilter sub (vs1 ++ vs2)
    = ALFilter (ALFilter sub vs1) vs2.
Proof.
  induction sub; simpl; sp.
  rw <- memberb_din.
  rw <- memberb_din.
  rw memberb_app.
  destructr (memberb DeqKey a0 vs1) as [m1 | m1]; simpl.
  apply IHsub.
  rw <- memberb_din.
  allsimpl. destruct (memberb DeqKey a0 vs2) as [m2 | m2];
  simpl; subst;
  try(rw IHsub); auto.
Qed.

Lemma ALFilterAppAsDiff :
  forall sub l1 l2,
    ALFilter sub (l1 ++ l2)
    = ALFilter sub (l1 ++ diff DeqKey l1 l2).
Proof.
  induction sub; simpl; sp; allsimpl;[].
  cases_ifd  Hd; cases_ifd  Hdd; cpx;
  allrw in_app_iff;
  allrw in_diff.
  - provefalse. apply Hddf.
    dorn Hdt; cpx;[].
    pose proof (in_deq _ DeqKey a0 l1) as X.
    dorn X; cpx.
  - provefalse. apply Hdf.
    dorn Hddt; exrepnd; cpx.
  - f_equal. auto.
Qed.

(** [lv] is needs to make the induction
    hypothesis strong enough *)
Lemma ALFilterDom : forall  sub lv,
  ALFilter sub (lv++ALDom sub) =[].
Proof.
  induction sub as [|(v,u) sub Hind] ; introv ; auto;[].
  allsimpl.
  cases_ifd Hd; cpx; allsimpl; allrw in_app_iff;
  cpx.
  - rw cons_as_app. rw app_assoc. rw Hind; auto.
  - provefalse. apply Hdf. right. cpx.
Qed.

Fixpoint ALKeepFirst (sub : AssocList) (vars : list Key) : AssocList :=
match sub with
| nil => nil
| (v, t) :: xs =>
    if in_deq _ DeqKey v vars
    then (v, t) :: ALKeepFirst
                   xs 
                   (diff DeqKey [v] vars)
    else ALKeepFirst xs vars
end.

Lemma ALKeepFirstNil :
  forall sub,
    ALKeepFirst sub [] = [].
Proof.
  induction sub; simpl; sp.
Qed.


Lemma ALFindSomeKeepFirstSingleton:
  forall sub v t,
    ALFind sub v = Some t
    -> ALKeepFirst sub [v] = [(v,t)].
Proof.
  induction sub as [|(v,t) sub Hind];
  introv Heq; allsimpl; cpx.
  destruct (DeqKey v0 v) as [xx|xx];
  subst;allsimpl; cpx;[].
  rewrite DeqTrue.
  rw ALKeepFirstNil; auto.
Qed.

Lemma ALFindNoneKeepFirstSingleton:
  forall sub v,
    ALFind sub v = None
    -> ALKeepFirst sub [v] = [].
Proof.
  induction sub as [|(v,t) sub Hind];
  introv Heq; allsimpl; cpx.
  destruct (DeqKey v0 v) as [xx|xx];
  subst;allsimpl; cpx.
Qed.
Hint Rewrite ALKeepFirstNil ALFilterDom ALFilter_nil_r : fast.

Lemma ALKeepFirstLin:
  forall sub v vs t,
    LIn (v,t) (ALKeepFirst sub vs)
    <=> (ALFind sub v = Some t # LIn v vs).
Proof.
  induction sub; simpl; sp;[split;sp|].
  destruct (DeqKey v a0);
  destruct (in_deq Key DeqKey a0 vs);
  subst; cpx; split; introns Hyp; allsimpl; exrepnd; cpx.
  - dorn Hyp; cpx. apply IHsub in Hyp.
    exrepnd.
    apply in_remove in Hyp; cpx.
  - apply IHsub in Hyp; exrepnd; cpx.
  - dorn Hyp; cpx. apply IHsub in Hyp.
    exrepnd.
    apply in_remove in Hyp; cpx.
  - right. apply IHsub; dands; cpx.
    apply in_remove; dands; cpx.
Qed.

Lemma ALKeepFirstLinApp:
  forall sub v vs vss t,
    LIn (v,t) (ALKeepFirst sub (vs))
    -> LIn (v,t) (ALKeepFirst sub (vs++ vss)).
Proof.
  introv X.
  apply ALKeepFirstLin in X.
  apply ALKeepFirstLin.
  exrepnd; dands; auto.
  apply in_app_iff.
  cpx.
Qed.

Lemma ALFilterLIn :
  forall v t sub vars,
    LIn (v, t) (ALFilter sub vars)
    <=>
    (
      LIn (v, t) sub
      #
      ! LIn v vars
    ).
Proof.
  induction sub; simpl; sp.
  split; sp. cases_if;
  simpl; allrw; split; sp; cpx.
  contradiction.
Qed.

Lemma ALFilterSubset :
  forall sub vars,
    subset (ALFilter sub vars) sub.
Proof.
  introv Hin.
  destruct x;
  rw ALFilterLIn in Hin; cpx.
Qed.

Lemma ALKeepFirstSubst :
  forall sub vars,
    subset (ALKeepFirst sub vars) sub.
Proof.
  introv Hin.
  destruct x;
  rw ALKeepFirstLin in Hin; exrepnd;
  cpx.
  apply ALFindSome; cpx.
Qed.

Hint Resolve ALFilterSubset ALKeepFirstSubst :
  SetReasoning.

Lemma ALKeepFirstAppLin:
  forall lv1 lv2 sub v u,
  LIn (v,u) (ALKeepFirst sub (lv1++lv2))
  -> LIn (v,u) (ALKeepFirst sub lv1) [+]
     LIn (v,u) (ALKeepFirst sub lv2). 
Proof. introv Hin.
  apply ALKeepFirstLin in Hin.
  repnd.
  apply in_app_iff in Hin. dorn Hin;[left|right];
  apply ALKeepFirstLin;sp.
Qed.

Lemma ALKeepFirstFilterDiff:
forall sub lvk lvf,
  (ALKeepFirst  sub (diff DeqKey lvf lvk))
  = 
  (ALKeepFirst (ALFilter sub lvf) lvk).
Proof.
  induction sub; allsimpl;
  autorewrite with fast; cpx;[].
  intros. allsimpl.
  destruct a.
  cases_ifd H1d; cases_ifd H2d;
   allrw in_diff; exrepnd; allsimpl; cpx.
  - cases_ifd H3d; cpx. f_equal.
    rw <- diff_remove. apply IHsub.
  - cases_ifd H3d; cpx. provefalse.
    apply H1df. dands;cpx.
Qed.


Lemma ALFilterAppSub :
  forall sub1 sub2 l,
  ALFilter (sub1++sub2) l
  = (ALFilter sub1 l)++(ALFilter sub2 l).
Proof.
  induction sub1; simpl; sp;[].
  rw IHsub1.
  cases_ifd Hd; cpx.
Qed.

Lemma ALFindApp :
  forall v sub1 sub2,
    ALFind (sub1 ++ sub2) v
    = match ALFind sub1 v with
        | Some t => Some t
        | None => ALFind sub2 v
      end.
Proof.
  induction sub1; simpl; sp.
  cases_if; auto.
Qed.


Lemma ALFindRangeMapSome :
  forall v t sub f,
    ALFind sub v = Some t
    -> ALFind (ALMapRange f sub) v 
        = Some (f t).
Proof.
  induction sub; simpl; sp; allsimpl;[].
  cases_ifd Hd; cpx.
Qed.
  
Lemma ALFindRangeMapNone :
  forall v sub f,
    ALFind sub v = None
    -> ALFind (ALMapRange f sub) v = None.
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_ifd Hd; cpx.
Qed.

Fixpoint ALRangeRel  (R : Value -> Value-> [univ]) 
    (subl subr : AssocList) : [univ] :=
match (subl, subr) with 
| ([],[]) => True
| ((vl,tl) :: sl , (vr,tr) :: sr) => (vl=vr # R tl tr # ALRangeRel R sl sr)
| ( _ , _) => False
end.


Lemma ALRangeRelApp : forall R subl1 subl2 subr1 subr2,
  (ALRangeRel  R subl1 subl2 # ALRangeRel R subr1 subr2)
  ->   ALRangeRel R (subl1 ++ subr1)  (subl2 ++ subr2).
Proof.
  induction subl1 as [|(v1,t1) subl1 Hind]; introv Hsr;
  destruct subl2 as [|(v2,t2) subl2]; inverts Hsr; allsimpl;sp.
Qed.

Lemma ALRangeRelRefl : forall R,
  refl_rel R -> refl_rel (ALRangeRel R).
Proof.
  introv Hr. unfold refl_rel in Hr. unfold refl_rel.
  induction x as [|(v1,t1) subl1 Hind];  allsimpl;sp.
Qed.
  
Lemma ALRangeRelSameDom : forall R 
  (subl subr : AssocList),
  ALRangeRel R subl subr
  -> ALDom subl = ALDom subr.
Proof.
  induction subl as [| (kl,vl) subl Hind]; introv Hal;
  destruct subr as [| (kr,vr) subr]; allsimpl; repnd; dands; cpx.
  f_equal; cpx.
Qed.

Lemma ALRangeRelFind : forall R 
  (subl subr : AssocList) k t,
  ALRangeRel R subl subr
  -> ALFind subl k = Some t
  -> { tr : Value & ALFind subr k = Some tr # R t tr}.
Proof.
  induction subl as [| (kl,vl) subl Hind]; cpx; introv HAl Hf.
  allsimpl. destruct subr as [| (kr,vr) subr]; cpx;[].
  allsimpl. repnd. subst.
  cases_ifd Hd; cpx.
  eexists; eauto.
Qed.

Lemma ALRangeRelFilter : forall R 
  (subl subr : AssocList) l,
  ALRangeRel R subl subr
  ->  ALRangeRel R
        (ALFilter  subl l) 
        (ALFilter  subr l).
Proof.
  induction subl as [| (kl,vl) subl Hind]; introv Hal;
  destruct subr as [| (kr,vr) subr]; allsimpl; repnd; dands; subst; cpx.
  cases_if; cpx.
Qed.

(* hints should be placed (again) after this line.
  the ones in the section get deactivated
 *)
End AssociationList.
Hint Rewrite ALKeepFirstNil ALFilterDom ALFilter_nil_r 
  ALRangeCombine ALDomCombine: fast.

Hint Resolve ALFilterSubset ALKeepFirstSubst :
  SetReasoning.

Definition ALSwitch {K V} (sub : AssocList K V)  : AssocList V K :=
  map (fun x => (snd x, fst x)) sub.

Lemma ALSwitchCombine : forall {K V} (lv: list V) (lk : list K) ,
  combine lv lk = ALSwitch (combine lk lv).
Proof.
  induction lv; allsimpl.
  - destruct lk; cpx.
  - destruct lk; cpx.
    allsimpl. f_equal. cpx.
Qed.

Lemma ALMapRangeFilterCommute :
  forall K V l T (deq : Deq K) (f: V -> T) (sub : AssocList K V),
  (ALFilter deq (ALMapRange f sub) l)  = ALMapRange f (ALFilter deq sub l).
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_if; simpl; auto; f_equal; auto.
Qed.

Lemma ALFindMapSome :
  forall {KA KB VA VB : Type} 
    (DKA : Deq KA)
    (DKB : Deq KB)
    (fk : KA -> KB)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v t, ALFind DKA sub v = Some t
  -> ALFind DKB (ALMap fk fv sub) (fk v) 
        = Some (fv t).
Proof.
  introv Hik.
  induction sub;simpl; introv Heq; sp; allsimpl;[].
  cases_ifd Hd; cpx.
  + f_equal. apply Hik in Hdt.
    destruct Hdt. rewrite DeqTrue in Heq.
    invertsn Heq. refl.
  + apply IHsub. revert Heq. cases_ifd Hdd;
    subst; cpx.
Qed.

Lemma ALFindMapNone :
  forall {KA KB VA VB : Type} 
    (DKA : Deq KA)
    (DKB : Deq KB)
    (fk : KA -> KB)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v, ALFind DKA sub v = None
  -> ALFind DKB (ALMap fk fv sub) (fk v) 
        = None.
Proof.
  introv Hik.
  induction sub;simpl; introv Heq; sp; allsimpl;[].
  cases_ifd Hd; cpx.
  + f_equal. apply Hik in Hdt.
    destruct Hdt. rewrite DeqTrue in Heq.
    invertsn Heq. 
  + apply IHsub. revert Heq. cases_ifd Hdd;
    subst; cpx.
Qed.

Lemma ALFindEndoMapSome :
  forall {KA VA VB: Type} 
    (DKA : Deq KA)
    (fk : KA -> KA)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v, ALFind DKA sub v = None
  -> ALFind DKA (ALMap fk fv sub) (fk v) 
        = None.
Proof.
  intros. eapply ALFindMapNone; eauto.
Qed.

Lemma ALMapFilterCommute :
  forall {KA KB VA VB : Type} 
  (DKA : Deq KA)
  (DKB : Deq KB)
  (fk : KA -> KB)
  (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) l,
      (ALFilter DKB (ALMap fk fv sub) (map fk l))  
          = ALMap fk fv (ALFilter DKA sub l).
Proof.
  introv Hin.
  induction sub; simpl; sp; allsimpl.
  cases_ifd Hd; cases_ifd Hc;
    simpl; auto; f_equal; auto.
  - apply in_map_iff in Hdt. exrepnd. apply Hin in Hdt0.
    subst. cpx.
  - rw in_map_iff in Hdf. provefalse.
    apply Hdf. eexists; eauto.
Qed.

(** endo maps avoid the need to provide another
    decider for keys *)
Lemma ALEndoMapFilterCommute :
  forall {KA VA VB : Type} 
  (DKA : Deq KA)
  (fk : KA -> KA)
  (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) l,
      (ALFilter DKA (ALMap fk fv sub) (map fk l))  
          = ALMap fk fv (ALFilter DKA sub l).
Proof.
  intros. apply ALMapFilterCommute; auto.
Qed.

Lemma ALMapRangeFindCommute :
  forall K V T (v: K) (deq : Deq K) (f: V -> T) (sub : AssocList K V),
  (ALFind deq (ALMapRange f sub) v)  = option_map f (ALFind deq sub v).
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_if; simpl; auto; f_equal; auto.
Qed.
