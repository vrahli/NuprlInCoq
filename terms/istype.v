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

  Authors: Abhishek Anand & Mark Bickford & Vincent Rahli

*)


Require Export csubst.


(**
  We can use  (T subtype_rel T) which is (\x.x in T -> T) to
  express the judgement that T is a type.

 *)
Definition mk_istype {o} (T : @NTerm o) :=
  mk_subtype_rel T T.
Definition mkc_istype {o} (T : @CTerm o) :=
  mkc_subtype_rel T T.

Lemma wf_mk_istype {p} : forall T : NTerm, wf_term (mk_istype T) <-> @wf_term  p T.
Proof.
  unfold mk_istype. intros. split; intro.
  rw @wf_subtype_rel_iff in H. exrepnd. auto.
  rw @wf_subtype_rel_iff . split; auto.
Qed.

Lemma cover_vars_mk_istype {p} :
  forall (T : NTerm) (s : CSub), cover_vars (@mk_istype p T) s <-> cover_vars T s.
Proof.
  unfold mk_istype. intros. split; intros.
  rw @cover_vars_subtype_rel in H. exrepnd. auto.
  rw @cover_vars_subtype_rel . split; auto.
Qed.

Lemma lsubstc_mk_istype {o} :
  (forall (T: @NTerm o)(s : CSub) (wf : wf_term (mk_istype T)) (c : cover_vars (mk_istype T) s),
    {w : wf_term T $
    {c': cover_vars T s $
      alphaeqc (lsubstc (mk_istype T) wf s c)  (mkc_istype (lsubstc T w s c'))}}).
Proof.
  intros. unfold mk_istype. unfold mkc_istype.

  assert (wf_term (mk_subtype_rel T T)) as wf1.
  { allrw @wf_mk_istype; apply wf_subtype_rel; auto. }

  assert (cover_vars (mk_subtype_rel T T) s) as cov1.
  { allrw @cover_vars_mk_istype; apply cover_vars_subtype_rel; auto. }

  pose proof (lsubstc_mk_subtype_rel_ex T T s wf1 cov1) as q; exrepnd; GC.
  exists wA cA; auto.
Qed.
