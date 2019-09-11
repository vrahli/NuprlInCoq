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

(**

  Extracts the unguessable tokens from canonical operators, opids, and
  terms.

*)

Require Export terms2.
Require Export sovar.

Definition oatom o := @OList (get_patom_set o).
Definition oatomv {o} a : oatom o := OLO a.
Definition oatoml {o} l : oatom o := OLL l.
Definition oatoms {o} f : oatom o := OLS f.

Definition oatomvs {o} (l : list (get_patom_set o)) : list (oatom o) :=
  map oatomv l.

Fixpoint get_cutokens {p} (t : @NTerm p) : oatom p :=
  match t with
    | vterm _ => oatoml []
    | oterm o bterms =>
      oappl ((oatomvs (get_utokens_o o))
               ++ (map get_cutokens_b bterms))
  end
with get_cutokens_b {p} (bt : @BTerm p) : oatom p :=
       match bt with
         | bterm _ t => get_cutokens t
       end.

Fixpoint get_utokens_so {p} (t : @SOTerm p) : list (get_patom_set p) :=
  match t with
  | sovar _ ts => flat_map get_utokens_so ts
  | soterm op bs => (get_utokens_o op) ++ (flat_map get_utokens_b_so bs)
  end
with get_utokens_b_so {p} (bt : @SOBTerm p) : list (get_patom_set p) :=
       match bt with
       | sobterm _ t => get_utokens_so t
       end.

Fixpoint get_cutokens_so {p} (t : @SOTerm p) : oatom p :=
  match t with
  | sovar _ ts => oappl (map get_cutokens_so ts)
  | soterm op bs => oappl ((oatomvs (get_utokens_o op))
                             ++ (map get_cutokens_b_so bs))
  end
with get_cutokens_b_so {p} (bt : @SOBTerm p) : oatom p :=
       match bt with
       | sobterm _ t => get_cutokens_so t
       end.

Definition get_utokens_bs {p} (bts : list (@BTerm p)) : list (get_patom_set p) :=
  flat_map get_utokens_b bts.

Definition get_cutokens_bs {p} (bts : list (@BTerm p)) : oatom p :=
  oatoml (map get_cutokens_b bts).

Definition getc_utokens {p} (t : @CTerm p) : list (get_patom_set p) :=
  get_utokens (get_cterm t).

Definition getc_cutokens {p} (t : @CTerm p) : oatom p :=
  get_cutokens (get_cterm t).

Definition is_free_from_atom {o} (a : get_patom_set o) (t : @NTerm o) :=
  !LIn a (get_utokens t).

Definition is_free_from_oatom {o} (a : get_patom_set o) (t : @NTerm o) :=
  !in_olist a (get_cutokens t).

Lemma nt_wf_utoken {o} : forall a : @get_patom_set o, nt_wf (mk_utoken a).
Proof.
  sp; repeat constructor; simpl; sp.
Qed.
