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


Require Export type_sys.
Require Import dest_close.



Lemma close_type_system_init {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ts lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou e.
  use_dou.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    spcast; dest_close_lr h; spts.

  + SCase "type_symmetric".
    repdors; subst; spcast; dest_close_lr h; apply CL_init; spts.

  + SCase "type_value_respecting".
    apply CL_init; sp; subst; try spts.

  + SCase "type_value_respecting_trans".
    unfold type_equality_respecting_trans; introv h ceq cl.
    pose proof (ceq lib) as c; simpl in c; autodimp c hyp; eauto 3 with slow; spcast.
    spcast; apply CL_init; sp; subst; try spts.

    { dup c2 as ct.
      eapply cequivc_uni in c2;[|eauto].
      dest_close_lr h.
      onedts uv tye tys tyt tyvr tes tet tevr.
      eapply tyt;[|exact h].
      apply tys.
      eapply tyvr;[|apply ccequivc_ext_sym;auto].
      eapply tyt; eauto. }

    { dup c0 as ct.
      eapply cequivc_uni in c0;[|eauto].
      dest_close_lr h.
      onedts uv tye tys tyt tyvr tes tet tevr.
      eapply tyt;[|exact h].
      apply tys.
      eapply tyvr;[|apply ccequivc_ext_sym;auto].
      eapply tyt; eauto. }

  + SCase "term_symmetric".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tes with (lib := lib) (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tet with (lib := lib) (T := T) (T' := T'); auto.

  + SCase "term_value_respecting".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tevr with (T := T); auto.
    use_trans T'; sp.

  + SCase "type_gsymmetric".
    sp; split; sp; subst; spcast; dest_close_lr h; apply CL_init; sp; try spts.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; spcast; dclose_lr; dands; apply CL_init; sp; spts.
Qed.
