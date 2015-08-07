(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Add LoadPath "../".

Require Export type_sys.
Require Import dest_close.



Lemma close_type_system_init {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> ts T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou e.
  use_dou.

  rw @type_sys_props_iff_type_sys_props2.

  prove_type_sys_props2 SCase; intros.

  + SCase "uniquely_valued".
    spcast; dclose cl cl; dest_close_lr h; spts.

  + SCase "type_symmetric".
    repdors; subst; spcast; dest_close_lr h; apply CL_init; spts.

  + SCase "type_value_respecting".
    apply CL_init; sp; subst; try spts.

  + SCase "term_symmetric".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tes with (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tet with (T := T) (T' := T'); auto.

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


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
