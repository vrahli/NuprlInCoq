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
  forall lib (ts : cts(p)) T eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> ts T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou e.
  use_dou.

  prove_ts_props Case.

  + SCase "uniquely_valued".
    introv cl.
    spcast.
    dest_close_lr h.
    onedts uv tye tyvr tes tet tevr.
    eapply uv; eauto.

  + SCase "type_extensionality".
    introv eqt.
    spcast.
    apply CL_init.
    onedts uv tye tyvr tes tet tevr.
    eapply tye; eauto.

  + SCase "type_value_respecting".
    introv ceq.
    spcast.
    apply CL_init.
    onedts uv tye tyvr tes tet tevr.
    eapply tyvr; eauto.

  + SCase "term_symmetric".
    onedts uv tye tyvr tes tet tevr.
    eapply tes; eauto.

  + SCase "term_transitive".
    onedts uv tye tyvr tes tet tevr.
    eapply tet; eauto.

  + SCase "term_value_respecting".
    onedts uv tye tyvr tes tet tevr.
    eapply tevr; eauto.
Qed.
