Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec
    [0.5071788072948802%R; 8.6%R; 3.8%R; -2.707945416165158%R; 2.443642398169077%R; 7.9%R; -2.1%R]
    [1.5071788072948802%R; 9.6%R; 4.8%R; -1.707945416165158%R; 3.443642398169077%R; 8.9%R; -1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace 1.5071788072948802%R with (0.5071788072948802%R + 1%R) by lra.
  replace 9.6%R with (8.6%R + 1%R) by lra.
  replace 4.8%R with (3.8%R + 1%R) by lra.
  replace (-1.707945416165158%R) with (-2.707945416165158%R + 1%R) by lra.
  replace 3.443642398169077%R with (2.443642398169077%R + 1%R) by lra.
  replace 8.9%R with (7.9%R + 1%R) by lra.
  replace (-1.1%R) with (-2.1%R + 1%R) by lra.
  reflexivity.
Qed.