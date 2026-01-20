Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [2.443642398169077%R; 5.9%R; (-40)%R; (-0.5)%R; 0%R; 5.9%R; 8.6%R; 3.8%R]
    [3.443642398169077%R; 6.9%R; (-39)%R; 0.5%R; 1%R; 6.9%R; 9.6%R; 4.8%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (2.443642398169077 + 1) with 3.443642398169077 by lra.
  replace (5.9 + 1) with 6.9 by lra.
  replace (-40 + 1) with (-39) by lra.
  replace (-0.5 + 1) with 0.5 by lra.
  replace (0 + 1) with 1 by lra.
  replace (5.9 + 1) with 6.9 by lra.
  replace (8.6 + 1) with 9.6 by lra.
  replace (3.8 + 1) with 4.8 by lra.
  reflexivity.
Qed.