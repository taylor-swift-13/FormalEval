Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_mixed :
  incr_list_spec [-2; (-1) / 2; 1; 16 / 5; (-1) / 2; (-17) / 5]
                 [-1; 1 / 2; 2; 21 / 5; 1 / 2; (-12) / 5].
Proof.
  unfold incr_list_spec.
  simpl.
  replace ((-17) / 5 + 1) with ((-12) / 5) by lra.
  replace (16 / 5 + 1) with (21 / 5) by lra.
  replace ((-1) / 2 + 1) with (1 / 2) by lra.
  replace (-2 + 1) with (-1) by lra.
  replace (1 + 1) with 2 by lra.
  reflexivity.
Qed.