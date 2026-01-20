Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [-3.4; -2; -0.5; 7.9; 7; 5.9; 6.4; 7.9]
                 [-2.4; -1; 0.5; 8.9; 8; 6.9; 7.4; 8.9].
Proof.
  unfold incr_list_spec.
  cbn.
  replace (-2.4) with (-3.4 + 1) by lra.
  replace (-1) with (-2 + 1) by lra.
  replace (0.5) with (-0.5 + 1) by lra.
  replace (8.9) with (7.9 + 1) by lra.
  replace (8) with (7 + 1) by lra.
  replace (6.9) with (5.9 + 1) by lra.
  replace (7.4) with (6.4 + 1) by lra.
  replace (8.9) with (7.9 + 1) by lra.
  reflexivity.
Qed.