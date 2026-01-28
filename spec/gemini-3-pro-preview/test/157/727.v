Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_fail : right_angle_triangle_spec 26.117120159873124 94.48837938393268 94.48837938393268 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | H]]; nra.
Qed.