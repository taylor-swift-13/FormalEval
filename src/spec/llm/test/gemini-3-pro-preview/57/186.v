Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sorted_inc : list Z -> Prop :=
  | sorted_inc_nil : sorted_inc []
  | sorted_inc_one : forall x, sorted_inc [x]
  | sorted_inc_cons : forall x y l, x <= y -> sorted_inc (y :: l) -> sorted_inc (x :: y :: l).

Inductive sorted_dec : list Z -> Prop :=
  | sorted_dec_nil : sorted_dec []
  | sorted_dec_one : forall x, sorted_dec [x]
  | sorted_dec_cons : forall x y l, x >= y -> sorted_dec (y :: l) -> sorted_dec (x :: y :: l).

Definition monotonic_spec (l : list Z) (res : bool) : Prop :=
  res = true <-> (sorted_inc l \/ sorted_dec l).

Example test_monotonic_case : monotonic_spec [2; 2; 1; 1; 2; 1; 3; 1; 4; 4; 5; 3] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Refuting sorted_inc: fails at 2, 1 *)
      inversion Hinc; subst; clear Hinc.
      match goal with H: sorted_inc _ |- _ => inversion H; subst; clear H end.
      lia.
    + (* Refuting sorted_dec: fails at 1, 2 *)
      inversion Hdec; subst; clear Hdec.
      match goal with H: sorted_dec _ |- _ => inversion H; subst; clear H end.
      match goal with H: sorted_dec _ |- _ => inversion H; subst; clear H end.
      match goal with H: sorted_dec _ |- _ => inversion H; subst; clear H end.
      lia.
Qed.