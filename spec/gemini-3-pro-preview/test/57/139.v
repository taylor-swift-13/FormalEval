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

Example test_monotonic_1 : monotonic_spec [2; 2; 1; 1; 1; 1; 4; 4; 0; 6; 7; 7] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Refute sorted_inc *)
      inversion Hinc; subst. (* 2 <= 2 *)
      inversion H3; subst.   (* 2 <= 1 -> False *)
      lia.
    + (* Refute sorted_dec *)
      inversion Hdec; subst. (* 2 >= 2 *)
      inversion H3; subst.   (* 2 >= 1 *)
      inversion H5; subst.   (* 1 >= 1 *)
      inversion H7; subst.   (* 1 >= 1 *)
      inversion H9; subst.   (* 1 >= 1 *)
      inversion H11; subst.  (* 1 >= 4 -> False *)
      lia.
Qed.