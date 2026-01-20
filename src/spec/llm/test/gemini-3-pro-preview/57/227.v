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

Example test_monotonic_2 : monotonic_spec [2; 2; 4; 5; 4; 3; 2; 1; -1; 1; 5; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Refute sorted_inc *)
      inversion Hinc; subst.
      inversion H3; subst.
      inversion H5; subst.
      inversion H7; subst.
      lia. (* Contradiction: 5 <= 4 is false *)
    + (* Refute sorted_dec *)
      inversion Hdec; subst.
      inversion H3; subst.
      lia. (* Contradiction: 2 >= 4 is false *)
Qed.