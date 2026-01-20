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

Example test_monotonic_2 : monotonic_spec [10; 3; 5; 3; 2; 9; 7; 5; 4] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> direction: false = true implies ... (contradiction) *)
    intros H.
    discriminate H.
  - (* <- direction: sorted implies false = true (contradiction) *)
    intros [Hinc | Hdec].
    + (* Case: sorted_inc *)
      inversion Hinc; subst.
      (* 10 <= 3 is false *)
      lia.
    + (* Case: sorted_dec *)
      inversion Hdec; subst.
      (* 10 >= 3 is true, check next element *)
      match goal with H: sorted_dec (3 :: 5 :: _) |- _ => inversion H; subst end.
      (* 3 >= 5 is false *)
      lia.
Qed.