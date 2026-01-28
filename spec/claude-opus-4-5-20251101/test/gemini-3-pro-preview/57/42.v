Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_increasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 <= nth j l 0.

Definition is_decreasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 >= nth j l 0.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> (is_increasing l \/ is_decreasing l).

Example test_monotonic : monotonic_spec [10; 9; 8; 7; 7; 7; 7] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    unfold is_decreasing.
    intros i j H_range H_len.
    simpl in H_len.
    destruct i; [| destruct i; [| destruct i; [| destruct i; [| destruct i; [| destruct i; [| lia ]]]]]].
    + destruct j; [ lia | destruct j; [| destruct j; [| destruct j; [| destruct j; [| destruct j; [| destruct j; [| lia ]]]]]]].
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
    + destruct j; [ lia | destruct j; [ lia | destruct j; [| destruct j; [| destruct j; [| destruct j; [| destruct j; [| lia ]]]]]]].
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
    + destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [| destruct j; [| destruct j; [| destruct j; [| lia ]]]]]]].
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
    + destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [| destruct j; [| destruct j; [| lia ]]]]]]].
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
    + destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [| destruct j; [| lia ]]]]]]].
      * simpl; lia.
      * simpl; lia.
    + destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [| lia ]]]]]]].
      * simpl; lia.
  - intros _.
    reflexivity.
Qed.