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

Example test_monotonic : monotonic_spec [-5; -7; -9; -11] true.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: Prove that the list is increasing or decreasing *)
    intros _.
    right. (* The list is decreasing *)
    unfold is_decreasing.
    intros i j H_range H_len.
    simpl in H_len.
    (* Break down index i based on the length of the list *)
    destruct i; [| destruct i; [| destruct i; [| lia ]]].
    + (* Case i = 0 *)
      (* Break down index j *)
      destruct j; [ lia | destruct j; [| destruct j; [| destruct j; [| lia ]]]].
      * (* i=0, j=1: -5 >= -7 *) simpl; lia.
      * (* i=0, j=2: -5 >= -9 *) simpl; lia.
      * (* i=0, j=3: -5 >= -11 *) simpl; lia.
    + (* Case i = 1 *)
      destruct j; [ lia | destruct j; [ lia | destruct j; [| destruct j; [| lia ]]]].
      * (* i=1, j=2: -7 >= -9 *) simpl; lia.
      * (* i=1, j=3: -7 >= -11 *) simpl; lia.
    + (* Case i = 2 *)
      destruct j; [ lia | destruct j; [ lia | destruct j; [ lia | destruct j; [| lia ]]]].
      * (* i=2, j=3: -9 >= -11 *) simpl; lia.
  - (* <- Direction: Trivial since result is true *)
    intros _.
    reflexivity.
Qed.