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

Example test_monotonic : monotonic_spec [5%Z; 1%Z; -10%Z; -7%Z; -9%Z; 1%Z; 2%Z; 5%Z] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> Direction: false = true implies contradiction *)
    intros H. discriminate.
  - (* <- Direction: Neither increasing nor decreasing implies false = true *)
    intros [Hinc | Hdec].
    + (* Case: Increasing *)
      unfold is_increasing in Hinc.
      (* Counter-example at indices 0 and 1: 5 is not <= 1 *)
      specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (Hbounds : (0 <= 0 < 1)%nat /\ (1 < 8)%nat) by lia.
      destruct Hbounds as [H1 H2].
      specialize (Hinc H1 H2).
      lia.
    + (* Case: Decreasing *)
      unfold is_decreasing in Hdec.
      (* Counter-example at indices 2 and 3: -10 is not >= -7 *)
      specialize (Hdec 2%nat 3%nat).
      simpl in Hdec.
      assert (Hbounds : (0 <= 2 < 3)%nat /\ (3 < 8)%nat) by lia.
      destruct Hbounds as [H1 H2].
      specialize (Hdec H1 H2).
      lia.
Qed.