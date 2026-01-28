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

Example test_monotonic : monotonic_spec [1; 1; 1; 2; 2; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* Prove not increasing by counterexample indices 4 and 5 *)
      specialize (Hinc 4%nat 5%nat).
      simpl in Hinc.
      assert (Hrange: (0 <= 4 < 5)%nat) by lia.
      assert (Hlen: (5 < 7)%nat) by lia.
      specialize (Hinc Hrange Hlen).
      (* nth 4 is 2, nth 5 is 1, so 2 <= 1 is false *)
      lia.
    + (* Prove not decreasing by counterexample indices 2 and 3 *)
      specialize (Hdec 2%nat 3%nat).
      simpl in Hdec.
      assert (Hrange: (0 <= 2 < 3)%nat) by lia.
      assert (Hlen: (3 < 7)%nat) by lia.
      specialize (Hdec Hrange Hlen).
      (* nth 2 is 1, nth 3 is 2, so 1 >= 2 is false *)
      lia.
Qed.