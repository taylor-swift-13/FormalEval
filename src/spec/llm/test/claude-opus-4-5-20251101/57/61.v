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

Example test_monotonic : monotonic_spec [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + unfold is_increasing in Hinc.
      assert (H1: nth 1 [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] 0 <= nth 2 [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] 0).
      { apply Hinc. lia. simpl. lia. }
      simpl in H1.
      lia.
    + unfold is_decreasing in Hdec.
      assert (H1: nth 0 [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] 0 >= nth 1 [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] 0).
      { apply Hdec. lia. simpl. lia. }
      simpl in H1.
      lia.
Qed.