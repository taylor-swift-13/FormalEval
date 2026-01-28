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

Example test_monotonic : monotonic_spec [5; 4; 6; 3; 2; 2; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + (* Prove not increasing *)
      unfold is_increasing in H_inc.
      (* Counter-example: indices 0 and 1 (5 and 4) *)
      specialize (H_inc 0%nat 1%nat).
      assert (H_range: (0 <= 0 < 1)%nat) by lia.
      assert (H_len: (1 < length [5; 4; 6; 3; 2; 2; 1])%nat) by (simpl; lia).
      specialize (H_inc H_range H_len).
      simpl in H_inc.
      lia.
    + (* Prove not decreasing *)
      unfold is_decreasing in H_dec.
      (* Counter-example: indices 1 and 2 (4 and 6) *)
      specialize (H_dec 1%nat 2%nat).
      assert (H_range: (0 <= 1 < 2)%nat) by lia.
      assert (H_len: (2 < length [5; 4; 6; 3; 2; 2; 1])%nat) by (simpl; lia).
      specialize (H_dec H_range H_len).
      simpl in H_dec.
      lia.
Qed.