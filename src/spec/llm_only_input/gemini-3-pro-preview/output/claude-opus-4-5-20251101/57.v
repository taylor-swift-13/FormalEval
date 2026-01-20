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

Example test_monotonic : monotonic_spec [1; 2; 4; 10] true.
Proof.
  unfold monotonic_spec.
  split.
  - (* Direction: true = true -> (is_increasing \/ is_decreasing) *)
    intros _.
    left. (* We choose to prove it is increasing *)
    unfold is_increasing.
    intros i j H_range H_len.
    simpl in H_len. (* length is 4 *)
    
    (* Perform case analysis on index i *)
    destruct i.
    + (* i = 0 *)
      simpl. (* nth 0 is 1 *)
      (* Perform case analysis on index j *)
      destruct j; [ lia | ]. (* j cannot be 0 because 0 <= i < j *)
      destruct j.
      * (* j = 1 *) simpl. lia. (* 1 <= 2 *)
      * destruct j.
        -- (* j = 2 *) simpl. lia. (* 1 <= 4 *)
        -- destruct j.
           ++ (* j = 3 *) simpl. lia. (* 1 <= 10 *)
           ++ (* j >= 4 *) lia. (* Contradicts j < length *)
    + destruct i.
      * (* i = 1 *)
        simpl. (* nth 1 is 2 *)
        destruct j; [ lia | ].
        destruct j; [ lia | ]. (* j must be > 1 *)
        destruct j.
        -- (* j = 2 *) simpl. lia. (* 2 <= 4 *)
        -- destruct j.
           ++ (* j = 3 *) simpl. lia. (* 2 <= 10 *)
           ++ lia.
      * destruct i.
        -- (* i = 2 *)
           simpl. (* nth 2 is 4 *)
           destruct j; [ lia | ].
           destruct j; [ lia | ].
           destruct j; [ lia | ]. (* j must be > 2 *)
           destruct j.
           ++ (* j = 3 *) simpl. lia. (* 4 <= 10 *)
           ++ lia.
        -- (* i >= 3 *)
           (* Since i < j and j < 4, i cannot be >= 3 *)
           lia.
  - (* Direction: (is_increasing \/ is_decreasing) -> true = true *)
    intros _.
    reflexivity.
Qed.