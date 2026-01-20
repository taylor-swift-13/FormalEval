Require Import Arith.
Require Import List.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left plus well 0.

Definition required_trips (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let water_in_well := count_water well in
      acc + (water_in_well + bucket_capacity - 1) / bucket_capacity)
    grid 0.

Definition Spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips grid bucket_capacity.

Example test_case :
  Spec [[1; 1; 1; 1; 1]; [0; 0; 0; 0; 0]; [0; 0; 0; 0; 0]] 2 3.
Proof.
  unfold Spec.
  unfold required_trips.
  simpl.
  reflexivity.
Qed.