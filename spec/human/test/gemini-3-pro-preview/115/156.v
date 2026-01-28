Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left Nat.add well 0.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let w := count_water well in
      acc + (w + bucket_capacity - 1) / bucket_capacity)
    grid
    0.

Definition problem_115_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.

Example test_case:
  problem_115_spec
    [[0; 0; 0; 1]; [0; 1; 1; 1]; [0; 0; 0; 1]; [0; 0; 0; 1]; [0; 1; 1; 1]]
    4
    5.
Proof.
  unfold problem_115_spec.
  unfold required_trips_impl.
  unfold count_water.
  simpl.
  reflexivity.
Qed.