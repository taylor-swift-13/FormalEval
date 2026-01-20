Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Definition count_water (well : list nat) : nat := fold_left Nat.add well 0.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left (fun acc well => let w := count_water well in acc + (w + bucket_capacity - 1) / bucket_capacity) grid 0.

Example required_trips_impl_ex:
  required_trips_impl ((1%nat :: 0%nat :: nil) :: (1%nat :: 1%nat :: nil) :: nil) 1%nat = 3%nat.
Proof. reflexivity. Qed.

Definition required_trips_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.


