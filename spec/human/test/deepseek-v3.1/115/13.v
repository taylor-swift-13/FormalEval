Require Import Coq.Lists.List Coq.Arith.Arith Psatz.
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

Lemma example2_correct : required_trips_impl [[0;0;1;0]; [0;0;1;0]; [1;1;1;1]] 2 = 4.
Proof.
  unfold required_trips_impl, count_water.
  simpl.
  repeat rewrite Nat.add_assoc.
  repeat rewrite Nat.add_cancel_l.
  reflexivity.
Qed.