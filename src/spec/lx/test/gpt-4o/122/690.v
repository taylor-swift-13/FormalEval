Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition sum_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example sum_test :
  sum_spec [100; 200; 300; 400; 10000; 600; 700; 800; 900; 1000; 1000] 3 0.
Proof.
  unfold sum_spec.
  simpl.
  reflexivity.
Qed.