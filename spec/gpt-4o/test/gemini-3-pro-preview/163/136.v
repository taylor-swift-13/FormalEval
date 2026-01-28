Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition generate_integers_spec (a b : Z) (evens : list Z) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (map Z.of_nat (seq (Z.to_nat a) (Z.to_nat (Z.min (b + 1) 10 - a)))).

Example test_generate_integers : generate_integers_spec 987654321 56789 [].
Proof.
  unfold generate_integers_spec.
  vm_compute.
  reflexivity.
Qed.