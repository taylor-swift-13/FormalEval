Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition generate_integers_spec (a b : Z) (evens : list Z) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  let upper := Z.min (b + 1) 10 in
  let count := upper - a in
  if count <=? 0 then evens = []
  else
    let start := Z.to_nat a in
    let len := Z.to_nat count in
    evens = filter (fun i => i mod 2 =? 0) (map Z.of_nat (seq start len)).

Example test_generate_integers : generate_integers_spec 987654321 10001 [].
Proof.
  vm_compute.
  reflexivity.
Qed.