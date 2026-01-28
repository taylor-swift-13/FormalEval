Require Import List.
Require Import Arith.
Require Import Lia.

Definition get_max_triples_spec (n : nat) (count : nat) : Prop :=
  let a := map (fun i => i * i - i + 1) (seq 1 n) in
  count = 
    if n <=? 2 then 0
    else
      let one_cnt := 1 + (n - 2) / 3 * 2 + (n - 2) mod 3 in
      let zero_cnt := n - one_cnt in
      one_cnt * (one_cnt - 1) * (one_cnt - 2) / 6 + zero_cnt * (zero_cnt - 1) * (zero_cnt - 2) / 6.

Example test_get_max_triples : get_max_triples_spec 201 439989.
Proof.
  unfold get_max_triples_spec.
  vm_compute.
  reflexivity.
Qed.