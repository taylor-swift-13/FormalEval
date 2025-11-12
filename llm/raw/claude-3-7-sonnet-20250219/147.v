
Require Import Arith.
Require Import Nat.

Definition a_val (i : nat) : nat :=
  i * i - i + 1.

Definition valid_triple (i j k : nat) (n : nat) : Prop :=
  1 <= i < j < k <= n /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

Definition get_max_triples_spec (n : nat) (res : nat) : Prop :=
  (n <= 2 -> res = 0) /\
  (n > 2 ->
    let one_cnt := 1 + ((n - 2) / 3) * 2 + ((n - 2) mod 3) in
    let zero_cnt := n - one_cnt in
    res = (one_cnt * (one_cnt - 1) * (one_cnt - 2)) / 6 
        + (zero_cnt * (zero_cnt - 1) * (zero_cnt - 2)) / 6).
