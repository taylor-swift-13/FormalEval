
Require Import ZArith.

Definition get_max_triples_spec (n : Z) (result : Z) : Prop :=
  (n <= 2 -> result = 0) /\
  (n > 2 -> 
    let one_cnt := 1 + (n - 2) / 3 * 2 + (n - 2) mod 3 in
    let zero_cnt := n - one_cnt in
    result = one_cnt * (one_cnt - 1) * (one_cnt - 2) / 6 + zero_cnt * (zero_cnt - 1) * (zero_cnt - 2) / 6).
