
Require Import List.
Require Import ZArith.

Definition smallest_change_spec (arr : list Z) (result : nat) : Prop :=
  exists arr_reversed : list Z,
    arr_reversed = rev arr /\
    (exists cnt : nat,
        cnt = 0 /\
        (forall i : nat, 
            i < length arr / 2 ->
            (nth i arr 0 <> nth i arr_reversed 0 -> cnt = S (cnt - 1)) /\
            (nth i arr 0 = nth i arr_reversed 0 -> cnt = cnt)) /\
        result = cnt).
