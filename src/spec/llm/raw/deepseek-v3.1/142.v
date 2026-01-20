
Require Import List ZArith.
Import ListNotations.

Definition sum_squares_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc '(i, num) =>
    if Z.eqb (Z.modulo i 3) 0 then
      acc + (num * num)
    else if Z.eqb (Z.modulo i 4) 0 then
      acc + (num * num * num)
    else
      acc + num) (seq 0 (length lst) |> combine lst) 0.
