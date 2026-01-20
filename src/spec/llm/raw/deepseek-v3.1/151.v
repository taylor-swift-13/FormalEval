
Require Import List ZArith.
Import ListNotations.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc num => 
    if (Z.odd num && (num > 0)%Z && (Z.abs num <? 1000)%Z) then
      acc + (num * num)
    else
      acc) lst 0.
