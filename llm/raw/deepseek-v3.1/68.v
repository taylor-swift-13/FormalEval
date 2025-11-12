
Require Import List ZArith.
Import ListNotations.

Definition pluck_spec (arr : list Z) (result : list Z) : Prop :=
  if forallb (fun x => Z.odd x) arr then
    result = []
  else
    let min_even := Z.min_list (filter (fun x => Z.even x) arr) in
    exists i, nth_error arr i = Some min_even /\
    (forall j, j < i -> nth_error arr j <> Some min_even) /\
    result = [min_even; Z.of_nat i].
