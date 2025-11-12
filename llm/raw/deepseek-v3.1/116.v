
Require Import List ZArith.
Import ListNotations.

Fixpoint count_ones (n : Z) : nat :=
  match n with
  | 0%Z => 0%nat
  | _ => if Z.odd n then S (count_ones (Z.div2 n)) else count_ones (Z.div2 n)
  end.

Definition cmp_spec (x y : Z) : comparison :=
  let x_ones := count_ones x in
  let y_ones := count_ones y in
  match Nat.compare x_ones y_ones with
  | Lt => Lt
  | Gt => Gt
  | Eq => Z.compare x y
  end.

Definition sort_array_spec (arr sorted_arr : list Z) : Prop :=
  Permutation arr sorted_arr /\
  Sorted (fun x y => cmp_spec x y <> Gt) sorted_arr.
