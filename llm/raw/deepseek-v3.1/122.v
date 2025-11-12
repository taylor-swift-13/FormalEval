
Require Import List ZArith.
Import ListNotations.

Definition digits (x : Z) : nat :=
  match x with
  | Z0 => 1
  | Zpos p => Z.to_nat (Z.log10 (Zpos p) + 1)
  | Zneg p => Z.to_nat (Z.log10 (Zpos p) + 1)
  end.

Definition add_elements_spec (arr : list Z) (k : nat) (sum : Z) : Prop :=
  exists prefix, prefix = firstn k arr /\
  sum = fold_left Z.add (filter (fun x => digits x <= 2) prefix) 0%Z /\
  1 <= length arr <= 100 /\
  1 <= k <= length arr.
