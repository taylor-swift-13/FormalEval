
Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 1 < d < p -> Z.rem p d <> 0.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * product xs
  end.

Definition all_prime (l : list Z) : Prop :=
  forall x, In x l -> is_prime x.

Definition sorted_ascending (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    nth (Z.to_nat i) l 0 <= nth (Z.to_nat j) l 0.

Definition factorize_spec (n : Z) (result : list Z) : Prop :=
  n > 1 ->
  all_prime result /\
  sorted_ascending result /\
  product result = n.
