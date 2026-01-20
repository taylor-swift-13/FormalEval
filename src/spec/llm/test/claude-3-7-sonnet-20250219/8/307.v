Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint fold_left_Z_add (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => fold_left_Z_add xs (acc + x)
  end.

Fixpoint fold_left_Z_mul (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | x :: xs => fold_left_Z_mul xs (acc * x)
  end.

Definition sum_product_Z_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left_Z_add numbers 0 /\
  result_product = fold_left_Z_mul numbers 1.

Example test_sum_product_Z_specific_list :
  sum_product_Z_spec [10%Z; 30%Z; -2%Z; -8%Z; -6%Z; 30%Z; 10%Z; 10%Z; 10%Z] 84 (-864000000).
Proof.
  unfold sum_product_Z_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.