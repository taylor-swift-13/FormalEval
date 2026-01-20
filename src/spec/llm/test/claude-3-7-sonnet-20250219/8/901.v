Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec [3%Z; 7%Z; 1%Z; 4%Z; 7%Z; 3%Z; 2%Z; 7%Z; 7%Z] 41%Z 172872%Z.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum part *)
    simpl.
    reflexivity.
  - (* product part *)
    simpl.
    reflexivity.
Qed.