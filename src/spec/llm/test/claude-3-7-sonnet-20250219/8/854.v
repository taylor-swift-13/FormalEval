Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [1%Z; 2%Z; 3%Z; 10%Z; 20%Z; 30%Z; 3%Z] 69 108000.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    reflexivity.
  - (* product *)
    simpl.
    reflexivity.
Qed.