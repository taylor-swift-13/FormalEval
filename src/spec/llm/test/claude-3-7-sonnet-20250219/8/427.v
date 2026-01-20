Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [10%Z; 2%Z; 9%Z; 30%Z; 0%Z; 3%Z; -8%Z; 10%Z; -5%Z; 10%Z; 0%Z] 61 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Sum: 10 + 2 + 9 + 30 + 0 + 3 + (-8) + 10 + (-5) + 10 + 0 = 61 *)
    reflexivity.
  - simpl.
    (* Product includes 0, so product is 0 *)
    reflexivity.
Qed.