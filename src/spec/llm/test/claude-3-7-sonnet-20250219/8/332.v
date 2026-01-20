Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [2%Z; 4%Z; -6%Z; 0%Z; 8%Z; -10%Z; -10%Z; -6%Z] (-18) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: 2 + 4 + (-6) + 0 + 8 + (-10) + (-10) + (-6) = -18 *)
    reflexivity.
  - simpl.
    (* Product has a 0, so product is 0 *)
    reflexivity.
Qed.