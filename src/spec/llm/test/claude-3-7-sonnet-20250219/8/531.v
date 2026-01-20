Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [10%Z; -5%Z; 0%Z; -8%Z; -6%Z; -7%Z; 30%Z; -3%Z] 11 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 10 + (-5) + 0 + (-8) + (-6) + (-7) + 30 + (-3) = 11 *)
    reflexivity.
  - simpl.
    (* Product contains 0, so product = 0 *)
    reflexivity.
Qed.