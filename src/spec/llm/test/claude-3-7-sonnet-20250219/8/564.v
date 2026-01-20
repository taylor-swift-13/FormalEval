Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nonempty_list :
  sum_product_spec [10%Z; 6%Z; 30%Z; 0%Z; -7%Z; 31%Z; 10%Z] 80 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* compute sum: 10 + 6 + 30 + 0 + (-7) + 31 + 10 = 80 *)
    reflexivity.
  - simpl.
    (* compute product: 10 * 6 * 30 * 0 * (-7) * 31 * 10 = 0 *)
    reflexivity.
Qed.