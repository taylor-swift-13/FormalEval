Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [0%Z; 0%Z; 1%Z; 0%Z; 0%Z; -6%Z; -6%Z; 1%Z; -1%Z; -6%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z; -7%Z] (-32)%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    rewrite ?Z.add_0_l.
    (* Compute the sum manually *)
    (* 0 + 0 + 1 + 0 + 0 + (-6) + (-6) + 1 + (-1) + (-6) + (-8) + 0 + 0 + 0 + 0 + (-7) = -32 *)
    reflexivity.
  - simpl.
    (* The product contains zeros, so fold multiplication gives 0 *)
    reflexivity.
Qed.