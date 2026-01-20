Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [-2%Z; -1%Z; 31%Z; 5%Z; -10%Z; 0%Z; 21%Z] 44 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* compute sum: -2 -1 + 31 + 5 -10 + 0 + 21 = 44 *)
    reflexivity.
  - simpl.
    (* compute product: folding multiplication over list yields 0 (due to zero element) *)
    reflexivity.
Qed.