Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_values : sum_product_spec [20; 30; 40; 49] 139 1176000.
Proof.
  unfold sum_product_spec.
  split.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.