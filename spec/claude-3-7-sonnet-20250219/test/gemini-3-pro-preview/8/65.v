Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_large : sum_product_spec [1; 4; 8; 16; 32; 8; 50] 119 6553600.
Proof.
  unfold sum_product_spec.
  split.
  - apply Nat.eqb_eq. vm_compute. reflexivity.
  - apply Nat.eqb_eq. vm_compute. reflexivity.
Qed.