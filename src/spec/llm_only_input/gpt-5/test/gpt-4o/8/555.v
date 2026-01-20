Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_mixed_negatives :
  sum_product_spec
    (-6 :: -9 :: -10 :: 1 :: -4 :: 7 :: 4 :: -6 :: 9 :: -11 :: -5 :: 4 :: 8 :: 0 :: -4 :: nil)
    (-22, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.