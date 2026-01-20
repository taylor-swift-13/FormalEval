Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_test_case :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; -6; -6; 1; 1; 1; 1; 1; 1; 1; -5; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 3; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    (41, -540).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.