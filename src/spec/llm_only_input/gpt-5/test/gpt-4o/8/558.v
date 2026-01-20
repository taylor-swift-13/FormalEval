Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec [-10; 1; 10; 5; -8; 8; 6; -5; -5; 9] (11, 43200000).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.