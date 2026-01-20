Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_negative_list :
  sum_product_spec [-9; 4; -10; -6; 8; -6] (-19, 103680).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.