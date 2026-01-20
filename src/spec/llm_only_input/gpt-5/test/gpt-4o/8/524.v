Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_negatives :
  sum_product_spec ((-5)%Z :: 30%Z :: 6%Z :: 10%Z :: nil) (41%Z, (-9000)%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.