Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec
    (cons 1 (cons 5 (cons (-1) (cons (-36) (cons (-1) (cons (-2) (cons (-1) (cons (-1) nil))))))))
    (-36, 360).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.