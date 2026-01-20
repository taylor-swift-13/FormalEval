Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_example :
  sum_product_spec (cons 5%Z (cons 1%Z (cons (-2)%Z (cons (-1)%Z nil)))) (3%Z, 10%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.