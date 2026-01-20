Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec [1%Z; 10%Z; 5%Z; 9%Z; 8%Z; (-5)%Z; 11%Z; (-5)%Z; (-10)%Z] (24%Z, (-9900000)%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.