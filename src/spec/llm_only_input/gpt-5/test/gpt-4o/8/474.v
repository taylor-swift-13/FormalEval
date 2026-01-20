Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negatives_and_positives :
  sum_product_spec [-2%Z; 5%Z; -10%Z; 10%Z; -2%Z; 10%Z] (11%Z, -20000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.