Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_case :
  sum_product_spec [78%Z; -77%Z; 91%Z; -36%Z; 6%Z; -2%Z; -74%Z; 20%Z; 27%Z; 93%Z] (126%Z, 877442962556160%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.