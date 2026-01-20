Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0%Z numbers in
  let product := fold_right Z.mul 1%Z numbers in
  result = (sum, product).

Example sum_product_spec_negatives :
  sum_product_spec [-5%Z; 30%Z; -8%Z; 10%Z] (27%Z, 12000%Z).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.