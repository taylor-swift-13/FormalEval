Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Local Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_nonempty_list :
  sum_product_spec [10; -5; -10; 0; -8; 30; 10; -5] (22, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.