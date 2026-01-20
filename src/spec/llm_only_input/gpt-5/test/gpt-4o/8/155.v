Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  let sum := fold_right Z.add 0 numbers in
  let product := fold_right Z.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_mixed_integers :
  sum_product_spec (-10 :: 0 :: 9 :: 5 :: 8 :: -3 :: -5 :: nil) (4, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.