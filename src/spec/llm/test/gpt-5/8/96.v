Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_list (l : list bool) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if x then 1 else 0) + sum_list xs
  end.

Fixpoint prod_list (l : list bool) : Z :=
  match l with
  | [] => 1
  | x :: xs => (if x then 1 else 0) * prod_list xs
  end.

Definition sum_product_spec (numbers : list bool) (res : Z * Z) : Prop :=
  res = (sum_list numbers, prod_list numbers).

Example test_case_sum_product_bools : sum_product_spec [false; false; false; false; false; true; true; true; true; false] (4, 0).
Proof.
  unfold sum_product_spec.
  vm_compute.
  reflexivity.
Qed.