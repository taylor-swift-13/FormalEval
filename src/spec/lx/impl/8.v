Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* 实现：返回 (和, 积) *)
Definition sum_product_impl (l : list Z) : Z * Z :=
  (List.fold_left Z.add l 0, List.fold_left Z.mul l 1).

Example sum_product_impl_nil: sum_product_impl [] = (0%Z, 1%Z).
Proof. reflexivity. Qed.

Example sum_product_impl_1_2_3: sum_product_impl (1%Z :: 2%Z :: 3%Z :: nil) = (6%Z, 6%Z).
Proof. reflexivity. Qed.

Definition sum_product_spec (l : list Z) (output : Z * Z) : Prop :=
  output = sum_product_impl l.


