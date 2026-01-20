Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool := (Z.ltb (-100) n) && (Z.ltb n 100).

Definition sum_two_digits_first_k_impl (arr : list Z) (k : nat) : Z :=
  let first_k := firstn k arr in
  let filtered := filter is_at_most_two_digits first_k in
  fold_left Z.add filtered 0.

Example sum_two_digits_first_k_impl_ex:
  sum_two_digits_first_k_impl (111%Z :: 21%Z :: 3%Z :: 4000%Z :: nil) 4%nat = 24%Z.
Proof. reflexivity. Qed.

Definition sum_two_digits_first_k_spec (arr : list Z) (k : nat) (output : Z) : Prop :=
  output = sum_two_digits_first_k_impl arr k.


