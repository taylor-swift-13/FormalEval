Require Import Coq.Arith.Arith.

(* 实现：1..n 的和 *)
Definition sum_to_n_impl (n : nat) : nat := n * (n + 1) / 2.

Example sum_to_n_impl_5: sum_to_n_impl 5 = (15)%nat.
Proof. reflexivity. Qed.

Definition sum_to_n_spec (n : nat) (output : nat) : Prop :=
  output = sum_to_n_impl n.


