Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_list_with_zeros :
  sum_product_spec (cons 0 (cons 8 (cons 0 (cons 0 (cons 21 (cons 0 (cons 0 (cons 8 nil)))))))) (37, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.