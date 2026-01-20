Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition sum_product_spec (numbers : list nat) (result : nat * nat) : Prop :=
  let sum := fold_right Nat.add 0 numbers in
  let product := fold_right Nat.mul 1 numbers in
  result = (sum, product).

Example sum_product_spec_nonempty_list :
  sum_product_spec (6 :: 1 :: 4 :: 30 :: 2 :: nil) (43, 1440).
Proof.
  unfold sum_product_spec.
  simpl.
  reflexivity.
Qed.