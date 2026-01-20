Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Fixpoint count_true (b : bool) (l : list bool) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if Bool.eqb x b then 1 else 0) + count_true b xs
  end.

Definition sum_product_spec (bool_lists : list (list bool)) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left (fun acc l => acc + count_true true l) bool_lists 0 /\
  result_product = fold_left (fun acc _ => 0) bool_lists 1.

Example test_sum_product_single_list :
  sum_product_spec [[false; false; false; false; false; true; true; true; true; false]] 4 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.