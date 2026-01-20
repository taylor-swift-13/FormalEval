Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 0
  | n :: rest => n + sum_list rest
  end.

Fixpoint product_list (numbers : list Z) : Z :=
  match numbers with
  | [] => 1
  | n :: rest => n * product_list rest
  end.

Definition sum_product_spec (numbers : list Z) (result : Z * Z) : Prop :=
  fst result = sum_list numbers /\ snd result = product_list numbers.

Definition bool_to_Z (b : bool) : Z :=
  if b then 1 else 0.

Fixpoint bool_list_to_Z_list (bools : list bool) : list Z :=
  match bools with
  | [] => []
  | b :: rest => bool_to_Z b :: bool_list_to_Z_list rest
  end.

Example test_sum_product_bools : sum_product_spec (bool_list_to_Z_list [false; false; false; false; false; true; true; true; true; false]) (4, 0).
Proof.
  unfold sum_product_spec.
  simpl.
  split; reflexivity.
Qed.