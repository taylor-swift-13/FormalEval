Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [1000; 20; 101; 300; 40000; 100; 500; 500; 10000; 501; 6000; 70; 40000; 333; 333] 5 20.
Proof.
  unfold add_elements_spec.
  simpl.
  reflexivity.
Qed.