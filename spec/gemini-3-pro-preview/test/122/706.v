Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [-99; -88; -77; -66; -55; -44; -33; -22; -11; 0; 11; 22; 33; 44; 55; 20; 66; 77; 88; 99] 9 (-495).
Proof.
  unfold add_elements_spec.
  simpl.
  reflexivity.
Qed.