Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec [1; 1; 1; 3; 2; 2; 2; 3; -10; 4; 4; 4; 5; 5; 5] [-10].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.