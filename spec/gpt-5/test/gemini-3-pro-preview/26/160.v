Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec [12; 1; 1; 2; 5; 2; 3; -10; 4; 4; 5; 4; 2; 4; 4; 2; 2] [12; 3; -10].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.