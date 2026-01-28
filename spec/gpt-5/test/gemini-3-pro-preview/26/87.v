Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Open Scope Z_scope.

Example test_case: remove_duplicates_spec [1; -1; 3; 4; 5; 6; 7; 4; 9; 9; 9; 9] [1; -1; 3; 5; 6; 7].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.