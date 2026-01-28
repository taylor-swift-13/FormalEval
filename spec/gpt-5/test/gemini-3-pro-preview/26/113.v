Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec [5; 0; 1; 3; 5; 7; 9; 11; -5; 15; 17; 19; 13] [0; 1; 3; 7; 9; 11; -5; 15; 17; 19; 13].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.