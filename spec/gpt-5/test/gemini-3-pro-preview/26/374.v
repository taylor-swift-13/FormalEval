Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec [-30; 1; 1; 2; 2; 3; 4; 14; 4; 4; 14; 5; 4; 2; 5; 4; 5; 14; 14] [-30; 3].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.