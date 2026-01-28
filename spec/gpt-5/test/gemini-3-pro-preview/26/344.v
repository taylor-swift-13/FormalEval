Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec 
  [-10; 5; -30; 5; -10; 8; 12; 12; 1; 0; 20; -5; 9; -5; 20; 20; -30; 11; 12; 20] 
  [8; 1; 0; 9; 11].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.