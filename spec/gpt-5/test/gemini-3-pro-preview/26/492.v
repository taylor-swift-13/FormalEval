Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Open Scope Z_scope.

Example test_case_1: remove_duplicates_spec 
  [1; 2; 3; 3; 1; 20; 4; 5; 7; 6; 7; 8; 18; 9; 10; 3; 12; 14; 18; 19; 20; 18; 10; 12; 7; 3; 14; 16; 10; 18; 19; 20; 7; 10; 20; -10; 16; 8; 18]
  [2; 4; 5; 6; 9; -10].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.