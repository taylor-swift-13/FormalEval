Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec [999; 5; 3; 5; -10; 8; 12; 12; 1; -5; 5; -5; 19; -6; 20; -30; 12; -10; 2] [999; 3; 8; 1; 19; -6; 20; -30; 2].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.