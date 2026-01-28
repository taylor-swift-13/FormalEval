Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec [12; 1; 1; 2; 2; 3; 4; 2; 4; 5; 5; 5; 4; 2; 5; -30; 4] [12; 3; -30].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.