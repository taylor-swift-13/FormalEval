Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [-10; 5; 1; 11; 17; -10; 8; 12; 12; 1; 0; -5; 9; -5; -9; 20; 20; -30] [5; 11; 17; 8; 0; 9; -9; -30].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.