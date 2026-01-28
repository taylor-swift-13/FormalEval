Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [1; 2; 3; 3; 3; 4; 4; 5; 5; 5; 5; 6; 7; 8; 9; 9; 9; 9; 10; 11; 11; 20; 12; 12; 12; 13; 13; 13; 13; 14; 14; 15; 16; 1000; 18; 4; 20; 20; 10] [1; 2; 6; 7; 8; 15; 16; 1000; 18].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.