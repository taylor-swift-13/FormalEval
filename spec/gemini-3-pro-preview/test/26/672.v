Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [1; 3; 3; 3; 3; 4; 4; 5; 5; 5; 5; 6; 7; 8; 9; 9; 9; 9; 10; 11; 18; 6; 12; 12; 12; 13; 13; 13; 14; 15; 16; 17; 18; 19; 20; 18; 13] [1; 7; 8; 10; 11; 14; 15; 16; 17; 19; 20].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.