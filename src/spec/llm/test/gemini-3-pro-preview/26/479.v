Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [7; 1; 3; 2; 1; 4; 5; 7; 6; 7; 18; 9; 10; 3; -31; 14; 16; 18; 19; 20; 18; 12; 7; 3; 14; 16; 10; 18; 19; 20; 7; 10; 20; 16; 18; 16] [2; 4; 5; 6; 9; -31; 12].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.