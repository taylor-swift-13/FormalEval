Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [1; 2; 3; 2; 1; 3; 4; 5; 7; 6; 7; 8; 9; 10; 3; 12; 14; 16; 18; 19; 20; 18; 10; 1000; 7; 3; 14; 16; 10; 18; 19; 20; 7; 10; 20; 16; 18; 12] [4; 5; 6; 8; 9; 1000].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.