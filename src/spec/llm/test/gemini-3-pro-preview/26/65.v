Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [1; 2; 3; 4; 5; 6; 7; 8; 10; 6; 8; 9; 9; 9] [1; 2; 3; 4; 5; 7; 10].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.