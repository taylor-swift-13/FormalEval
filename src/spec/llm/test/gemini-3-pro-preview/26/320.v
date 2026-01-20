Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [12; 1; 1; 2; 6; 2; 16; 3; 4; 2; 4; 4; 5; 5; 10; 15; 2; 5; 4; 4] [12; 6; 16; 3; 10; 15].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.