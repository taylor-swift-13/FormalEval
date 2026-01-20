Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [1; 2; 3; 3; 3; 4; 4; 5; 5; 5; 5; 6; 7; 9; 9; 9; 9; 10; 11; 11; 12; 11; 12; 13; 13; 13; 13; 14; 15; 16; 17; 18; 18; 19; 20; 16] [1; 2; 6; 7; 10; 14; 15; 17; 19; 20].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.