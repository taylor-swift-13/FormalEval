Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [1; 5; 12; 9; 11; 13; 15; 15; 8; 17; 19; 7; 1; 13] [5; 12; 9; 11; 8; 17; 19; 7].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.