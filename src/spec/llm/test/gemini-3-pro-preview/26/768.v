Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [1; 3; 5; 7; 13; 9; 13; 15; 16; -30; 5; 6; 5] [1; 3; 7; 9; 15; 16; -30; 6].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.