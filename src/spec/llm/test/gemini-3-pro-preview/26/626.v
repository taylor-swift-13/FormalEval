Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_new : remove_duplicates_spec [1; 3; 7; 8; 11; 13; 15; 1000; 10; 13] [1; 3; 7; 8; 11; 15; 1000; 10].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.