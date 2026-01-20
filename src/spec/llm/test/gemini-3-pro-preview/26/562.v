Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [0; 10; 10; 9; 10; 8; 10; 10; 5; 10; 10] [0; 9; 8; 5].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.