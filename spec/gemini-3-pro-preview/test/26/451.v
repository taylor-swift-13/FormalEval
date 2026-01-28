Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [1; 1; 4; -9; 2; 4; 2; 3; 3; 4; 4; 4; 0; 4; 5; 4; 5] [-9; 0].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.