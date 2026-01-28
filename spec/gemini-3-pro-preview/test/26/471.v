Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [12; 0; 2; 5; 0; 2; 3; 9; 4; 4; 4; 4; 5; 5; 11; 4; 2; 5; 5; 2; 5; 5] [12; 3; 9; 11].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.