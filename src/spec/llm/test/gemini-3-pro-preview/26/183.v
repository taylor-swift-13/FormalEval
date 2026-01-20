Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [0; 1; 19; 5; 7; 9; 11; 13; 15; 17; 8; 19; 13; 19] [0; 1; 5; 7; 9; 11; 15; 17; 8].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.