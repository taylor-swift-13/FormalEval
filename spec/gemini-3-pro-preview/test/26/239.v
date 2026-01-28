Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [0; 1; 3; 5; 7; 9; 11; 13; 18; 15; 1000; 19; 13; 11] [0; 1; 3; 5; 7; 9; 18; 15; 1000; 19].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.