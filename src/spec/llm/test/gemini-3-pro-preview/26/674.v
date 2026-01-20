Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [3; 5; -5; 7; 9; 0; 11; -30; 13; 15; 18; 19; 18; 9] [3; 5; -5; 7; 0; 11; -30; 13; 15; 19].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.