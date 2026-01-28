Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [1; 5; 6; 11; 17; 13; -9; 18; 19; 7; 5] [1; 6; 11; 17; 13; -9; 18; 19; 7].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.