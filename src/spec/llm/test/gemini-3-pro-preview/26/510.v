Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [12; 1; 15; 5; 2; 9; 2; 4; 4; 5; 5; 4; 2; 5; 4; 2; 2] [12; 1; 15; 9].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.