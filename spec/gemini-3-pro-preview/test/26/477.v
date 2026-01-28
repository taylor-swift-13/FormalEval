Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_case1 : remove_duplicates_spec [12; 1; 1; 5; 2; 3; 3; 2; 3; 4; 3; 5; 5; 2; 5; 15; 5] [12; 4; 15].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.