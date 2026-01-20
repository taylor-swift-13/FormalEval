Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [-30; 1; 1; 2; 2; 3; 4; 14; 4; 4; 14; 5; 4; 2; 5; 4; 5; 14] [-30; 3].
Proof.
  unfold remove_duplicates_spec.
  compute.
  reflexivity.
Qed.