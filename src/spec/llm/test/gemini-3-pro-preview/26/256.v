Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [-10; 5; -30; 5; -10; 8; 12; 12; 0; -5; 9; -5; 20; 20; -30; 12; 12; 20] [8; 0; 9].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.