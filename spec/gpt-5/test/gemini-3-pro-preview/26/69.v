Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Open Scope Z_scope.

Example test_case_1: remove_duplicates_spec [-1; 0; 10; -1; 1] [0; 10; 1].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.