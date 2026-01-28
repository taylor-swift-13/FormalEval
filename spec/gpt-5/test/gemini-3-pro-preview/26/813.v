Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec [3; 5; -5; 7; 9; 21; 0; 20; 11; 13; 15; 18; 19; 0; 18; 18; 13] [3; 5; -5; 7; 9; 21; 20; 11; 15; 19].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.