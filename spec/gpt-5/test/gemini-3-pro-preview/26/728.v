Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Open Scope Z_scope.

Example test_case: remove_duplicates_spec [3; 5; -5; 7; 9; 0; 20; 11; 13; 16; 18; 19; 0; 15; 18] [3; 5; -5; 7; 9; 20; 11; 13; 16; 19; 15].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.