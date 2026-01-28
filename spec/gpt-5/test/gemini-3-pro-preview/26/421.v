Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Open Scope Z_scope.

Example test_case_new: remove_duplicates_spec [-30; 1; -10; 1; 1; 2; 2; 2; 3; 3; 4; 5; 4; 5; 5; 5; 2; 4; 2; 2] [-30; -10].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.