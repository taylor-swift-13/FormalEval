Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example remove_duplicates_spec_test_case :
  remove_duplicates_spec
    [12%Z; 0%Z; 2%Z; 5%Z; 0%Z; 2%Z; 3%Z; 15%Z; 4%Z; 2%Z; 4%Z; 4%Z; 5%Z; 5%Z; 4%Z; 2%Z; 5%Z; 14%Z; 2%Z; 5%Z; 5%Z]
    [12%Z; 3%Z; 15%Z; 14%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.