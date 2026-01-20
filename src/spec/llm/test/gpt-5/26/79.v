Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example remove_duplicates_spec_nontrivial_list :
  remove_duplicates_spec [2%Z; 9%Z; 2%Z; 3%Z; 2%Z; 10%Z] [9%Z; 3%Z; 10%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.