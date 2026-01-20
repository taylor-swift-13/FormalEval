Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example remove_duplicates_spec_repeated_elements :
  remove_duplicates_spec [10%Z; 10%Z; 10%Z; 10%Z; 13%Z; 999%Z; 10%Z] [13%Z; 999%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.