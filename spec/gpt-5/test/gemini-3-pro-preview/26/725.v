Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec 
  [999%Z; 5%Z; 3%Z; 5%Z; (-10)%Z; 8%Z; 12%Z; 12%Z; 1%Z; (-5)%Z; 9%Z; (-5)%Z; 19%Z; 20%Z; (-30)%Z; 12%Z; (-10)%Z; 2%Z] 
  [999%Z; 3%Z; 8%Z; 1%Z; 9%Z; 19%Z; 20%Z; (-30)%Z; 2%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.