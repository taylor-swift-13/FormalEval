Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec 
  [18%Z; (-10)%Z; 5%Z; 2%Z; 7%Z; 5%Z; (-10)%Z; 12%Z; 12%Z; 1%Z; 0%Z; (-5)%Z; 9%Z; (-5)%Z; 20%Z; 20%Z; (-30)%Z; 1000%Z; (-10)%Z; 1%Z]
  [18%Z; 2%Z; 7%Z; 0%Z; 9%Z; (-30)%Z; 1000%Z].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.