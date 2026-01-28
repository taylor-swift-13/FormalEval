Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 13%Z; 15%Z; 16%Z; (-30)%Z; 5%Z; 19%Z] [1%Z; 3%Z; 7%Z; 9%Z; 13%Z; 15%Z; 16%Z; (-30)%Z; 19%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.