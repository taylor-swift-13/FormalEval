Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_1: remove_duplicates_spec [1%Z; 2%Z; 4%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 6%Z; 8%Z; 9%Z; 9%Z; 6%Z; 3%Z] [1%Z; 2%Z; 5%Z; 7%Z].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.