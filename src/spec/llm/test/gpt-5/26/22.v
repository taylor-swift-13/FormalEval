Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example remove_duplicates_spec_all_unique :
  remove_duplicates_spec [2%Z; 3%Z; 4%Z; 6%Z; 8%Z; 9%Z] [2%Z; 3%Z; 4%Z; 6%Z; 8%Z; 9%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.