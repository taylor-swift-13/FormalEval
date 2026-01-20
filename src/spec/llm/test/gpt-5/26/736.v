Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example remove_duplicates_spec_single_duplicate :
  remove_duplicates_spec [7%Z; 8%Z; 5%Z; 10%Z; 6%Z; 6%Z] [7%Z; 8%Z; 5%Z; 10%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.