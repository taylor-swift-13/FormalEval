Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec 
  [-10%Z; 4%Z; -30%Z; 5%Z; -10%Z; 8%Z; 12%Z; 12%Z; 1%Z; 0%Z; -5%Z; 9%Z; -5%Z; 20%Z; 20%Z; -30%Z; 12%Z] 
  [4%Z; 5%Z; 8%Z; 1%Z; 0%Z; 9%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.