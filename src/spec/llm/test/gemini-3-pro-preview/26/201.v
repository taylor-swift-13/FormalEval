Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [1%Z; 5%Z; 12%Z; 9%Z; 11%Z; 13%Z; 15%Z; 15%Z; 17%Z; 19%Z; 7%Z; 1%Z] [5%Z; 12%Z; 9%Z; 11%Z; 13%Z; 17%Z; 19%Z; 7%Z].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.