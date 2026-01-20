Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_complex : remove_duplicates_spec [10%Z; 10%Z; 10%Z; 10%Z; 9%Z; 9%Z; 11%Z; 10%Z; 10%Z; 9%Z] [11%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.