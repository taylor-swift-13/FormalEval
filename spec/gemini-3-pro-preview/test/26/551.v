Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_repeated : remove_duplicates_spec [10; 10; 10; 10; 10] [].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.