Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition count_occurrences (n : Z) (l : list Z) : nat :=
  length (filter (fun x => Z.eqb x n) l).

Definition occurs_once (n : Z) (l : list Z) : Prop :=
  count_occurrences n l = 1%nat.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun n => Nat.eqb (count_occurrences n numbers) 1%nat) numbers.

Example test_remove_duplicates_1: remove_duplicates_spec [7%Z; 0%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 20%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 13%Z; 7%Z] [0%Z; 1%Z; 3%Z; 5%Z; 9%Z; 20%Z; 11%Z; 15%Z; 17%Z; 19%Z].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.