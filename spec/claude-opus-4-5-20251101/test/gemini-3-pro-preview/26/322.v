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

Example test_remove_duplicates_complex: remove_duplicates_spec [-10%Z; 5%Z; -30%Z; 5%Z; -10%Z; 12%Z; 12%Z; 1%Z; 0%Z; -5%Z; 9%Z; 5%Z; 20%Z; 20%Z; -30%Z; 12%Z; 12%Z; 12%Z; 20%Z; 0%Z] [1%Z; -5%Z; 9%Z].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.