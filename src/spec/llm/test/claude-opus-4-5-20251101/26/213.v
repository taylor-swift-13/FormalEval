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

Example test_remove_duplicates : remove_duplicates_spec [12%Z; 1%Z; 1%Z; 1%Z; 4%Z; 2%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 4%Z; 2%Z; 5%Z; 4%Z; 2%Z] [12%Z; 3%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.