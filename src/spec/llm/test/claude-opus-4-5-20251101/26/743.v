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

Example test_mixed_duplicates : remove_duplicates_spec [-10; 5; 2; 7; 5; -10; 8; 12; 12; 1; 0; -5; 9; -5; 0; 20; 20; -30; 14; -10; 11; -10] [2; 7; 8; 1; 9; -30; 14; 11].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.