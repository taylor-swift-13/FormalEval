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

Example test_remove_duplicates :
  remove_duplicates_spec [1; 2; 3; 4; 4; 6; 7; 8; 9] [1; 2; 3; 6; 7; 8; 9].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.