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

Example test_remove_duplicates_complex: remove_duplicates_spec [12; 1; 2; 2; 3; 3; 4; 2; 5; 5; 4; 6; 5; 5; 2; 5; 12; 1; 5; 2] [6].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.