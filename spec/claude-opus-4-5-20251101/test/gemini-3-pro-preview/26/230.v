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

Example test_remove_duplicates_complex: remove_duplicates_spec [1; 2; 3; -30; 1; 4; -10; 5; 7; 6; 17; 8; 9; 10; 3; 12; 14; 16; 18; 19; 20; 18; 10; 12; 7; 3; 14; 16; 10; 18; 19; 20; 7; 10; 20; 16; 18] [2; -30; 4; -10; 5; 6; 17; 8; 9].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.