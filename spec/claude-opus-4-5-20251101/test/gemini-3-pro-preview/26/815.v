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

Example test_remove_duplicates_long:
  remove_duplicates_spec
    [1; 3; 3; 3; 3; 4; 4; 5; 5; 5; 6; 7; 8; 9; 9; 1001; 9; 9; 10; 11; 19; 6; 12; 12; 12; 13; 13; 13; 16; 14; 15; 16; 17; 18; 19; 20; 18; 13; 12]
    [1; 7; 8; 1001; 10; 11; 14; 15; 17; 20].
Proof.
  unfold remove_duplicates_spec.
  reflexivity.
Qed.