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
  remove_duplicates_spec [999; 5; 3; 5; -10; 8; 12; 12; 1; -5; 5; -5; 19; -6; 20; -30; 12; -10; 2]
                         [999; 3; 8; 1; 19; -6; 20; -30; 2].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.