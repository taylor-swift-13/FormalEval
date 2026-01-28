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

Example test_remove_duplicates_complex: 
  remove_duplicates_spec 
    [0; 1; 3; 5; 7; 9; 11; 13; 18; 15; 1000; 19; 13; 11; 13] 
    [0; 1; 3; 5; 7; 9; 18; 15; 1000; 19].
Proof.
  unfold remove_duplicates_spec.
  compute.
  reflexivity.
Qed.