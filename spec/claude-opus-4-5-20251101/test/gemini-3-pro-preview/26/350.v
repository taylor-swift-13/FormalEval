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

Example test_remove_duplicates_complex: remove_duplicates_spec 
  [2%Z; 3%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 9%Z; 9%Z; 9%Z; 10%Z; 12%Z; 11%Z; 12%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 18%Z; 19%Z; 20%Z; 3%Z; 7%Z] 
  [2%Z; 6%Z; 8%Z; 10%Z; 11%Z; 15%Z; 16%Z; 17%Z; 19%Z; 20%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.