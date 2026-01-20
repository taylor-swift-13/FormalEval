Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (x : Z) (l : list Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solve (l : list Z) : Z :=
  let uniques := filter (fun x => Nat.eqb (count_occurrences x l) 1) l in
  match uniques with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case : solve [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; 4%Z; 1%Z; 6%Z; 2%Z; -1%Z; -6%Z] = -8%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.