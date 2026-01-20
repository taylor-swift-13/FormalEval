Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (x : Z) : Z :=
  Z.of_nat (length (filter (fun y => Z.eqb x y) l)).

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count_occurrences l x) x) l in
  match candidates with
  | [] => -1
  | x :: xs => fold_right Z.min x xs
  end.

Example test_case: search [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -1%Z.
Proof.
  compute.
  reflexivity.
Qed.