Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : nat :=
  length (filter (Z.eqb x) lst).

Definition solution (lst : list Z) : Z :=
  let unique := filter (fun x => Nat.eqb (count_occurrences lst x) 1) lst in
  match unique with
  | [] => 0 
  | h :: t => fold_left Z.min t h
  end.

Example human_eval_test : solution [1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -6%Z; 2%Z; -1%Z] = -6%Z.
Proof. compute. reflexivity. Qed.