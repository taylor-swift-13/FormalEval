Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if n =? h then 1 + count n t else count n t
  end.

Definition search (l : list Z) : Z :=
  let fix aux (rest : list Z) (best : Z) : Z :=
    match rest with
    | [] => best
    | h :: t =>
      if (h >? 0) && (count h l >=? h) && (h >? best)
      then aux t h
      else aux t best
    end
  in aux l (-1).

Example test_search:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 3%Z] = 3%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.