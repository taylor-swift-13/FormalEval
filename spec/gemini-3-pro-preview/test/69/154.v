Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occurrences t x
  end.

Definition search (l : list Z) : Z :=
  let fix aux (rem : list Z) (current_max : Z) : Z :=
    match rem with
    | [] => current_max
    | h :: t =>
      let c := count_occurrences l h in
      let new_max := if c >=? h then Z.max current_max h else current_max in
      aux t new_max
    end in
  aux l (-1).

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 14%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 1%Z] = 3%Z.
Proof. reflexivity. Qed.