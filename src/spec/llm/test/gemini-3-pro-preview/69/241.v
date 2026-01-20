Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if x =? y then 1 else 0) + count_occurrences x tl
  end.

Definition search (l : list Z) : Z :=
  let fix aux (rem : list Z) (acc : Z) :=
    match rem with
    | [] => acc
    | x :: xs =>
      let count := count_occurrences x l in
      let valid := (count >=? x) && (x >? 0) in
      let new_acc := if valid && (x >? acc) then x else acc in
      aux xs new_acc
    end
  in aux l (-1).

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 3%Z.
Proof.
  compute.
  reflexivity.
Qed.