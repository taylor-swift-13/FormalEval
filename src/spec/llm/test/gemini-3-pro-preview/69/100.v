Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eqb n h then 1 + count n t else count n t
  end.

Definition search (l : list Z) : Z :=
  let fix aux (rem : list Z) (acc : Z) : Z :=
    match rem with
    | [] => acc
    | h :: t =>
        let c := count h l in
        let is_valid := (h >? 0) && (c >=? h) in
        let new_acc := if is_valid && (h >? acc) then h else acc in
        aux t new_acc
    end
  in aux l (-1).

Example test_search: search [1; 1; 1; 2; 2; 2; 2; 3; 3] = 2.
Proof. reflexivity. Qed.