Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? x then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let max_val := fold_right Z.max 0 l in
  let fix aux (k : Z) (fuel : nat) {struct fuel} : Z :=
    match fuel with
    | 0%nat => -1
    | S n =>
        if k <=? 0 then -1
        else if count k l >=? k then k
        else aux (k - 1) n
    end
  in aux max_val (S (Z.to_nat max_val)).

Example test_search:
  search [1; 1; 1; 2; 2; 3; 3; 4; 7; 4; 4; 4; 4; 9; 4; 4; 3] = 4.
Proof.
  reflexivity.
Qed.