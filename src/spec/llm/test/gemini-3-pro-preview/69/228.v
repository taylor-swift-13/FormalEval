Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (lst : list Z) (x : Z) : Z :=
  match lst with
  | [] => 0
  | h :: t => (if x =? h then 1 else 0) + count_occurrences t x
  end.

Definition solve (lst : list Z) : Z :=
  fold_left (fun acc x => if (count_occurrences lst x =? x) && (acc <? x) then x else acc) lst (-1).

Example test_case: solve [2; 2; 3; 3; 4; 4; 4; 5; 6; 5; 5; 5] = 2.
Proof.
  reflexivity.
Qed.