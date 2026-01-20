Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eqb val h then 1%nat else 0%nat) + count val t
  end.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => if x <=? Z.of_nat (count x l) then Z.max acc x else acc) l (-1).

Example test_case_1 : search [1; 3; 4; 6; 7; 8; 9; 10; 10; 10; 10; 10; 10; 9; 11; 12; 13; 14; 15] = 1.
Proof. reflexivity. Qed.