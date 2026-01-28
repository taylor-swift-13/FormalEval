Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_square (n : Z) : bool :=
  let r := Z.sqrt n in
  (r * r =? n).

Fixpoint solve_aux (l : list Z) (i : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if is_square i then h else 0) + solve_aux t (i + 1)
  end.

Definition solve (l : list Z) : Z :=
  solve_aux l 0.

Example test_case:
  solve [1%Z; -1%Z; 1%Z; -1%Z; -99%Z; 0%Z; 1%Z; 1%Z; -1%Z; -6%Z; 1%Z; -2%Z; 1%Z; -1%Z; 1%Z; 1%Z; -80%Z; 30%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -184%Z.
Proof.
  reflexivity.
Qed.