Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution_aux (l : list Z) (is_odd_idx : bool) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      let rest := solution_aux xs (negb is_odd_idx) in
      if is_odd_idx then
        if Z.odd x then x + rest else rest
      else
        rest
  end.

Definition solution (l : list Z) : Z := solution_aux l false.

Example test_case_2 : solution [1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -6%Z; 1%Z; 40%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 30%Z; -1%Z; -51%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; -1%Z] = -53%Z.
Proof. reflexivity. Qed.