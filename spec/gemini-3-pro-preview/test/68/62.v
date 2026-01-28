Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_last_even (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | x :: xs => 
      let new_acc := if Z.even x then Some (x, idx) else acc in
      find_last_even xs (idx + 1) new_acc
  end.

Definition solution (l : list Z) : list Z :=
  match find_last_even l 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: solution [1; 3; 20; 7; 9] = [20; 2].
Proof. reflexivity. Qed.