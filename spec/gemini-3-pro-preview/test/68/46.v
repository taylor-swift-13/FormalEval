Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even (l : list Z) (idx : Z) : option (Z * Z) :=
  match l with
  | [] => None
  | x :: xs =>
    let res := find_min_even xs (idx + 1) in
    if Z.even x then
      match res with
      | None => Some (x, idx)
      | Some (min_val, _) => if x <=? min_val then Some (x, idx) else res
      end
    else res
  end.

Definition solution (l : list Z) : list Z :=
  match find_min_even l 0 with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: solution [6; 6; 4; 2; 0; 8; 10] = [0; 4].
Proof. reflexivity. Qed.