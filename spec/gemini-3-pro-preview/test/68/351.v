Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_aux (l : list Z) (idx : Z) (current : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => current
  | x :: xs =>
      let new_current :=
        if Z.even x then
          match current with
          | None => Some (x, idx)
          | Some (min_val, _) =>
              if x <? min_val then Some (x, idx) else current
          end
        else
          current
      in
      find_min_even_aux xs (idx + 1) new_current
  end.

Definition solution (l : list Z) : list Z :=
  match find_min_even_aux l 0 None with
  | Some (val, idx) => [val; idx]
  | None => []
  end.

Example test_case: solution [7%Z; 9%Z; 23%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 22%Z; 31%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 39%Z; 4%Z; 2%Z; 7%Z; 21%Z] = [2%Z; 21%Z].
Proof.
  compute.
  reflexivity.
Qed.