Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_aux (l : list Z) (idx : Z) (current : option (Z * Z)) : list Z :=
  match l with
  | [] => match current with
          | Some (val, i) => [val; i]
          | None => []
          end
  | x :: xs =>
      let new_current :=
        if Z.even x then
          match current with
          | None => Some (x, idx)
          | Some (min_val, _) =>
              if x <? min_val then Some (x, idx) else current
          end
        else current
      in
      find_min_even_aux xs (idx + 1) new_current
  end.

Definition solution (l : list Z) : list Z :=
  find_min_even_aux l 0 None.

Example test_case_1 : solution [5; 10; 16; 9; 20; 10] = [10; 1].
Proof. reflexivity. Qed.