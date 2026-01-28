Require Import Coq.Lists.List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
    match l with
    | [] => match best with
            | Some (v, i) => [v; i]
            | None => []
            end
    | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (v, _) => if x <? v then Some (x, idx) else best
          end
        else best
      in aux xs (idx + 1) new_best
    end
  in aux l 0 None.

Example test_case: solution [1%Z; 5%Z; 8%Z; 1%Z; 1%Z; 1%Z] = [8%Z; 2%Z].
Proof. reflexivity. Qed.