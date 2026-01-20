Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      let new_acc :=
        if Z.even x then
          match acc with
          | None => Some (x, idx)
          | Some (min_val, _) =>
            if x <? min_val then Some (x, idx) else acc
          end
        else acc
      in aux xs (idx + 1) new_acc
    end
  in
  match aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_case: solution [5%Z; 10%Z; 15%Z; 9%Z; 20%Z; 10%Z] = [10%Z; 1%Z].
Proof. reflexivity. Qed.