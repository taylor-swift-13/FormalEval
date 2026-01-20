Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (bx, bi) =>
            if x <? bx then Some (x, idx) else best
          end
        else best
      in aux xs (idx + 1) new_best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [0%Z; 7%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 2%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.