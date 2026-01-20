Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
    match l with
    | [] =>
      match best with
      | None => []
      | Some (v, i) => [v; i]
      end
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (min_v, _) =>
          if x <? min_v then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) best
        end
      else aux xs (idx + 1) best
    end
  in aux arr 0 None.

Example test_pluck: pluck [5%Z; 11%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z; 11%Z] = [2%Z; 5%Z].
Proof. reflexivity. Qed.