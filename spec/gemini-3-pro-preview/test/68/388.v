Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (v, i) =>
          if x <? v then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) best
        end
      else aux xs (idx + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [10%Z; 9%Z; 8%Z; 6%Z; 33%Z; 4%Z; 19%Z; 3%Z; 2%Z; 1%Z; 7%Z] = [2%Z; 8%Z].
Proof. reflexivity. Qed.