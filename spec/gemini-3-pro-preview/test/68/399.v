Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if Z.even x then
        match best with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (v, _) =>
          if x <? v then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) best
        end
      else aux xs (i + 1) best
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example pluck_example : pluck [2%Z; 37%Z; 4%Z; 10%Z; 8%Z; 10%Z; 2%Z; 2%Z; 37%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.