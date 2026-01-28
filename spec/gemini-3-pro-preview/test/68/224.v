Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      if Z.even x then
        match acc with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (min_v, _) =>
          if x <? min_v then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) acc
        end
      else aux xs (i + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example pluck_example : pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 5%Z; 9%Z; 9%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.