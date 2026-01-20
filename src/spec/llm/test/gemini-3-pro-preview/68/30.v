Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      if Z.even x then
        match acc with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (min_val, _) =>
          if x <? min_val then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) acc
        end
      else aux xs (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example pluck_example : pluck [5%Z; 5%Z; 10%Z; 15%Z] = [10%Z; 2%Z].
Proof. reflexivity. Qed.