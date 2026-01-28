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
        | Some (min_v, min_i) =>
          if x <? min_v then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) acc
        end
      else aux xs (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck: pluck [10; 9; 8; 7; 7; 6; 5; 4; 3; 2; 1; 7; 4; 7] = [2; 9].
Proof. reflexivity. Qed.