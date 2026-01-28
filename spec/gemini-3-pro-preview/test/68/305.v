Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
        | Some (min_v, min_i) =>
          if x <? min_v then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) acc
        end
      else aux xs (i + 1) acc
    end in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck: pluck [1; 3; 5; 7; 5; 9] = [].
Proof. reflexivity. Qed.