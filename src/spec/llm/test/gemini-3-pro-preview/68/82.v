Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (l : list Z) : list Z :=
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
  match aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [5; 10; 15; 9; 20; 21; 10] = [10; 1].
Proof. reflexivity. Qed.