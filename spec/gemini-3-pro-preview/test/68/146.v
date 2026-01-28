Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (res : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => res
    | x :: xs =>
      if Z.even x then
        match res with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (min_val, _) =>
          if x <? min_val then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) res
        end
      else aux xs (i + 1) res
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [0; 2; 4; 6; 8; 10; 1; 3; 5; 6; 9; 6; 9] = [0; 0].
Proof. reflexivity. Qed.