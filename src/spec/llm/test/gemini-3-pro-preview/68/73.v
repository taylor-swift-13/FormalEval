Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => best
    | x :: xs =>
      if x mod 2 =? 0 then
        match best with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (min_v, _) =>
          if x <? min_v then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) best
        end
      else aux xs (idx + 1) best
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [5; 11; 7; 9; 11; 2; 9; 9] = [2; 5].
Proof. reflexivity. Qed.