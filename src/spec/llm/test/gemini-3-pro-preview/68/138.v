Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (res : option (Z * Z)) :=
    match l with
    | [] => res
    | x :: xs =>
      if (x mod 2 =? 0) then
        match res with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (v, idx) =>
          if (x <? v) then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) res
        end
      else aux xs (i + 1) res
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [2; 4; 6; 8; 10; 2] = [2; 0].
Proof. reflexivity. Qed.