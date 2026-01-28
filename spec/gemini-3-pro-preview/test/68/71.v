Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (current : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => current
    | x :: xs =>
      if Z.even x then
        match current with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (min_val, min_idx) =>
          if x <? min_val then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) current
        end
      else aux xs (idx + 1) current
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [1%Z; 304%Z; 5%Z; 9%Z] = [304%Z; 1%Z].
Proof. reflexivity. Qed.