Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (current_min : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => current_min
  | x :: xs =>
      if Z.even x then
        match current_min with
        | None => pluck_aux xs (idx + 1) (Some (x, idx))
        | Some (min_val, min_idx) =>
            if x <? min_val then pluck_aux xs (idx + 1) (Some (x, idx))
            else pluck_aux xs (idx + 1) current_min
        end
      else pluck_aux xs (idx + 1) current_min
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [7%Z; 6%Z; 15%Z; 2%Z; 0%Z; 8%Z; 10%Z; 8%Z] = [0%Z; 4%Z].
Proof. reflexivity. Qed.