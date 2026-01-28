Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (current : option (Z * Z)) : list Z :=
  match arr with
  | [] => match current with
          | Some (v, i) => [v; i]
          | None => []
          end
  | x :: xs =>
    if Z.even x then
      match current with
      | None => pluck_aux xs (idx + 1) (Some (x, idx))
      | Some (best_v, _) =>
        if x <? best_v then pluck_aux xs (idx + 1) (Some (x, idx))
        else pluck_aux xs (idx + 1) current
      end
    else pluck_aux xs (idx + 1) current
  end.

Definition pluck (arr : list Z) : list Z :=
  pluck_aux arr 0 None.

Example pluck_example : pluck [2; 4; 5; 10; 2; 2; 2] = [2; 0].
Proof. reflexivity. Qed.