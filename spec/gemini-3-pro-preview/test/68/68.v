Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => best
  | x :: xs =>
    if Z.even x then
      match best with
      | None => pluck_aux xs (idx + 1) (Some (x, idx))
      | Some (best_val, _) =>
        if x <? best_val then pluck_aux xs (idx + 1) (Some (x, idx))
        else pluck_aux xs (idx + 1) best
      end
    else pluck_aux xs (idx + 1) best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck : pluck [101%Z; 20%Z; 202%Z] = [20%Z; 1%Z].
Proof. reflexivity. Qed.