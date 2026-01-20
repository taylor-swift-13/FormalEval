Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (arr : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => best
  | x :: xs =>
    let new_best :=
      if Z.even x then
        match best with
        | None => Some (x, idx)
        | Some (best_val, _) =>
          if x <? best_val then Some (x, idx) else best
        end
      else best
    in
    pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck : pluck [10%Z; 15%Z; 20%Z] = [10%Z; 0%Z].
Proof. reflexivity. Qed.