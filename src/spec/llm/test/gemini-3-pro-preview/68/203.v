Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_helper (arr : list Z) (idx : Z) (current_best : option (Z * Z)) : option (Z * Z) :=
  match arr with
  | [] => current_best
  | x :: xs =>
      let new_best :=
        if x mod 2 =? 0 then
          match current_best with
          | None => Some (x, idx)
          | Some (best_val, _) =>
              if x <? best_val then Some (x, idx) else current_best
          end
        else current_best
      in
      pluck_helper xs (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_helper arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck_new: pluck [0; 7; 2; 4; 6; 4; 8; 10] = [0; 0].
Proof. reflexivity. Qed.