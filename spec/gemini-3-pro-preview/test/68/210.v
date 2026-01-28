Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (b_val, _) =>
            if x <? b_val then Some (x, idx) else best
          end
        else best
      in pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 7] = [2; 8].
Proof. reflexivity. Qed.