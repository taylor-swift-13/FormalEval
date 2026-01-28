Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      let new_best :=
        if x mod 2 =? 0 then
          match best with
          | None => Some (x, idx)
          | Some (min_val, _) =>
              if x <? min_val then Some (x, idx) else best
          end
        else best
      in
      pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [0; 7; 2; 4; 8; 10; 10; 2; 10] = [0; 0].
Proof. reflexivity. Qed.