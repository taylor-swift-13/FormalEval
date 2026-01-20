Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (i : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | None => []
          | Some (v, idx) => [v; idx]
          end
  | x :: xs =>
    if x mod 2 =? 0 then
      let new_best :=
        match best with
        | None => Some (x, i)
        | Some (bv, bi) =>
          if x <? bv then Some (x, i)
          else Some (bv, bi)
        end
      in pluck_aux xs (i + 1) new_best
    else
      pluck_aux xs (i + 1) best
  end.

Definition pluck (arr : list Z) : list Z :=
  pluck_aux arr 0 None.

Example test_pluck: pluck [5; 100; 10; 15] = [10; 2].
Proof.
  reflexivity.
Qed.