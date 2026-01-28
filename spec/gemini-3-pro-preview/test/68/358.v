Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | None => []
          | Some (v, i) => [v; i]
          end
  | x :: xs =>
    let new_best :=
      if Z.even x then
        match best with
        | None => Some (x, idx)
        | Some (v, _) => if x <? v then Some (x, idx) else best
        end
      else best
    in pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z :=
  pluck_aux l 0 None.

Example test_pluck: pluck [0%Z; 7%Z; 2%Z; 3%Z; 4%Z; 6%Z; 1%Z; 8%Z; 10%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.