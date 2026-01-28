Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : list Z :=
  match l with
  | [] => match best with
          | Some (v, i) => [v; i]
          | None => []
          end
  | x :: xs =>
      let new_best :=
        if Z.even x then
          match best with
          | None => Some (x, idx)
          | Some (bv, _) =>
              if x <? bv then Some (x, idx) else best
          end
        else best
      in
      pluck_aux xs (idx + 1) new_best
  end.

Definition pluck (l : list Z) : list Z := pluck_aux l 0 None.

Example test_pluck: pluck [7%Z; 15%Z; 12%Z; 21%Z; 8%Z; 13%Z] = [8%Z; 4%Z].
Proof. reflexivity. Qed.