Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | x :: xs =>
      if Z.even x then
        let current := (x, idx) in
        let new_best :=
          match best with
          | None => Some current
          | Some (bv, bi) =>
              if x <? bv then Some current else Some (bv, bi)
          end
        in pluck_aux xs (idx + 1) new_best
      else
        pluck_aux xs (idx + 1) best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 21%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 0%Z; 1%Z; 10000%Z] = [0%Z; 64%Z].
Proof. reflexivity. Qed.