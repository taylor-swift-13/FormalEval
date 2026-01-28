Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (current_min : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => current_min
    | x :: xs =>
      let new_min :=
        if Z.even x then
          match current_min with
          | None => Some (x, idx)
          | Some (m_val, _) =>
            if x <? m_val then Some (x, idx) else current_min
          end
        else current_min
      in
      aux xs (idx + 1) new_min
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck: pluck [10%Z; 2%Z; 6%Z; 8%Z; 2%Z; 39%Z; 2%Z; 2%Z] = [2%Z; 1%Z].
Proof. reflexivity. Qed.