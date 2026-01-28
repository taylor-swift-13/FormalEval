Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (xs : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match xs with
    | [] => acc
    | x :: xs' =>
      let is_even := (x mod 2 =? 0) in
      let new_acc :=
        if is_even then
          match acc with
          | None => Some (x, idx)
          | Some (min_val, _) =>
            if x <? min_val then Some (x, idx) else acc
          end
        else acc
      in
      aux xs' (idx + 1) new_acc
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [2%Z; 22%Z; 8%Z; 25%Z; 10%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.