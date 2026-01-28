Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (acc : option (Z * Z)) : list Z :=
    match l with
    | [] =>
      match acc with
      | Some (val, idx) => [val; idx]
      | None => []
      end
    | x :: xs =>
      if Z.even x then
        match acc with
        | Some (min_val, min_idx) =>
          if x <? min_val then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) acc
        | None => aux xs (i + 1) (Some (x, i))
        end
      else aux xs (i + 1) acc
    end
  in aux arr 0 None.

Example test_pluck_1: pluck [10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 21%Z; 10000%Z; 27%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 1%Z; 10000%Z; 0%Z; 1%Z; 10000%Z; 10000%Z] = [0%Z; 65%Z].
Proof. reflexivity. Qed.