Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      if Z.even x then
        match acc with
        | None => aux xs (idx + 1) (Some (x, idx))
        | Some (v, i) =>
          if x <? v then aux xs (idx + 1) (Some (x, idx))
          else aux xs (idx + 1) acc
        end
      else aux xs (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 9%Z; 11%Z; 13%Z; 20%Z; 15%Z; 17%Z; 19%Z; 21%Z; 25%Z; 27%Z; 29%Z; 31%Z; 9%Z; 35%Z; 34%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.