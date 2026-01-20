Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      if Z.even x then
        match acc with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (best_v, _) =>
          if x <? best_v then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) acc
        end
      else aux xs (i + 1) acc
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck:
  pluck [5%Z; 4%Z; 11%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z; 4%Z] = [2%Z; 6%Z].
Proof.
  reflexivity.
Qed.