Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | h :: t =>
      if Z.even h then
        match acc with
        | None => aux t (idx + 1) (Some (h, idx))
        | Some (min_v, min_i) =>
          if h <? min_v then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) acc
        end
      else aux t (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_pluck:
  pluck [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 9%Z; 35%Z; 39%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.