Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | x :: xs =>
    let acc' :=
      if Z.even x then
        match acc with
        | None => Some (x, idx)
        | Some (min_val, _) =>
          if x <? min_val then Some (x, idx) else acc
        end
      else acc
    in pluck_aux xs (idx + 1) acc'
  end.

Definition pluck (arr : list Z) : list Z :=
  match pluck_aux arr 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_pluck: pluck [7; 9; 1; 5; 10000; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 33; 35; 37; 39; 4; 2; 9; 3] = [2; 23].
Proof. reflexivity. Qed.