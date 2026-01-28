Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (res : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => res
    | x :: xs =>
      let new_res :=
        if Z.even x then
          match res with
          | None => Some (x, i)
          | Some (min_v, _) =>
            if x <? min_v then Some (x, i) else res
          end
        else res
      in
      aux xs (i + 1) new_res
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example pluck_example : pluck [2; 5; 11; 7; 9; 11; 2] = [2; 0].
Proof. compute. reflexivity. Qed.