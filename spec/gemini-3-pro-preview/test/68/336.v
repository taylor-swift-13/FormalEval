Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (res : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => res
    | x :: xs =>
      let new_res :=
        if Z.even x then
          match res with
          | None => Some (x, idx)
          | Some (min_val, min_idx) =>
            if x <? min_val then Some (x, idx)
            else res
          end
        else res
      in
      aux xs (idx + 1) new_res
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [10; 8; 7; 6; 5; 4; 3; 7; 2; 1] = [2; 8].
Proof.
  reflexivity.
Qed.