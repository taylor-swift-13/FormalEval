Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (res : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => res
    | x :: xs =>
      let new_res :=
        if x mod 2 =? 0 then
          match res with
          | None => Some (x, i)
          | Some (v, _) => if x <? v then Some (x, i) else res
          end
        else res
      in aux xs (i + 1) new_res
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example pluck_example : pluck [1; 5; 7; 2; 0; 1] = [0; 4].
Proof. reflexivity. Qed.