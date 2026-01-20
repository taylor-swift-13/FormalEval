Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let fix aux (l : list Z) (i : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | x :: xs =>
      if Z.even x then
        match acc with
        | None => aux xs (i + 1) (Some (x, i))
        | Some (v, _) =>
          if x <? v then aux xs (i + 1) (Some (x, i))
          else aux xs (i + 1) acc
        end
      else aux xs (i + 1) acc
    end
  in
  match aux l 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: solve [101%Z; 202%Z; 303%Z] = [202%Z; 1%Z].
Proof. reflexivity. Qed.