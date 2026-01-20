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
        | Some (v, i) =>
          if h <? v then aux t (idx + 1) (Some (h, idx))
          else aux t (idx + 1) acc
        end
      else aux t (idx + 1) acc
    end
  in
  match aux arr 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck: pluck [2%Z; 4%Z; 7%Z; 6%Z; 8%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.