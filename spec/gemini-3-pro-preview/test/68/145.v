Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pluck (arr : list Z) : list Z :=
  let fix aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
    match l with
    | [] => acc
    | h :: t =>
      let new_acc :=
        if Z.even h then
          match acc with
          | None => Some (h, idx)
          | Some (val, i) =>
            if h <? val then Some (h, idx) else acc
          end
        else acc
      in aux t (idx + 1) new_acc
    end
  in
  match aux arr 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: pluck [2; 6; 15; 10] = [2; 0].
Proof. reflexivity. Qed.