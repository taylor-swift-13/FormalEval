Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : list Z :=
  match l with
  | [] => match acc with
          | None => []
          | Some (val, i) => [val; i]
          end
  | x :: xs => 
      if Z.even x then
        match acc with
        | None => pluck_aux xs (idx + 1) (Some (x, idx))
        | Some (val, i) => 
            if x <? val then pluck_aux xs (idx + 1) (Some (x, idx))
            else pluck_aux xs (idx + 1) acc
        end
      else pluck_aux xs (idx + 1) acc
  end.

Definition pluck (l : list Z) : list Z :=
  pluck_aux l 0 None.

Example test_pluck: pluck [2; 2; 4; 8; 10; 2] = [2; 0].
Proof. reflexivity. Qed.