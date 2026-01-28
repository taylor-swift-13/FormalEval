Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint smallest_even_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : list Z :=
  match l with
  | [] => match acc with
          | Some (val, i) => [val; i]
          | None => []
          end
  | h :: t =>
      if Z.even h then
        match acc with
        | None => smallest_even_aux t (idx + 1) (Some (h, idx))
        | Some (min_val, _) =>
            if h <? min_val then smallest_even_aux t (idx + 1) (Some (h, idx))
            else smallest_even_aux t (idx + 1) acc
        end
      else smallest_even_aux t (idx + 1) acc
  end.

Definition smallest_even (l : list Z) : list Z :=
  smallest_even_aux l 0 None.

Example test_case: smallest_even [31; 8; 1; 1; 1; 1; 39; 1; 2; 2; 2; 2] = [2; 8].
Proof. reflexivity. Qed.