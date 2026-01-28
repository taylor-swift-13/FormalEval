Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_aux (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | h :: t =>
      let new_acc :=
        if h mod 2 =? 0 then
          match acc with
          | None => Some (h, idx)
          | Some (min_val, _) =>
              if h <? min_val then Some (h, idx) else acc
          end
        else acc
      in
      find_min_even_aux t (idx + 1) new_acc
  end.

Definition solution (l : list Z) : list Z :=
  match find_min_even_aux l 0 None with
  | Some (v, i) => [v; i]
  | None => []
  end.

Example test_case: solution [101%Z; 202%Z] = [202%Z; 1%Z].
Proof. reflexivity. Qed.