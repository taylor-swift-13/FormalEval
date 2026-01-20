Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_idx (l : list Z) (idx : Z) (acc : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => acc
  | h :: t =>
    if Z.even h then
      match acc with
      | None => find_min_even_idx t (idx + 1) (Some (h, idx))
      | Some (min_val, _) =>
        if h <? min_val then find_min_even_idx t (idx + 1) (Some (h, idx))
        else find_min_even_idx t (idx + 1) acc
      end
    else find_min_even_idx t (idx + 1) acc
  end.

Definition solve (l : list Z) : list Z :=
  match find_min_even_idx l 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example test_case: solve [5%Z; 10%Z; 15%Z; 20%Z; 15%Z] = [10%Z; 1%Z].
Proof. reflexivity. Qed.