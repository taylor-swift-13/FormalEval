Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_idx_aux (l : list Z) (idx : Z) (current_min : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => current_min
  | x :: xs =>
      let new_min :=
        if Z.even x then
          match current_min with
          | None => Some (x, idx)
          | Some (m_val, m_idx) =>
              if x <? m_val then Some (x, idx) else current_min
          end
        else current_min
      in
      find_min_even_idx_aux xs (idx + 1) new_min
  end.

Definition solve (l : list Z) : list Z :=
  match find_min_even_idx_aux l 0 None with
  | None => []
  | Some (val, idx) => [val; idx]
  end.

Example example_test_case : solve [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 21%Z].
Proof.
  reflexivity.
Qed.