Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_aux (l : list Z) (idx : Z) (min_val : option Z) (min_idx : Z) : list Z :=
  match l with
  | [] => match min_val with
          | Some v => [v; min_idx]
          | None => []
          end
  | h :: t =>
      if Z.even h then
        match min_val with
        | None => find_min_even_aux t (idx + 1) (Some h) idx
        | Some v => if h <? v then find_min_even_aux t (idx + 1) (Some h) idx
                    else find_min_even_aux t (idx + 1) min_val min_idx
        end
      else find_min_even_aux t (idx + 1) min_val min_idx
  end.

Definition solution (l : list Z) : list Z :=
  find_min_even_aux l 0 None 0.

Example test_case : solution [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 22%Z; 31%Z; 25%Z; 27%Z; 29%Z; 31%Z; 33%Z; 34%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 21%Z].
Proof.
  reflexivity.
Qed.