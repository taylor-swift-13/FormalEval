Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_helper (l : list Z) (current_min : option Z) : option Z :=
  match l with
  | [] => current_min
  | x :: xs =>
      if Z.even x then
        match current_min with
        | None => find_min_even_helper xs (Some x)
        | Some m => if x <? m then find_min_even_helper xs (Some x) else find_min_even_helper xs (Some m)
        end
      else find_min_even_helper xs current_min
  end.

Definition find_min_even (l : list Z) : option Z :=
  find_min_even_helper l None.

Fixpoint find_index (l : list Z) (target : Z) (idx : Z) : option Z :=
  match l with
  | [] => None
  | x :: xs =>
      if x =? target then Some idx
      else find_index xs target (idx + 1)
  end.

Definition pluck (arr : list Z) : list Z :=
  match find_min_even arr with
  | None => []
  | Some min_val =>
      match find_index arr min_val 0 with
      | None => []
      | Some idx => [min_val; idx]
      end
  end.

Example pluck_example : pluck [7%Z; 9%Z; 1%Z; 5%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z] = [2%Z; 22%Z].
Proof. reflexivity. Qed.