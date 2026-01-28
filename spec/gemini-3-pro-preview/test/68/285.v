Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition is_even (n : Z) : bool := Z.even n.

Fixpoint min_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs =>
      match min_list xs with
      | None => Some x
      | Some m => Some (Z.min x m)
      end
  end.

Fixpoint index_of (x : Z) (l : list Z) (i : Z) : option Z :=
  match l with
  | [] => None
  | h :: t => if x =? h then Some i else index_of x t (i + 1)
  end.

Definition pluck (arr : list Z) : list Z :=
  let evens := filter is_even arr in
  match min_list evens with
  | None => []
  | Some m =>
      match index_of m arr 0 with
      | Some i => [m; i]
      | None => []
      end
  end.

Example test_pluck: pluck [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 31%Z; 31%Z; 37%Z; 39%Z; 4%Z; 2%Z; 4%Z] = [2%Z; 20%Z].
Proof. reflexivity. Qed.