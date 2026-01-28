Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs => Some (fold_left Z.min xs x)
  end.

Definition max_list (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs => Some (fold_left Z.max xs x)
  end.

Definition solution (l : list Z) : Z :=
  let negs := filter (fun x => x <? 0) l in
  match negs with
  | [] => match min_list l with Some m => m | None => 0 end
  | _ => match min_list negs, max_list negs with
         | Some mn, Some mx => mn + mx
         | _, _ => 0
         end
  end.

Example test_case_1: solution [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; 0%Z; -99%Z; -1%Z; 90%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -70%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z; -1%Z; 1%Z] = -100%Z.
Proof. reflexivity. Qed.