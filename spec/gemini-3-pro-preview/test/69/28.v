Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec x h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let fix aux (current : list Z) : Z :=
    match current with
    | [] => -1
    | h :: t =>
      let c := count h l in
      let max_rest := aux t in
      if h <=? c then Z.max h max_rest else max_rest
    end
  in aux l.

Example test_search: search [2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z] = 2%Z.
Proof. reflexivity. Qed.