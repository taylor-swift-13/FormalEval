Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.eqb (count x l) x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_search_new: search [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z] = -1%Z.
Proof. reflexivity. Qed.