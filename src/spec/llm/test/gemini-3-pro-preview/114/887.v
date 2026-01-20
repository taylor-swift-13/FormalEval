Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h val then 1 else 0) + count val t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (count x l) x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_search:
  search [100000%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; 2%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 2%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -1%Z.
Proof.
  reflexivity.
Qed.