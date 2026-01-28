Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let valid := filter (fun x => count x l >=? x) l in
  fold_right Z.max (-1) valid.

Example test_case: search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 3%Z; 9%Z; 10%Z] = 1%Z.
Proof. reflexivity. Qed.