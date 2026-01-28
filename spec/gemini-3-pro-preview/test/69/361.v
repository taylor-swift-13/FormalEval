Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb val h then 1 else 0) + count val t
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => Z.eqb (count x l) x) l in
  fold_left Z.max filtered (-1).

Example test_case_2:
  search [1; 1; 1; 1; 1; 2; 2; 2; 2; 17; 3; 3; 19; 3; 4; 4; 4; 3; 4; 19] = 4.
Proof. reflexivity. Qed.