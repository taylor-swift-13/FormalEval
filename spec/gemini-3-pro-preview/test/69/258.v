Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (n : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? n then 1 else 0) + count n t
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count x l >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_case_new : search [1; 2; 3; 4; 5; 7; 8; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15; 13] = 1.
Proof. reflexivity. Qed.