Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | h :: t => (if h =? val then 1 else 0) + count val t
  end.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => count x lst >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [8; 8; 8; 8; 8; 8; 8; 8] = 8.
Proof. reflexivity. Qed.