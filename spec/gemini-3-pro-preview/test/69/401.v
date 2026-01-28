Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eqb x y then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => Z.leb x (count x l)) l in
  fold_right Z.max (-1) filtered.

Example test_search: search [1; 1; 1; 1; 8; 1; 1; 2; 2; 2; 2; 2; 3; 3; 4; 3; 3; 3; 3; 3] = 3.
Proof.
  compute. reflexivity.
Qed.