Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if x =? y then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) filtered.

Example test_search: search [1%Z; 2%Z; 10%Z; 8%Z; 5%Z; 6%Z; 7%Z; 4%Z; 10%Z; 7%Z; 7%Z; 6%Z] = 1%Z.
Proof.
  reflexivity.
Qed.