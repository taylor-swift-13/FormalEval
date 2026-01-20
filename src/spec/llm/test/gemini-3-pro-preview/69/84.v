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
  let filtered := filter (fun x => x <=? count x l) l in
  fold_right Z.max (-1) filtered.

Example test_search : search [2; 4; 4; 4; 3] = -1.
Proof.
  reflexivity.
Qed.