Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb v h then 1 else 0) + count v t
  end.

Definition search (l : list Z) : Z :=
  fold_right Z.max (-1) (filter (fun x => x <=? count x l) l).

Example test_search: search [1; 2; 4; 4; 4; 4] = 4.
Proof. reflexivity. Qed.