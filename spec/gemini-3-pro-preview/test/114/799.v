Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solution (l : list Z) : Z :=
  let candidates := filter (fun x => negb (Nat.even (count x l))) l in
  match candidates with
  | [] => 0
  | h :: t => fold_right Z.min h t
  end.

Example test_case: solution [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 50%Z] = -100%Z.
Proof.
  compute. reflexivity.
Qed.