Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h val then S (count val t) else count val t
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? Z.of_nat (count x l)) l in
  fold_left Z.max filtered (-1).

Example test_case: search [2; 2; 3; 4; 4; 4; 5; 7; 5; 5; 2] = 2.
Proof. reflexivity. Qed.