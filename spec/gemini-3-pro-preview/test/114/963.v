Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | _ :: xs =>
    match xs with
    | [] => 0
    | y :: ys => y + solve ys
    end
  end.

Example test_case: solve [10%Z; -20%Z; 30%Z; -21%Z; -39%Z; 50%Z; -60%Z; 70%Z; -21%Z; -80%Z; 90%Z; -100%Z; 10%Z; -100%Z] = -201%Z.
Proof. reflexivity. Qed.