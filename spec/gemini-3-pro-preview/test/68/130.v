Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => map (fun y => x / y) xs
  end.

Example test_case: solve [0%Z; 3%Z; 3%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.