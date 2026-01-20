Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition rounded_avg (l : list Z) : Z :=
  match l with
  | n :: m :: _ => if n >? m then -1 else (n + m + 1) / 2
  | _ => -1
  end.

Example test_case: rounded_avg [2000%Z; 1999%Z] = (-1)%Z.
Proof. reflexivity. Qed.