Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition specification (input : list Z) : list Z :=
  match input with
  | [n] => [2%Z; n - 2]
  | _ => []
  end.

Example specification_test:
  specification [5%Z] = [2%Z; 3%Z].
Proof.
  unfold specification; simpl.
  reflexivity.
Qed.