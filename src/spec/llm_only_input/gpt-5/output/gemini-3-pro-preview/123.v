Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition specification (input : list Z) : list Z :=
  match input with
  | [14%Z] => [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z]
  | _ => []
  end.

Example test_case :
  specification [14%Z] = [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z].
Proof.
  unfold specification.
  reflexivity.
Qed.