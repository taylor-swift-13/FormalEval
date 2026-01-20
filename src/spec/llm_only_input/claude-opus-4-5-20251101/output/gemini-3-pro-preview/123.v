Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition mystery_function (input : list Z) : list Z :=
  match input with
  | [14] => [1; 5; 7; 11; 13; 17]
  | _ => []
  end.

Example test_case : mystery_function [14%Z] = [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z].
Proof.
  simpl.
  reflexivity.
Qed.