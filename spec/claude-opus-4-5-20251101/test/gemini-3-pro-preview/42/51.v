Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_custom: incr_list_spec [1%Z; 10000%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 100%Z; 1%Z; 1%Z] [2%Z; 10001%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 101%Z; 2%Z; 2%Z].
Proof.
  unfold incr_list_spec.
  reflexivity.
Qed.