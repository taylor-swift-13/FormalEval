Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_mixed : incr_list_spec [-5; 10; 100; 1000; 10000] [-4; 11; 101; 1001; 10001].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.