Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [-1; 0; -4; -4; -5; -4; -4] [0; 1; -3; -3; -4; -3; -3].
Proof.
  unfold incr_list_spec.
  reflexivity.
Qed.