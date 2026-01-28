Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [-8; 5; 9; -2; 6; 5; 0; -1; -8; 3] [-7; 6; 10; -1; 7; 6; 1; 0; -7; 4].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.