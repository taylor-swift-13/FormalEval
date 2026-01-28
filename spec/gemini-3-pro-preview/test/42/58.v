Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [0; 0; 0; 100; 0] [1; 1; 1; 101; 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.