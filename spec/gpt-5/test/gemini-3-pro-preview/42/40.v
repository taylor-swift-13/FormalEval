Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [2; 200; 2; 2; 2] [3; 201; 3; 3; 3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.