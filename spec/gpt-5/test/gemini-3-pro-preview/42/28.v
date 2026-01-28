Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [0%Z; 0%Z; 0%Z; 6%Z; 0%Z; 0%Z; 0%Z] [1%Z; 1%Z; 1%Z; 7%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold incr_list_spec.
  reflexivity.
Qed.