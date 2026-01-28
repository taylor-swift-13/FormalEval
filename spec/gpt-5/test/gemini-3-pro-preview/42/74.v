Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [4%Z; -2%Z; -3%Z; 1000%Z; 1000%Z] [5%Z; -1%Z; -2%Z; 1001%Z; 1001%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.