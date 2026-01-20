Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [1%Z; 10000%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 100%Z; 1%Z; 1%Z] [2%Z; 10001%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 101%Z; 2%Z; 2%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.