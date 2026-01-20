Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [-29%Z; 13%Z; 11%Z; -29%Z] [-28%Z; 14%Z; 12%Z; -28%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.