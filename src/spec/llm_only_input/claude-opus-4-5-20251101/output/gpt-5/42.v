Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_empty : incr_list_spec nil nil.
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.