Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_test :
  incr_list_spec [2%Z; 501%Z; 0%Z; -1%Z; 500%Z] [3%Z; 502%Z; 1%Z; 0%Z; 501%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.