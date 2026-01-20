Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_100_300_400_500 :
  incr_list_spec [100%Z; 300%Z; 400%Z; 500%Z] [101%Z; 301%Z; 401%Z; 501%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.