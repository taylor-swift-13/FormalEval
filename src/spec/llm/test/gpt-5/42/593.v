Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-5%Z; -4%Z; 12%Z; -3%Z; -2%Z; 0%Z; -2%Z; 90000%Z; 90000%Z; 12%Z]
    [-4%Z; -3%Z; 13%Z; -2%Z; -1%Z; 1%Z; -1%Z; 90001%Z; 90001%Z; 13%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.