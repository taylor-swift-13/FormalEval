Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec [-5%Z; 20000%Z; -3%Z; -3%Z] [-4%Z; 20001%Z; -2%Z; -2%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.