Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec [-5%Z; 18%Z; 9%Z; 14%Z; -1%Z; 9%Z; -5%Z]
                 [-4%Z; 19%Z; 10%Z; 15%Z; 0%Z; 10%Z; -4%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.