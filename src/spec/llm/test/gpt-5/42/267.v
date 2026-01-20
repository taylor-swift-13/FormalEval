Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec [1%Z; 4%Z; 12%Z; 8%Z; 17%Z; 14%Z; 9%Z; 16%Z; -10%Z]
                 [2%Z; 5%Z; 13%Z; 9%Z; 18%Z; 15%Z; 10%Z; 17%Z; -9%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.