Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_test :
  incr_list_spec [5%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z]
                 [6%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.