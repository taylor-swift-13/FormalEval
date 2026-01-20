Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [1%Z; 49998%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 8%Z; 9%Z; -10%Z; 7%Z; 7%Z]
                 [2%Z; 49999%Z; -1%Z; 4%Z; -3%Z; 6%Z; -5%Z; 8%Z; -7%Z; 9%Z; 10%Z; -9%Z; 8%Z; 8%Z].
Proof.
  unfold incr_list_spec.
  compute.
  reflexivity.
Qed.