Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [5%Z; 70000%Z; 5%Z; 0%Z; -1%Z; -8%Z; 3%Z; 10%Z]
                 [6%Z; 70001%Z; 6%Z; 1%Z; 0%Z; -7%Z; 4%Z; 11%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.