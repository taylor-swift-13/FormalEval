Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec
    [90000%Z; 4%Z; 8%Z; -29%Z; 79999%Z; 16%Z; 20%Z; 10%Z; 79999%Z]
    [90001%Z; 5%Z; 9%Z; -28%Z; 80000%Z; 17%Z; 21%Z; 11%Z; 80000%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.