Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [9%Z; 1%Z; -29%Z; -2%Z; 3%Z; 1%Z; -4%Z; -1%Z; -29%Z; 5%Z; 0%Z; 40000%Z; 9%Z; 1%Z; -10%Z; 9%Z; -4%Z]
    [10%Z; 2%Z; -28%Z; -1%Z; 4%Z; 2%Z; -3%Z; 0%Z; -28%Z; 6%Z; 1%Z; 40001%Z; 10%Z; 2%Z; -9%Z; 10%Z; -3%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.