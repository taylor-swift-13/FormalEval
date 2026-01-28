Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; 7%Z; 40000%Z; 9%Z; -10%Z] [2%Z; -1%Z; 4%Z; -3%Z; 6%Z; 8%Z; 40001%Z; 10%Z; -9%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.