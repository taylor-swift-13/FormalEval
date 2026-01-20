Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x : Z => x + 1%Z) l.

Example incr_list_spec_case1 :
  incr_list_spec [0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 1%Z]
                 [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.