Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [2%Z; 200%Z; 300%Z] [3%Z; 201%Z; 301%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.