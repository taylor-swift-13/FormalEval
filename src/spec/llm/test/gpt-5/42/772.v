Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list bool) (res : list Z) : Prop :=
  res = List.map (fun b : bool => if b then 2%Z else 1%Z) l.

Example incr_list_spec_case0 :
  incr_list_spec
    [true; false; false; true; true; false; false; true; true]
    [2%Z; 1%Z; 1%Z; 2%Z; 2%Z; 1%Z; 1%Z; 2%Z; 2%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.