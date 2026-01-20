Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list (list bool)) (res : list Z) : Prop :=
  res = List.map (fun _ => 2%Z) (List.concat l).

Example incr_list_spec_true_true :
  incr_list_spec [[true; true]] [2%Z; 2%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.