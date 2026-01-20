Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list bool) (res : list Z) : Prop :=
  res = List.map (fun b => Z.b2z b + 1) l.

Example incr_list_spec_bool :
  incr_list_spec [false; false; false; true; false] [1%Z; 1%Z; 1%Z; 2%Z; 1%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.