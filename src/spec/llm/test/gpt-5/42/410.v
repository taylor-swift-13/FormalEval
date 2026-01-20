Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_all_false :
  incr_list_spec [Z.b2z false; Z.b2z false; Z.b2z false; Z.b2z false; Z.b2z false]
                 [1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.