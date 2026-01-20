Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_mixed :
  incr_list_spec
    [IZR 2%Z; (IZR 7%Z)/(IZR 2%Z); IZR (-4%Z); IZR 0%Z; IZR 5000000000%Z]
    [IZR 2%Z + 1; (IZR 7%Z)/(IZR 2%Z) + 1; IZR (-4%Z) + 1; IZR 0%Z + 1; IZR 5000000000%Z + 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.