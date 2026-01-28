Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [11; -1; -2; -5; -3; -4; 5; 6; 0; 6; 7; -9; -9; 5; 10; -9] [11; 5; 6; 6; 7; 5; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.