Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [1; 2; 2; -4; 1; -5; 0; 0; 3; 6; 7; 9; -9; 10; 10] [1; 2; 2; 1; 3; 6; 7; 9; 10; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.