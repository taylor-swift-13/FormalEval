Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [-3; 20; -20; 25; -20; -10; 5; 3] [20; 25; 5; 3].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.