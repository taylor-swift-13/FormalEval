Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Forward direction *)
    intros _ x H.
    simpl in H.
    (* Destruct the list membership hypothesis repeatedly *)
    repeat (destruct H as [H | H]; [subst; lia | ]).
    (* Handle the empty list case *)
    contradiction.
  - (* Backward direction *)
    intros _.
    reflexivity.
Qed.