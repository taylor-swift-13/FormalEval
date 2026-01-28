Require Import List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  if res then Forall (fun x => x < t) l else ~ Forall (fun x => x < t) l.

Example test_below_threshold : below_threshold_spec [3.5; 2.6445924145352944; 2.2; 1.1] 3 false.
Proof.
  unfold below_threshold_spec.
  intro H.
  inversion H.
  lra.
Qed.