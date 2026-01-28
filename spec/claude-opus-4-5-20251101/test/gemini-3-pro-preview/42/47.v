Require Import List.
Require Import Reals.
Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (result : list R) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list: incr_list_spec [3.7%R; 0.1%R; 1.2%R] [4.7%R; 1.1%R; 2.2%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (3.7 + 1) with 4.7 by lra.
  replace (0.1 + 1) with 1.1 by lra.
  replace (1.2 + 1) with 2.2 by lra.
  reflexivity.
Qed.