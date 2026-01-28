Require Import Coq.Reals.Reals.

Open Scope R_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Example test_triangle_area : triangle_area_spec 5 3 7.5.
Proof.
  unfold triangle_area_spec.
  (* Replace INR 2 with 2 so that the field tactic can handle it *)
  replace (INR 2) with 2 by (simpl; field).
  (* Use field tactic to solve the equation of real numbers *)
  field.
  (* field generates subgoals to prove denominators are non-zero *)
  (* Subgoal 1: 2 <> 0 *)
  - apply IZR_neq; discriminate.
  (* Subgoal 2: 10 <> 0 (arising from the decimal representation 7.5 = 75/10) *)
  - apply IZR_neq; discriminate.
Qed.