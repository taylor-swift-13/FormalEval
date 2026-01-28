Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec 2.5 2 3 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [H _].
    unfold is_int in H. destruct H as [z Hz].
    replace 2.5 with (5/2) in Hz by lra.
    apply (f_equal (fun v => 2 * v)) in Hz.
    replace (2 * (5 / 2)) with 5 in Hz by lra.
    rewrite <- mult_IZR in Hz.
    apply eq_IZR in Hz.
    lia.
Qed.