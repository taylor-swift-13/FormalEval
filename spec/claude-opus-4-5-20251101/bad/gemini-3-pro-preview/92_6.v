Require Import Reals.
Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition is_int (r : R) : Prop := exists n : Z, IZR n = r.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec 2.2 2.2 2.2 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [H _].
    unfold is_int in H. destruct H as [n Hn].
    assert (H1: IZR 2 < 2.2) by lra.
    assert (H2: 2.2 < IZR 3) by lra.
    rewrite <- Hn in H1.
    rewrite <- Hn in H2.
    apply IZR_lt in H1.
    apply IZR_lt in H2.
    lia.
Qed.