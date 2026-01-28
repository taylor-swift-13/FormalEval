Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_xywzx :
  problem_48_spec "xywzx"%string false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hpal.
    exfalso.
    specialize (Hpal 1).
    assert (Hlt : (1 < String.length "xywzx"%string / 2)%nat) by (simpl; lia).
    specialize (Hpal Hlt).
    simpl in Hpal.
    destruct (Ascii.ascii_dec "y"%char "z"%char) as [Heq | Hneq]; [inversion Heq|].
    injection Hpal as Hyz. apply Hneq in Hyz. contradiction.
Qed.