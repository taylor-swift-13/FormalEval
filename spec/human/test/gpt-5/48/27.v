Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_case :
  problem_48_spec "aWas ait a car or a sacat I saw?b" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    assert (Hi : (0 < String.length "aWas ait a car or a sacat I saw?b" / 2)%nat).
    { simpl. lia. }
    specialize (H 0 Hi).
    simpl in H.
    discriminate H.
Qed.