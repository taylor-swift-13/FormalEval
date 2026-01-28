Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_abca :
  problem_48_spec "abca"%string false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros HP.
    exfalso.
    assert (Hlt : (1 < String.length "abca"%string / 2)%nat).
    { replace (String.length "abca"%string) with 4%nat by reflexivity.
      replace (4 / 2)%nat with 2%nat by reflexivity.
      lia.
    }
    specialize (HP 1%nat Hlt).
    assert (Hneq : String.get 1%nat "abca"%string <>
                   String.get 2%nat "abca"%string).
    { intros Heq. simpl in Heq. discriminate Heq. }
    apply Hneq in HP.
    assumption.
Qed.