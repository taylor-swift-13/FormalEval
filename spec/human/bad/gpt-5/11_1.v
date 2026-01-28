Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* Spec *)
Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).

Example problem_11_example :
  problem_11_pre "111000" "101010" /\ problem_11_spec "111000" "101010" "010010".
Proof.
  split.
  (* Pre *)
  unfold problem_11_pre.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [|i1].
    + simpl. split; [right; reflexivity | right; reflexivity].
    + destruct i1 as [|i2].
      * simpl. split; [right; reflexivity | left; reflexivity].
      * destruct i2 as [|i3].
        { simpl. split; [right; reflexivity | right; reflexivity]. }
        { destruct i3 as [|i4].
          - simpl. split; [left; reflexivity | left; reflexivity].
          - destruct i4 as [|i5].
            + simpl. split; [left; reflexivity | right; reflexivity].
            + destruct i5 as [|i6].
              * simpl. split; [left; reflexivity | left; reflexivity].
              * exfalso; lia. }
  (* Spec *)
  unfold problem_11_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      simpl in Hi.
      destruct i as [|i1].
      * simpl. split.
        { intros _. reflexivity. }
        { intros Hneq. exfalso. simpl in Hneq. apply Hneq. reflexivity. }
      * destruct i1 as [|i2].
        { simpl. split.
          - intros Heq. exfalso. simpl in Heq. injection Heq as Hc. congruence.
          - intros _. reflexivity. }
        { destruct i2 as [|i3].
          { simpl. split.
            - intros _. reflexivity.
            - intros Hneq. exfalso. simpl in Hneq. apply Hneq. reflexivity. }
          { destruct i3 as [|i4].
            - simpl. split.
              + intros _. reflexivity.
              + intros Hneq. exfalso. simpl in Hneq. apply Hneq. reflexivity.
            - destruct i4 as [|i5].
              + simpl. split.
                * intros Heq. exfalso. simpl in Heq. injection Heq as Hc. congruence.
                * intros _. reflexivity.
              + destruct i5 as [|i6].
                * simpl. split.
                  { intros _. reflexivity. }
                  { intros Hneq. exfalso. simpl in Hneq. apply Hneq. reflexivity. }
                * exfalso; lia. }
Qed.