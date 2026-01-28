Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Definition happy (s : string) : Prop :=
  String.length s >= 3 /\
  forall i : nat,
    i + 2 < String.length s ->
    let a := String.get i s in
    let b := String.get (i + 1) s in
    let c := String.get (i + 2) s in
    match a, b, c with
    | Some a', Some b', Some c' =>
        a' <> b' /\ a' <> c' /\ b' <> c'
    | _, _, _ => True
    end.

Definition is_happy_spec (s : string) (res : bool) : Prop :=
  res = true <-> happy s.

Example test_case : is_happy_spec "abbaacbaccb" false.
Proof.
  unfold is_happy_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    unfold happy in H.
    destruct H as [_ H].
    specialize (H 0).
    simpl in H.
    assert (Hcond : 2 < 11). { lia. }
    apply H in Hcond.
    destruct Hcond as [_ [_ Hneq]].
    exfalso.
    apply Hneq.
    reflexivity.
Qed.