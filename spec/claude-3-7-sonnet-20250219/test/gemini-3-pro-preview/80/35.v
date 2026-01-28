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

Example test_case : is_happy_spec " this is aao comment" false.
Proof.
  unfold is_happy_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    unfold happy in H.
    destruct H as [_ H].
    specialize (H 9).
    assert (Hlen : 9 + 2 < String.length " this is aao comment").
    { simpl. lia. }
    apply H in Hlen.
    simpl in Hlen.
    destruct Hlen as [Hneq _].
    exfalso.
    apply Hneq.
    reflexivity.
Qed.