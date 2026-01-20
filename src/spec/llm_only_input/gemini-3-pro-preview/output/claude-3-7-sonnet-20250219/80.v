Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

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

Example test_case_a_false : is_happy_spec "a" false.
Proof.
  unfold is_happy_spec.
  split.
  - (* false = true -> happy "a" *)
    intros H.
    discriminate H.
  - (* happy "a" -> false = true *)
    unfold happy.
    intros [Hlen _].
    simpl in Hlen.
    (* Hlen is 3 <= 1, which is false *)
    (* We can derive a contradiction by reducing the inequality *)
    apply le_S_n in Hlen. (* reduces to 2 <= 0 *)
    inversion Hlen.
Qed.