Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

Definition problem_38_pre (input : string) : Prop := True.

Definition problem_38_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (
    let k := (String.length input / 3)%nat in
    let n := (k * 3 - 1)%nat in
    let L := String.length input in

    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        ( (k > 0 /\ i <= n)%nat ->
          (
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\
        ( (~(k > 0 /\ i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

Example test_problem_38 : problem_38_spec "cc" "cc".
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - simpl.
    intros i Hi.
    split.
    + intros [H_k _]. inversion H_k.
    + intros _.
      destruct i.
      * reflexivity.
      * destruct i.
        -- reflexivity.
        -- exfalso; lia.
Qed.