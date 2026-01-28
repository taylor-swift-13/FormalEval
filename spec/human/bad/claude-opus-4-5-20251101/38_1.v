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
    let n := ((String.length input / 3) * 3 - 1)%nat in
    let L := String.length input in
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        ( (i <= n)%nat ->
          (
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\
        ( (~(i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

Example problem_38_test :
  problem_38_spec "uzfplzjfzcltmdly" "fuzzplzjftcllmdy".
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - simpl.
    intros i Hi.
    split.
    + intros Hle.
      destruct i as [|i0]; [left; split; reflexivity |].
      destruct i0 as [|i1]; [right; split; [left; reflexivity | reflexivity] |].
      destruct i1 as [|i2]; [right; split; [right; reflexivity | reflexivity] |].
      destruct i2 as [|i3]; [left; split; reflexivity |].
      destruct i3 as [|i4]; [right; split; [left; reflexivity | reflexivity] |].
      destruct i4 as [|i5]; [right; split; [right; reflexivity | reflexivity] |].
      destruct i5 as [|i6]; [left; split; reflexivity |].
      destruct i6 as [|i7]; [right; split; [left; reflexivity | reflexivity] |].
      destruct i7 as [|i8]; [right; split; [right; reflexivity | reflexivity] |].
      destruct i8 as [|i9]; [left; split; reflexivity |].
      destruct i9 as [|i10]; [right; split; [left; reflexivity | reflexivity] |].
      destruct i10 as [|i11]; [right; split; [right; reflexivity | reflexivity] |].
      destruct i11 as [|i12]; [left; split; reflexivity |].
      destruct i12 as [|i13]; [right; split; [left; reflexivity | reflexivity] |].
      destruct i13 as [|i14].
      * (* i = 14: n = 14, check if 14 <= 14 *)
        exfalso. simpl in Hle. lia.
      * (* i >= 15 *)
        exfalso. simpl in Hle. lia.
    + intros Hnle.
      destruct i as [|i0]; [exfalso; simpl in Hnle; lia |].
      destruct i0 as [|i1]; [exfalso; simpl in Hnle; lia |].
      destruct i1 as [|i2]; [exfalso; simpl in Hnle; lia |].
      destruct i2 as [|i3]; [exfalso; simpl in Hnle; lia |].
      destruct i3 as [|i4]; [exfalso; simpl in Hnle; lia |].
      destruct i4 as [|i5]; [exfalso; simpl in Hnle; lia |].
      destruct i5 as [|i6]; [exfalso; simpl in Hnle; lia |].
      destruct i6 as [|i7]; [exfalso; simpl in Hnle; lia |].
      destruct i7 as [|i8]; [exfalso; simpl in Hnle; lia |].
      destruct i8 as [|i9]; [exfalso; simpl in Hnle; lia |].
      destruct i9 as [|i10]; [exfalso; simpl in Hnle; lia |].
      destruct i10 as [|i11]; [exfalso; simpl in Hnle; lia |].
      destruct i11 as [|i12]; [exfalso; simpl in Hnle; lia |].
      destruct i12 as [|i13]; [exfalso; simpl in Hnle; lia |].
      destruct i13 as [|i14]; [exfalso; simpl in Hnle; lia |].
      destruct i14 as [|i15]; [reflexivity |].
      simpl in Hi. lia.
Qed.