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

Example problem_38_example :
  problem_38_spec "uzfplzjfzcltmdly" "fuzzplzjftcllmdy".
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - unfold get_char. simpl.
    let n := ((String.length "uzfplzjfzcltmdly" / 3) * 3 - 1)%nat in
    let L := String.length "uzfplzjfzcltmdly" in
    assert (Hn: n = 14) by reflexivity.
    assert (HL: L = 16) by reflexivity.
    intros i Hi.
    assert (HiL: i < L) by lia.
    destruct (le_lt_dec i n) as [Hle | Hgt].
    + assert (Hle' : i <= n) by lia.
      destruct (Nat.modulo (i + 1) 3) eqn:Hmod.
      * assert (Hmod0: (i + 1) mod 3 = 0) by lia.
        assert (i = 2 \/ i = 5 \/ i = 8 \/ i = 11 \/ i = 14) by lia.
        subst.
        simpl.
        split; [lia|].
        right.
        split; [lia | reflexivity].
      * assert (Hmod1: (i + 1) mod 3 = 1) by lia.
        simpl.
        split; [lia|].
        left.
        split; [lia | reflexivity].
      * assert (Hmod2: (i + 1) mod 3 = 2) by lia.
        simpl.
        split; [lia|].
        right.
        split; [lia | reflexivity].
    + assert (~ (i <= n)) by lia.
      simpl.
      split; [lia|].
      reflexivity.
Qed.