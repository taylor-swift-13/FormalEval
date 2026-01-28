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

Example test_problem_38 : problem_38_spec "The quick brown fox jumps over the lazy dog." "eThu qkicr bnowo fjx pumos rveh tle yazo dg.".
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - simpl.
    intros i Hi.
    let solve_char_at_index :=
      simpl;
      split;
      [ 
        intro H_le;
        try (left; split; [ reflexivity | reflexivity ]);
        try (right; split; [ (left; reflexivity) || (right; reflexivity) | reflexivity ]);
        try (exfalso; lia)
      | 
        intro H_gt;
        try reflexivity;
        try (exfalso; apply H_gt; lia)
      ]
    in
    do 44 (destruct i; [ solve_char_at_index | ]).
    exfalso; lia.
Qed.