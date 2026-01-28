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

(* Pre: no additional constraints for `encode/decode_cyclic` by default *)
Definition problem_38_pre (input : string) : Prop := True.

Definition problem_38_spec (input output : string) : Prop :=
  (* 1. Basic constraint: lengths must be equal *)
  String.length input = String.length output /\
  (
    (* 2. Define constants *)
    let n := ((String.length input / 3) * 3 - 1)%nat in
    let L := String.length input in

    (* 3. For all indices i, assertions must hold *)
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        (* Case 1: i <= n *)
        ( (i <= n)%nat ->
          (
            (* Subcase 1: (i+1)%3 = 1 *)
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/

            (* Subcase 2: (i+1)%3 = 2 or 0 *)
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\

        (* Case 2: i > n *)
        ( (~(i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

Example test_problem_38 : problem_38_spec "" "".
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - simpl. intros i Hi.
    exfalso. lia.
Qed.