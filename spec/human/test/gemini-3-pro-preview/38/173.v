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
    (* Use limit instead of n to correctly handle cases where length < 3 *)
    let limit := ((String.length input / 3) * 3)%nat in
    let L := String.length input in

    (* 3. For all indices i, assertions must hold *)
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        (* Case 1: i < limit (part of a cyclic group) *)
        ( (i < limit)%nat ->
          (
            (* Subcase 1: (i+1)%3 = 1 *)
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/

            (* Subcase 2: (i+1)%3 = 2 or 0 *)
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\

        (* Case 2: i >= limit (leftover characters) *)
        ( (~(i < limit)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

Example test_problem_38 : problem_38_spec "c" "c".
Proof.
  (* Unfold the specification *)
  unfold problem_38_spec.
  
  (* Split the conjunction: Length Check and Character Check *)
  split.
  
  - (* 1. Prove lengths are equal *)
    reflexivity.
    
  - (* 2. Prove character mapping logic *)
    simpl.
    intros i Hi.
    
    (* For "c", length is 1, limit is 0. *)
    (* i must be 0 due to Hi : i < 1 *)
    destruct i.
    + (* i = 0 *)
      split.
      * (* Case i < 0 is impossible *)
        intro H_lt. exfalso. lia.
      * (* Case ~(i < 0) is true, check identity mapping *)
        intro H_nlt. reflexivity.
    + (* i >= 1 contradicts Hi *)
      exfalso. lia.
Qed.