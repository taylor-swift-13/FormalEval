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

Example test_problem_38 : problem_38_spec "xzhjnclgnihoinfs" "hxzcjnnlgoihfins".
Proof.
  (* Unfold the specification to see the goals *)
  unfold problem_38_spec.
  
  (* Split the conjunction: Length Check and Character Check *)
  split.
  
  - (* 1. Prove lengths are equal *)
    reflexivity.
    
  - (* 2. Prove character mapping logic *)
    (* Simplify the expressions first (computes n = 14, L = 16) *)
    simpl.
    intros i Hi.
    
    (* Define a tactic to solve the logic for a concrete index i *)
    let solve_char_at_index :=
      simpl; (* Reduce (i+1) mod 3 and string lookups *)
      split; (* Split the implication (i <= 14 -> ...) /\ (~(i <= 14) -> ...) *)
      [ 
        (* Branch: i <= n *)
        intro H_le;
        (* Try to prove the left disjunct (i+1)%3 = 1 *)
        try (left; split; [ reflexivity | reflexivity ]);
        (* Try to prove the right disjunct (i+1)%3 = 2 or 0 *)
        try (right; split; [ (left; reflexivity) || (right; reflexivity) | reflexivity ]);
        (* If we are here but i > n (contradiction in this branch), solve by lia *)
        try (exfalso; lia)
      | 
        (* Branch: i > n *)
        intro H_gt;
        (* Try to prove equality directly *)
        try reflexivity;
        (* If we are here but i <= n (contradiction in this branch), solve by lia *)
        try (exfalso; apply H_gt; lia)
      ]
    in
    
    (* Iterate through indices 0 to 15 using destruct *)
    do 16 (destruct i; [ solve_char_at_index | ]).
    
    (* For i >= 16, it contradicts the hypothesis Hi : i < 16 *)
    exfalso; lia.
Qed.