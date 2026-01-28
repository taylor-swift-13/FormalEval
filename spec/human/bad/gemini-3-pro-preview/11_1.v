Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.

(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* Definition of Specification *)
Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).

(* Proof for the Test Case *)
Example test_xor_example : problem_11_spec "111000" "101010" "010010".
Proof.
  unfold problem_11_spec.
  repeat split.
  - (* Verify Length a = Length b *)
    simpl. reflexivity.
  - (* Verify Length output = Length a *)
    simpl. reflexivity.
  - (* Verify XOR logic for each index *)
    intros i Hi.
    (* Unroll the loop 6 times for indices 0 to 5 *)
    do 6 (destruct i as [|i]; [
      (* Base case for the current index: simplify and verify logic *)
      simpl; split; intros H; [
        (* Subgoal 1: a[i] == b[i] -> output[i] == '0' *)
        (* If a[i] and b[i] are different, H is a contradiction (solve with discriminate) *)
        (* If they are same, output[i] must be '0' (solve with reflexivity) *)
        try discriminate; try reflexivity 
      | 
        (* Subgoal 2: a[i] != b[i] -> output[i] == '1' *)
        (* If a[i] and b[i] are same, H is a contradiction (solve with congruence) *)
        (* If they are different, output[i] must be '1' (solve with reflexivity) *)
        try congruence; try reflexivity
      ]
    | 
      (* Recursive step: continue to next index *)
    ]).
    
    (* For indices >= 6, the length hypothesis Hi gives a contradiction *)
    simpl in Hi. lia.
Qed.