Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope char_scope.

Definition char_to_bool (c : ascii) : bool :=
  if ascii_dec c "1" then true else false.

Definition bool_to_char (b : bool) : ascii :=
  if b then "1" else "0".

Definition xor_ascii (c1 c2 : ascii) : ascii :=
  bool_to_char (xorb (char_to_bool c1) (char_to_bool c2)).

Definition string_xor_spec (a b result : string) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  let lr := list_ascii_of_string result in
  length lr = length la /\
  forall i, (i < length la)%nat ->
    nth i lr "0" = xor_ascii (nth i la "0") (nth i lb "0").

Example test_xor : string_xor_spec "101010" "010101" "111111".
Proof.
  (* Unfold the specification to see the list goals *)
  unfold string_xor_spec.
  
  (* Simplify the conversion from string to list_ascii and length computations *)
  simpl.
  
  (* Split the conjunction into Length equality and Pointwise equality *)
  split.
  
  - (* Case 1: Length equality *)
    reflexivity.
    
  - (* Case 2: Pointwise verification *)
    intros i H.
    (* The length of the string is 6. We check indices 0 to 5. *)
    (* We destruct i repeatedly to handle each specific index. *)
    destruct i.
    { (* i = 0 *) reflexivity. }
    destruct i.
    { (* i = 1 *) reflexivity. }
    destruct i.
    { (* i = 2 *) reflexivity. }
    destruct i.
    { (* i = 3 *) reflexivity. }
    destruct i.
    { (* i = 4 *) reflexivity. }
    destruct i.
    { (* i = 5 *) reflexivity. }
    
    (* For i >= 6, the hypothesis H (i < 6) is false *)
    exfalso.
    lia.
Qed.