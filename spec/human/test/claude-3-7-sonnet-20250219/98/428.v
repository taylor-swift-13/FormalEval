Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_example :
  problem_98_spec "AAEIOOUaeiuouBAabcdVWxWYzz" 5.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "AAEIOOUaeiuouBAabcdVWxWYzz" = 26 *)
  (* seq 0 26 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25] *)
  (* Filter by even indices and uppercase vowels: *)
  (* i=0: "A" (uppercase vowel), even -> true *)
  (* i=2: "E" (uppercase vowel), even -> true *)
  (* i=4: "O" (uppercase vowel), even -> true *)
  (* i=6: "U" (uppercase vowel), even -> true *)
  (* i=14: "A" (uppercase vowel), even -> true *)
  (* Others at even indices are not uppercase vowels *)
  (* Total count = 5 *)
  reflexivity.
Qed.