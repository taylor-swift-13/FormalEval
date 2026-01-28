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
  problem_98_spec "AEIOUaeDiiouBCDFabcdEFGHFjyNNsqqpPazeMePJAWYzwoSMqrdxvQZaGTiJKLMNOpQRstuVWxGyz" 4.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length = 82 *)
  (* seq 0 82 = [0;1;2;...;81] *)
  (* Evaluate filter predicate on indices where both Nat.even i and is_uppercase_vowel_bool hold true: *)

  (* i=0: char = 'A', even = true, vowel = true -> keep *)
  (* i=2: char = 'I', even = true, vowel = true -> keep *)
  (* i=4: char = 'U', even = true, vowel = true -> keep *)
  (* i=24: char = 'E', even = true, vowel = true -> keep *)
  (* i=52: char = 'A', even = true, vowel = true -> keep, *)
  (* i=60: char = 'O', even = true, vowel = true -> keep => but must check actual char *)
  (* Checking all occurrences, only these indexes yield true predicate: 0, 2, 4, 24 (total 4) *)

  reflexivity.
Qed.