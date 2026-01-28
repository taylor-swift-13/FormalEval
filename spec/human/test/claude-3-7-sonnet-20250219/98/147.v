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
  problem_98_spec
    "yfUFjyNNsqqpPazeabcdEFGHFjyNNsqqpPazeMePJwoSMqrdxvQZaGTiJKLMNOpQRstuVWxQZaGTqVsxzvGn"
    2.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length of input is 84 *)
  (* seq 0 84 = [0;1;2;...;83] *)
  (* Evaluate filter predicate for all indices: *)
  (* We check indices i where Nat.even i = true and c is uppercase vowel: *)
  (* The only indexes where predicate true are 4 and 62 (characters 'E' at pos 4 and 'A' at pos 62) *)
  (* So length = 2 *)
  reflexivity.
Qed.