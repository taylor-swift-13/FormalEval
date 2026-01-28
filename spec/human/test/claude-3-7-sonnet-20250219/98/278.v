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
  problem_98_spec "AEIOUaeiouBCDFGJKLmOryfbYpORjKDimUqVAEIOUaeiouBCDFGJTyfbYpORjKDimUqVsxzvGnKVWAbCCdEOpQrStUvWxYzxyZLtvGnPrsTxyzsxzvGnPrsTxyz" 9.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* The string length is 104 *)
  (* The indices are 0 to 103 *)
  (* Filter indices where index is even and character is uppercase vowel *)
  (* We check only even indices with uppercase vowel letters "A","E","I","O","U" *)

  (* By enumerating the string and checking these positions, the count is 9 *)

  reflexivity.
Qed.