Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.
Open Scope char_scope.

Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a" => c_out = "e" | "b" => c_out = "f" | "c" => c_out = "g" | "d" => c_out = "h"
  | "e" => c_out = "i" | "f" => c_out = "j" | "g" => c_out = "k" | "h" => c_out = "l"
  | "i" => c_out = "m" | "j" => c_out = "n" | "k" => c_out = "o" | "l" => c_out = "p"
  | "m" => c_out = "q" | "n" => c_out = "r" | "o" => c_out = "s" | "p" => c_out = "t"
  | "q" => c_out = "u" | "r" => c_out = "v" | "s" => c_out = "w" | "t" => c_out = "x"
  | "u" => c_out = "y" | "v" => c_out = "z" | "w" => c_out = "a" | "x" => c_out = "b"
  | "y" => c_out = "c" | "z" => c_out = "d"
  | _ => c_out = c_in
  end.

Definition problem_89_pre (s : string) : Prop := True.

Definition problem_89_spec (s : string) (output : string) : Prop :=
  String.length s = String.length output /\
  forall i, i < String.length s ->
    match String.get i s, String.get i output with
    | Some c_in, Some c_out => char_relation c_in c_out
    | _, _ => False
    end.

Example encrypt_hi_returns_lm : problem_89_spec "hi" "lm".
Proof.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i].
    + simpl. unfold char_relation. reflexivity.
    + destruct i as [|i].
      * simpl. unfold char_relation. reflexivity.
      * simpl in Hi.
        simpl.
        exfalso.
        assert (2 <= S (S i)) by lia.
        lia.
Qed.