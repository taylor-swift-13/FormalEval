Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.

Definition m_numerals : list string := [""; "m"].
Definition c_numerals : list string := [""; "c"; "cc"; "ccc"; "cd"; "d"; "dc"; "dcc"; "dccc"; "cm"].
Definition x_numerals : list string := [""; "x"; "xx"; "xxx"; "xl"; "l"; "lx"; "lxx"; "lxxx"; "xc"].
Definition i_numerals : list string := [""; "i"; "ii"; "iii"; "iv"; "v"; "vi"; "vii"; "viii"; "ix"].

Definition nth_default {A : Type} (default : A) (l : list A) (n : nat) : A :=
  nth n l default.

Definition int_to_mini_roman_spec (number : nat) (result : string) : Prop :=
  1 <= number <= 1000 /\
  let thousands := nth_default "" m_numerals (number / 1000) in
  let hundreds := nth_default "" c_numerals ((number mod 1000) / 100) in
  let tens := nth_default "" x_numerals ((number mod 100) / 10) in
  let ones := nth_default "" i_numerals (number mod 10) in
  result = (thousands ++ hundreds ++ tens ++ ones)%string.

Example test_int_to_mini_roman_19 : int_to_mini_roman_spec 19 "xix".
Proof.
  (* Unfold the specification *)
  unfold int_to_mini_roman_spec.
  
  (* Split the conjunction into range check and result check *)
  split.
  
  - (* Subgoal 1: Prove 1 <= 19 <= 1000 *)
    split.
    + (* Prove 1 <= 19 *)
      apply Nat.leb_le. reflexivity.
    + (* Prove 19 <= 1000 *)
      apply Nat.leb_le. reflexivity.
      
  - (* Subgoal 2: Prove "xix" is the correct result *)
    unfold nth_default.
    (* Simplify arithmetic and list operations *)
    simpl.
    (* Verify string equality *)
    reflexivity.
Qed.