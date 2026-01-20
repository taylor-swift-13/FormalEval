
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition digit_to_char (d : nat) : option ascii :=
  match d with
  | 0 => Some "0"%char
  | 1 => Some "1"%char
  | 2 => Some "2"%char
  | 3 => Some "3"%char
  | 4 => Some "4"%char
  | 5 => Some "5"%char
  | 6 => Some "6"%char
  | 7 => Some "7"%char
  | 8 => Some "8"%char
  | 9 => Some "9"%char
  | _ => None
  end.

Fixpoint change_base_digits (x base : nat) : option (list nat) :=
  match x with
  | 0 => Some []
  | _ =>
    match change_base_digits (x / base) base with
    | None => None
    | Some l =>
      let r := x mod base in
      if Nat.ltb r 10 then Some (if l =? [] then [r] else l ++ [r]) else None
    end
  end.

Fixpoint digits_to_string (l : list nat) : option string :=
  match l with
  | [] => Some ""
  | d :: ds =>
    match digit_to_char d, digits_to_string ds with
    | Some c, Some s => Some (String c s)
    | _, _ => None
    end
  end.

Definition change_base_spec (x base : nat) (res : string) : Prop :=
  1 < base < 10 /\
  (x = 0 /\ res = "0"%string \/
  exists digits,
    change_base_digits x base = Some digits /\
    digits_to_string digits = Some res /\
    Forall (fun d => d < base) digits /\
    (* The digits represent x in base [base], most significant digit first *)
    x = fold_left (fun acc d => acc * base + d) digits 0).
