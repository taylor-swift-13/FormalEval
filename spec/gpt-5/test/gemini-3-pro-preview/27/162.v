Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  orb (andb (Nat.leb 97 n) (Nat.leb n 122))
      (andb (Nat.leb 224 n) (Nat.leb n 254)).

Definition is_upper_nat (n : nat) : bool :=
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))
      (andb (Nat.leb 192 n) (Nat.leb n 222)).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

(* Input: "ïîÏÎñÑàÀáÁéÉèÈìÌÜíÍòÒúÙüÜ" *)
Definition input_str : string :=
  String (ascii_of_nat 239) (String (ascii_of_nat 238) (String (ascii_of_nat 207) (String (ascii_of_nat 206) 
  (String (ascii_of_nat 241) (String (ascii_of_nat 209) (String (ascii_of_nat 224) (String (ascii_of_nat 192) 
  (String (ascii_of_nat 225) (String (ascii_of_nat 193) (String (ascii_of_nat 233) (String (ascii_of_nat 201) 
  (String (ascii_of_nat 232) (String (ascii_of_nat 200) (String (ascii_of_nat 236) (String (ascii_of_nat 204) 
  (String (ascii_of_nat 220) (String (ascii_of_nat 237) (String (ascii_of_nat 205) (String (ascii_of_nat 242) 
  (String (ascii_of_nat 210) (String (ascii_of_nat 250) (String (ascii_of_nat 218) (String (ascii_of_nat 252) 
  (String (ascii_of_nat 220) EmptyString)))))))))))))))))))))))).

(* Output: "ÏÎïîÑñÀàÁáÉéÈèÌìüÍíÒòÚùÜü" *)
Definition output_str : string :=
  String (ascii_of_nat 207) (String (ascii_of_nat 206) (String (ascii_of_nat 239) (String (ascii_of_nat 238) 
  (String (ascii_of_nat 209) (String (ascii_of_nat 241) (String (ascii_of_nat 192) (String (ascii_of_nat 224) 
  (String (ascii_of_nat 193) (String (ascii_of_nat 225) (String (ascii_of_nat 201) (String (ascii_of_nat 233) 
  (String (ascii_of_nat 200) (String (ascii_of_nat 232) (String (ascii_of_nat 204) (String (ascii_of_nat 236) 
  (String (ascii_of_nat 252) (String (ascii_of_nat 205) (String (ascii_of_nat 237) (String (ascii_of_nat 210) 
  (String (ascii_of_nat 242) (String (ascii_of_nat 218) (String (ascii_of_nat 250) (String (ascii_of_nat 220) 
  (String (ascii_of_nat 252) EmptyString)))))))))))))))))))))))).

Example test_flip_case_extended : flip_case_spec input_str output_str.
Proof.
  unfold flip_case_spec.
  unfold input_str, output_str.
  vm_compute.
  reflexivity.
Qed.