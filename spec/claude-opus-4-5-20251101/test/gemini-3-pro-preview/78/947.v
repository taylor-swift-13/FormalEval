Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint count_prime_hex_digits (chars : list ascii) : nat :=
  match chars with
  | [] => 0
  | c :: rest => (if is_prime_hex_digit c then 1 else 0) + count_prime_hex_digits rest
  end.

Definition hex_key_spec (num : string) (result : nat) : Prop :=
  result = count_prime_hex_digits (string_to_list num).

Example test_hex_key : hex_key_spec "CEEEFAA12345CEA753BDD67891234567890ABCDEF12345BACDF11118872753BD159CEFF723BCBCD21234567890ABCDEFA12345BBAA20200DBBCC22EECEACACDF11118872159CEFFACDF11118872159CDEFF23BCCBB3137D1DDBB1CBB333A11DDB12345753BD6789123567890ABCDEF123B45BBAA22020A2202ECBBBD44BB333A191DDBFCBBBD4F212345BBAA220ED" 136.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.