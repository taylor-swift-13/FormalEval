Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope char_scope.

Definition ord (ch : ascii) : Z := Z.of_nat (nat_of_ascii ch).

Definition chr (n : Z) : ascii := ascii_of_nat (Z.to_nat n).

Definition ord_a : Z := ord "a"%char.

Definition encode_shift_char (ch : ascii) : ascii :=
  chr (((ord ch + 5 - ord_a) mod 26) + ord_a).

Definition decode_shift_char (ch : ascii) : ascii :=
  chr (((ord ch - ord_a - 5 + 26) mod 26) + ord_a).

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String c (list_to_string rest)
  end.

Definition encode_shift (s : string) : string :=
  list_to_string (map encode_shift_char (string_to_list s)).

Definition decode_shift (s : string) : string :=
  list_to_string (map decode_shift_char (string_to_list s)).

Definition decode_shift_spec (s : string) (result : string) : Prop :=
  result = decode_shift s.

Definition bytes_to_string (l : list nat) : string :=
  list_to_string (map ascii_of_nat l).

Definition input_bytes : list nat := 
  [233; 238; 248; 252; 104; 101; 108; 108; 111; 32; 119; 111; 114; 108; 100; 241].

Definition input_str : string := bytes_to_string input_bytes.

Example test_case : decode_shift_spec input_str "bgquczggjirjmgyj".
Proof.
  unfold decode_shift_spec.
  unfold input_str, bytes_to_string, input_bytes.
  vm_compute.
  reflexivity.
Qed.