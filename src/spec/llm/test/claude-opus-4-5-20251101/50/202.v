Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition ord (ch : ascii) : Z := Z.of_nat (nat_of_ascii ch).

Definition chr (n : Z) : ascii := ascii_of_nat (Z.to_nat n).

Definition ord_a : Z := ord "a"%char.

Definition encode_shift_char (ch : ascii) : ascii :=
  chr (((ord ch + 5 - ord_a) mod 26) + ord_a).

Definition decode_shift_char (ch : ascii) : ascii :=
  chr (((ord ch - ord_a - 5 + 26) mod 26) + ord_a).

Definition is_lower (ch : ascii) : bool :=
  let n := nat_of_ascii ch in
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition decode_char (ch : ascii) : ascii :=
  if is_lower ch then decode_shift_char ch else ch.

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
  list_to_string (map decode_char (string_to_list s)).

Definition decode_shift_spec (s : string) (result : string) : Prop :=
  result = decode_shift s /\
  forall original : string,
    encode_shift original = s -> result = original.

Definition input_string : string :=
  String "1"%char (String "a"%char (String "2"%char (String "d"%char 
  (String "3"%char (String "g"%char (String "4"%char (String "j"%char 
  (String "5"%char (String "m"%char (String "6"%char (String "p"%char 
  (String "9"%char (String "s"%char (String "8"%char (String "v"%char 
  (String "7"%char (String "y"%char (String "0"%char (String "z"%char 
  EmptyString))))))))))))))))))).

Definition output_string : string :=
  String "1"%char (String "v"%char (String "2"%char (String "y"%char 
  (String "3"%char (String "b"%char (String "4"%char (String "e"%char 
  (String "5"%char (String "h"%char (String "6"%char (String "k"%char 
  (String "9"%char (String "n"%char (String "8"%char (String "q"%char 
  (String "7"%char (String "t"%char (String "0"%char (String "u"%char 
  EmptyString))))))))))))))))))).

Example test_decode_shift :
  decode_shift input_string = output_string.
Proof.
  unfold decode_shift, input_string, output_string.
  unfold string_to_list, list_to_string.
  unfold decode_char, is_lower, decode_shift_char.
  unfold ord, chr, ord_a.
  simpl.
  reflexivity.
Qed.