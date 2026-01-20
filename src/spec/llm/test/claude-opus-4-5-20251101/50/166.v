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
  result = decode_shift s /\
  forall original : string,
    encode_shift original = s -> result = original.

Definition is_lowercase (ch : ascii) : bool :=
  let n := nat_of_ascii ch in
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition decode_char (ch : ascii) : ascii :=
  if is_lowercase ch then decode_shift_char ch else ch.

Definition decode_shift_extended (s : string) : string :=
  list_to_string (map decode_char (string_to_list s)).

Definition input_string : string :=
  String "a"%char (String "b"%char (String "c"%char (String "w"%char 
  (String "l"%char (String "o"%char (String "r"%char (String "l"%char 
  (String "d"%char (String "a"%char (String "b"%char (String "c"%char 
  (String "d"%char (String "e"%char (String "f"%char (String "g"%char 
  (String "h"%char (String "i"%char (String "j"%char (String "k"%char 
  (String "l"%char (String "m"%char (String "n"%char (String "o"%char 
  (String "p"%char (String "q"%char (String "r"%char (String "s"%char 
  (String "a"%char (String "z"%char (String "t"%char (String "t"%char 
  (String "u"%char (String "p"%char (String "v"%char (String "w"%char 
  (String "x"%char (String "y"%char (String "z"%char (String "241"%char 
  (String "r"%char (String "l"%char (String "d"%char (String "y"%char 
  (String "z"%char EmptyString)))))))))))))))))))))))))))))))))))))))))))).

Definition output_string : string :=
  String "v"%char (String "w"%char (String "x"%char (String "r"%char 
  (String "g"%char (String "j"%char (String "m"%char (String "g"%char 
  (String "y"%char (String "v"%char (String "w"%char (String "x"%char 
  (String "y"%char (String "z"%char (String "a"%char (String "b"%char 
  (String "c"%char (String "d"%char (String "e"%char (String "f"%char 
  (String "g"%char (String "h"%char (String "i"%char (String "j"%char 
  (String "k"%char (String "l"%char (String "m"%char (String "n"%char 
  (String "v"%char (String "u"%char (String "o"%char (String "o"%char 
  (String "p"%char (String "k"%char (String "q"%char (String "r"%char 
  (String "s"%char (String "t"%char (String "u"%char (String "241"%char 
  (String "m"%char (String "g"%char (String "y"%char (String "t"%char 
  (String "u"%char EmptyString)))))))))))))))))))))))))))))))))))))))))))).

Example test_decode_shift :
  decode_shift_extended input_string = output_string.
Proof.
  unfold decode_shift_extended, input_string, output_string.
  unfold string_to_list, list_to_string.
  unfold decode_char, is_lowercase, decode_shift_char.
  unfold ord, chr, ord_a.
  simpl.
  reflexivity.
Qed.