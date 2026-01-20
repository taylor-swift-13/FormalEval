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

Definition input_string : string :=
  String "t"%char (String "e"%char (String "s"%char (String "t"%char 
  (String " "%char (String "i"%char (String "n"%char (String "p"%char 
  (String "u"%char (String "t"%char (String " "%char (String "w"%char 
  (String "i"%char (String "t"%char (String "h"%char (String " "%char 
  (String "s"%char (String "p"%char (String "a"%char (String "c"%char 
  (String "e"%char (String "s"%char 
  EmptyString))))))))))))))))))))).

Definition output_string : string :=
  String "o"%char (String "z"%char (String "n"%char (String "o"%char 
  (String "i"%char (String "d"%char (String "i"%char (String "k"%char 
  (String "p"%char (String "o"%char (String "i"%char (String "r"%char 
  (String "d"%char (String "o"%char (String "c"%char (String "i"%char 
  (String "n"%char (String "k"%char (String "v"%char (String "x"%char 
  (String "z"%char (String "n"%char 
  EmptyString))))))))))))))))))))).

Example test_decode_shift :
  decode_shift input_string = output_string.
Proof.
  unfold decode_shift, input_string, output_string.
  unfold string_to_list, list_to_string.
  unfold decode_shift_char.
  unfold ord, chr, ord_a.
  simpl.
  reflexivity.
Qed.