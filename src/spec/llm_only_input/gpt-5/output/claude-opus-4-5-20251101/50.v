Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

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

Example test_decode_shift_value :
  decode_shift "tantywccpjkimslotpzs" = "oviotrxxkefdhngjokun".
Proof.
  vm_compute. reflexivity.
Qed.

Example test_encode_shift_value :
  encode_shift "oviotrxxkefdhngjokun" = "tantywccpjkimslotpzs".
Proof.
  vm_compute. reflexivity.
Qed.

Axiom encode_shift_injective : forall s1 s2, encode_shift s1 = encode_shift s2 -> s1 = s2.

Example test_decode_shift_spec :
  decode_shift_spec "tantywccpjkimslotpzs" "oviotrxxkefdhngjokun".
Proof.
  unfold decode_shift_spec.
  split.
  - vm_compute. reflexivity.
  - intros original H.
    assert (Hinverse : encode_shift (decode_shift "tantywccpjkimslotpzs") = "tantywccpjkimslotpzs") by (vm_compute; reflexivity).
    rewrite <- Hinverse in H.
    apply encode_shift_injective in H.
    vm_compute in H.
    rewrite <- H.
    reflexivity.
Qed.