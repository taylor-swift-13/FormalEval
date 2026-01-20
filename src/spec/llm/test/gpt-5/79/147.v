Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.

Open Scope string_scope.
Open Scope Z_scope.

Definition char_of_bit (b : bool) : ascii :=
  if b then "1"%char else "0"%char.

Fixpoint string_of_bits (bits : list bool) : string :=
  match bits with
  | nil => EmptyString
  | b :: bs => String (char_of_bit b) (string_of_bits bs)
  end.

Fixpoint bits_value_fold (bits : list bool) (acc : Z) : Z :=
  match bits with
  | nil => acc
  | b :: bs => bits_value_fold bs (2 * acc + (if b then 1 else 0))
  end.

Definition bits_value (bits : list bool) : Z :=
  bits_value_fold bits 0.

Definition decimal_to_binary_spec (decimal : Z) (res : string) : Prop :=
  exists bits : list bool,
    res = ("db" ++ string_of_bits bits ++ "db")%string /\
    bits_value bits = decimal /\
    ((decimal = 0 /\ bits = false :: nil) \/
     (decimal > 0 /\ exists bs : list bool, bits = true :: bs)).

Fixpoint bits_of_string (s : string) : list bool :=
  match s with
  | EmptyString => nil
  | String c s' => (if Ascii.eqb c "1"%char then true else false) :: bits_of_string s'
  end.

Example decimal_to_binary_test_0 :
  decimal_to_binary_spec 10000000000000000000000000000005%Z "db1111110001101111011111000100000001000101100000010010001010010110010011010000000000000000000000000000101db".
Proof.
  unfold decimal_to_binary_spec.
  exists (bits_of_string "1111110001101111011111000100000001000101100000010010001010010110010011010000000000000000000000000000101").
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + right. split.
      * lia.
      * exists (tl (bits_of_string "1111110001101111011111000100000001000101100000010010001010010110010011010000000000000000000000000000101")). reflexivity.
Qed.