Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

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

Example test_case_0 : decimal_to_binary_spec 1000000005 "db111011100110101100101000000101db".
Proof.
  unfold decimal_to_binary_spec.
  exists (true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: true :: false :: true :: nil).
  split.
  - simpl.
    reflexivity.
  - split.
    + unfold bits_value.
      simpl.
      reflexivity.
    + right.
      split.
      * reflexivity.
      * eexists.
        reflexivity.
Qed.