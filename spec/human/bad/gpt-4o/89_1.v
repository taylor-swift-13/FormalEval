Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope char_scope.

(* Helper function to compute the new character by shifting 4 positions *)
Definition shift_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let shifted := if (97 <=? n) && (n <=? 122) then (n - 97 + 4) mod 26 + 97 else n in
  ascii_of_nat shifted.

(* Encrypt function implementation *)
Fixpoint encrypt (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (shift_char c) (encrypt rest)
  end.

Example test_encrypt_hi : encrypt "hi" = "lm".
Proof.
  unfold encrypt.
  simpl.
  unfold shift_char.
  simpl.
  unfold nat_of_ascii, ascii_of_nat.
  simpl. reflexivity.
Qed.

Example test_encrypt_asdfghjkl : encrypt "asdfghjkl" = "ewhjklnop".
Proof.
  unfold encrypt.
  simpl.
  unfold shift_char.
  simpl.
  unfold nat_of_ascii, ascii_of_nat.
  simpl. reflexivity.
Qed.

Example test_encrypt_gf : encrypt "gf" = "kj".
Proof.
  unfold encrypt.
  simpl.
  unfold shift_char.
  simpl.
  unfold nat_of_ascii, ascii_of_nat.
  simpl. reflexivity.
Qed.

Example test_encrypt_et : encrypt "et" = "ix".
Proof.
  unfold encrypt.
  simpl.
  unfold shift_char.
  simpl.
  unfold nat_of_ascii, ascii_of_nat.
  simpl. reflexivity.
Qed.

(* Example proof for the specification *)
Example example_encrypt_spec : forall s output,
  encrypt s = output -> problem_89_spec s output.
Proof.
  intros s output H.
  unfold problem_89_spec.
  split.
  - rewrite <- H.
    induction s.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHs.
  - intros i Hi.
    rewrite <- H.
    induction s.
    + simpl in Hi. lia.
    + simpl in Hi.
      simpl.
      destruct (Nat.eq_dec i 0).
      * subst. simpl. unfold shift_char. unfold char_relation. simpl.
        destruct ((97 <=? nat_of_ascii a) && (nat_of_ascii a <=? 122)) eqn:Hrange.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
      * simpl. apply IHs. lia.
Qed.

Qed.