Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Inductive is_prime_hex_digit : ascii -> Prop :=
| iphd_2 : is_prime_hex_digit "2"%char
| iphd_3 : is_prime_hex_digit "3"%char
| iphd_5 : is_prime_hex_digit "5"%char
| iphd_7 : is_prime_hex_digit "7"%char
| iphd_B : is_prime_hex_digit "B"%char
| iphd_D : is_prime_hex_digit "D"%char.

Inductive count_prime_hex_rel : string -> nat -> Prop :=
| cphr_nil : count_prime_hex_rel "" 0%nat
| cphr_prime : forall h t n, is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) (S n)
| cphr_not_prime : forall h t n, ~ is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) n.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  count_prime_hex_rel s output.

Example test_case_1 : problem_78_spec "ACDF1111887215CACEADEA9CEFFACDF11118872159CDEFF23BCCBB333A11DDBCBBBD44" 25.
Proof.
  unfold problem_78_spec.
  Ltac np := apply cphr_not_prime; [intro H; inversion H | ].
  Ltac p c := apply cphr_prime; [apply c | ].
  np. np. p iphd_D. np. np. np. np. np. np. np.
  p iphd_7. p iphd_2. np. p iphd_5. np. np. np. np. np. p iphd_D.
  np. np. np. np. np. np. np. np. np. p iphd_D.
  np. np. np. np. np. np. np. p iphd_7. p iphd_2. np.
  p iphd_5. np. np. p iphd_D. np. np. np. p iphd_2. p iphd_3. p iphd_B.
  np. np. p iphd_B. p iphd_B. p iphd_3. p iphd_3. p iphd_3. np. np. np.
  p iphd_D. p iphd_D. p iphd_B. np. p iphd_B. p iphd_B. p iphd_B. p iphd_D. np. np.
  apply cphr_nil.
Qed.