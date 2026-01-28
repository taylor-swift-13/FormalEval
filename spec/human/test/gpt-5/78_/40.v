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

Example problem_78_test_44888989894 : problem_78_spec "44888989894" 0%nat.
Proof.
  unfold problem_78_spec.
  apply cphr_not_prime with (h:="4"%char) (t:="4888989894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="4"%char) (t:="888989894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="8"%char) (t:="88989894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="8"%char) (t:="8989894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="8"%char) (t:="989894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="9"%char) (t:="89894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="8"%char) (t:="9894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="9"%char) (t:="894") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="8"%char) (t:="94") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="9"%char) (t:="4") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="4"%char) (t:="") (n:=0).
  unfold not; intros H; inversion H.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_44888989894_Z_output : Z.of_nat 0 = 0%Z.
Proof.
  reflexivity.
Qed.