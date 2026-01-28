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

Example problem_78_test_77C67ABCD2C37777 : problem_78_spec "77C67ABCD2C37777" 11%nat.
Proof.
  unfold problem_78_spec.
  apply cphr_prime with (h:="7"%char) (t:="7C67ABCD2C37777") (n:=10).
  exact iphd_7.
  apply cphr_prime with (h:="7"%char) (t:="C67ABCD2C37777") (n:=9).
  exact iphd_7.
  apply cphr_not_prime with (h:="C"%char) (t:="67ABCD2C37777") (n:=9).
  unfold not; intros H; inversion H.
  apply cphr_not_prime with (h:="6"%char) (t:="7ABCD2C37777") (n:=9).
  unfold not; intros H; inversion H.
  apply cphr_prime with (h:="7"%char) (t:="ABCD2C37777") (n:=8).
  exact iphd_7.
  apply cphr_not_prime with (h:="A"%char) (t:="BCD2C37777") (n:=8).
  unfold not; intros H; inversion H.
  apply cphr_prime with (h:="B"%char) (t:="CD2C37777") (n:=7).
  exact iphd_B.
  apply cphr_not_prime with (h:="C"%char) (t:="D2C37777") (n:=7).
  unfold not; intros H; inversion H.
  apply cphr_prime with (h:="D"%char) (t:="2C37777") (n:=6).
  exact iphd_D.
  apply cphr_prime with (h:="2"%char) (t:="C37777") (n:=5).
  exact iphd_2.
  apply cphr_not_prime with (h:="C"%char) (t:="37777") (n:=5).
  unfold not; intros H; inversion H.
  apply cphr_prime with (h:="3"%char) (t:="7777") (n:=4).
  exact iphd_3.
  apply cphr_prime with (h:="7"%char) (t:="777") (n:=3).
  exact iphd_7.
  apply cphr_prime with (h:="7"%char) (t:="77") (n:=2).
  exact iphd_7.
  apply cphr_prime with (h:="7"%char) (t:="7") (n:=1).
  exact iphd_7.
  apply cphr_prime with (h:="7"%char) (t:="") (n:=0).
  exact iphd_7.
  apply cphr_nil.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Example problem_78_test_77C67ABCD2C37777_Z_output : Z.of_nat 11 = 11%Z.
Proof.
  reflexivity.
Qed.