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

Ltac solve_step :=
  match goal with
  | [ |- count_prime_hex_rel "" 0 ] => apply cphr_nil
  | [ |- count_prime_hex_rel (String ?h ?t) ?n ] =>
      first [
        let Hp := fresh "Hp" in
        assert (is_prime_hex_digit h) as Hp by constructor;
        apply cphr_prime; [ exact Hp | clear Hp ]
      |
        apply cphr_not_prime; [ let Hn := fresh "Hn" in intro Hn; inversion Hn | ]
      ]
  end.

Example test_case_1 : problem_78_spec "1ACDF11118872159CEFF23BCCBBDDDBBCFFEEDDCCBBBAA20200DDBBBCCACEADEA12345CEA753BDD67891234567890ABCDEF121234567890ABCDEF12345BBAA2202E345BBAA2202E0ABCDEF12345BBAA2202EFFEEDDCCBBAA890ABCEAD0CDEFA12345BBAA20200CEEF" 89.
Proof.
  unfold problem_78_spec.
  repeat solve_step.
Qed.