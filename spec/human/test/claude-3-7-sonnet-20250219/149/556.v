Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.

Fixpoint lex_le (s1 s2 : string) : bool :=
  match s1,s2 with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String c1 t1, String c2 t2 =>
    match Ascii.compare c1 c2 with
    | Lt => true | Gt => false | Eq => lex_le t1 t2
    end
  end.

Definition string_le (s1 s2 : string) : bool :=
  match Nat.compare (length s1) (length s2) with
  | Lt => true | Gt => false | Eq => lex_le s1 s2
  end.

Definition has_even_length (s : string) : bool := Nat.even (length s).

Fixpoint insert_by (le : string -> string -> bool) (x : string) (l:list string) : list string :=
  match l with []=>[x] | h::t => if le x h then x::l else h::insert_by le x t end.

Fixpoint sort_by (le : string -> string -> bool) (l:list string) : list string :=
  match l with []=>[] | h::t => insert_by le h (sort_by le t) end.

Definition list_sort_impl (lst_in : list string) : list string :=
  sort_by string_le (filter has_even_length lst_in).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  output = list_sort_impl input.

Example test_case_149 :
  problem_149_spec ["Hello"; "Porogramming"; "is"] ["is"; "Porogramming"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* length "Hello" = 5 (odd) -> filtered out *)
  (* length "Porogramming" = 11 (odd) -> filtered out *)
  (* length "is" = 2 (even) -> kept *)

  (* Wait, "Porogramming" length is 11 (odd), so it should be filtered out.
     The problem expects output = ["is"; "Porogramming"], but "Porogramming" length = 11 (odd).
     Let's verify the length of "Porogramming":
     Characters: P o r o g r a m m i n g
     Count: 11 characters -> odd.

     According to has_even_length, it would be filtered out.
     But the expected output includes "Porogramming".

     This would conflict with the spec, unless there is a mistake in the input or the filtering condition.

     Check input and expected output again:
     Input: ["Hello"; "Porogramming"; "is"]
     Output: ["is"; "Porogramming"]

     "Porogramming" length odd but included.

     Could it be a typo in the test case? Or are we to consider that filter is on even length, but "Porogramming" has odd length?

     Let's check the length of "Porogramming" carefully using Coq:

     # Calculate length "Porogramming":
     Let's count:
     P(1) o(2) r(3) o(4) g(5) r(6) a(7) m(8) m(9) i(10) n(11) g(12)

     Actually, "Porogramming" has 12 characters, not 11.

     Recount:
     P o r o g r a m m i n g
     1 2 3 4 5 6 7 8 9 10 11 12

     So length = 12, which is even.

     So it is kept.

  *)

  reflexivity.
Qed.