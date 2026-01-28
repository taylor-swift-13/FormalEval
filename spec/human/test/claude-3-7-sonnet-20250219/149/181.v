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
  problem_149_spec ["stu"; "world"; "Programming"; "is"; "Programmaaaaing"; "Python"] ["is"; "Python"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* lengths:
     "stu" = 3 (odd) filtered out
     "world" = 5 (odd) filtered out
     "Programming" = 11 (odd) filtered out
     "is" = 2 (even) kept
     "Programmaaaaing" = 14 (even) kept
     "Python" = 6 (even) kept
  *)
  (* filter has_even_length = ["is"; "Programmaaaaing"; "Python"] *)

  (* Sort by string_le: compare lengths first:
     "is" (2), "Python" (6), "Programmaaaaing" (14)
     So sorted by length ascending: ["is"; "Python"; "Programmaaaaing"]
  *)

  (* Output is given as ["is"; "Python"], so explanation: output is ["is"; "Python"] but "Programmaaaaing" is missing? *)
  (* According to specification output = list_sort_impl input. The code as is does not remove "Programmaaaaing" because it has even length 14 *)
  (* But test case output omits it, so either test case is incorrect or there is an error. However, we must produce exactly the given output. *)

  (* To pass the equality, we must show output = list_sort_impl input. 
     But list_sort_impl input = ["is"; "Python"; "Programmaaaaing"] under current definitions.

     There might be a mistake in the test input or output.

     Since requested is exactly that test case, we will prove reflexivity after unfolding.
     Use cbn to reduce computations for the function.
     Actually simplify with simpl or cbn is the same.

     The filter step keeps "is", "Programmaaaaing", "Python".
     The sort step sorts ["is"; "Programmaaaaing"; "Python"] by length and lex order on ties.
     Lengths:
       is = 2 even
       Programmaaaaing = 14 even
       Python = 6 even
     Sorted lengths ascending: "is" (2), "Python" (6), "Programmaaaaing" (14)
     So sorted list is ["is"; "Python"; "Programmaaaaing"].

     So the output ["is"; "Python"] excludes "Programmaaaaing".
     This contradicts the definition.

     Possibly a misstatement in the user request, but the instructions say:

     > You are given the full content of an existing Coq output file for a HumanEval spec.
     > It already includes the specification definitions and the proof for the first test case.
     > Now, generate a Coq Example proof for the following new test case
     > `input = [["stu"; "world"; "Programming"; "is"; "Programmaaaaing"; "Python"]], output = ["is"; "Python"]`

    So we must trust these inputs and outputs.

    The only way to have output = ["is"; "Python"] given the current filter and sort functions
    is that the input has only "is" and "Python" as even length strings.
   
    But "Programmaaaaing" has length 14, which is even.

    Is the length correct?

    Count characters of "Programmaaaaing"

    "P", "r", "o", "g", "r", "a", "m", "m", "a", "a", "a", "a", "i", "n", "g"
    That's 15 chars, not 14.

    So length "Programmaaaaing" = 15 (odd), so filtered out.

    So initial count was wrong.

    Let's count "Programmaaaaing" again:

    P r o g r a m m a a a a i n g
    Count:
    P(1), r(2), o(3), g(4), r(5), a(6), m(7), m(8), a(9),
    a(10), a(11), a(12), i(13), n(14), g(15)
    Length is 15, which is odd => filtered out.

    That matches expected output.

  *)

  (* Hence filtered list is ["is"; "Python"] *)
  (* sort_by string_le ["is"; "Python"] *)
  (* Lengths of "is" = 2, "Python" = 6 *)
  (* sorted by length ascending: ["is"; "Python"] *)

  reflexivity.
Qed.