Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.

Fixpoint list_eqb {A} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [],[] => true
  | x1::t1, x2::t2 => andb (eq x1 x2) (list_eqb eq t1 t2)
  | _,_ => false
  end.

Fixpoint existsb {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | h::t => orb (f h) (existsb f t) end.

Fixpoint delete_chars_impl (s c : list ascii) : list ascii :=
  match s with
  | [] => []
  | h::t => if existsb (fun x => Ascii.eqb x h) c then delete_chars_impl t c else h :: delete_chars_impl t c
  end.

Definition is_pal_impl (s : list ascii) : bool := list_eqb Ascii.eqb s (rev s).

Definition del_and_pal_impl (s c : list ascii) : list ascii * bool :=
  let r := delete_chars_impl s c in (r, is_pal_impl r).

Definition reverse_delete (s c : string) : string * bool :=
  let (r, b) := del_and_pal_impl (list_ascii_of_string s) (list_ascii_of_string c) in
  (string_of_list_ascii r, b).

Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  output = reverse_delete s c.

Open Scope char_scope.
Open Scope string_scope.

Example test_spec : problem_112_spec "ammadalmxxyz" "abcedceba" ("mmlmxxyz"%string, false).
Proof.
  unfold problem_112_spec, reverse_delete, del_and_pal_impl, is_pal_impl, delete_chars_impl.
  cbn.

  (* list_ascii_of_string "ammadalmxxyz" =
     ["a"; "m"; "m"; "a"; "d"; "a"; "l"; "m"; "x"; "x"; "y"; "z"] *)
  (* list_ascii_of_string "abcedceba" =
     ["a"; "b"; "c"; "e"; "d"; "c"; "e"; "b"; "a"] *)

  (* delete_chars_impl removes all chars in c from s:
     Remove 'a': positions 1,4,6
     Remove 'b': none in s
     Remove 'c': none in s
     Remove 'e': none in s
     Remove 'd': position 5
     So remaining chars are:

     "m" (pos 2), "m" (pos 3), "l" (pos 7), "m" (pos 8), "x" (pos 9), "x" (pos 10), "y" (pos 11), "z" (pos 12)

     Wait, "d" is in c so remove it => pos 5 removed

     Also 'b' and 'c' and 'e' are in c but do not appear in s except a, d

     After full deletion, list is
     ["m"; "m"; "l"; "m"; "x"; "x"; "y"; "z"]

     Check palindrome: is ["m"; "m"; "l"; "m"; "x"; "x"; "y"; "z"] = rev ["m"; "m"; "l"; "m"; "x"; "x"; "y"; "z"]?

     The reverse is ["z"; "y"; "x"; "x"; "m"; "l"; "m"; "m"]

     So no, is_pal_impl = false

     string_of_list_ascii converts back to "mmlmxxyz"
  *)

  reflexivity.
Qed.