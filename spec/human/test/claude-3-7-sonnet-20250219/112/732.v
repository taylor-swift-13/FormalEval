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

Example test_spec : problem_112_spec "tricaasymmeticalacasymriicaleebl" "xyz" ("tricaasmmeticalacasmriicaleebl"%string, false).
Proof.
  unfold problem_112_spec, reverse_delete, del_and_pal_impl, is_pal_impl, delete_chars_impl.
  cbn.

  (* list_ascii_of_string "tricaasymmeticalacasymriicaleebl" *)
  (* characters 'x', 'y', 'z' are not present, so delete_chars_impl does not remove anything *)
  (* The resulting string will be identical except for filtering any 'x','y','z' if present - *)
  (* but since none are in the input, effectively none removed *)
  (* Wait - the original output has repeated 'm' and some removed 'y' letters which suggests that characters to delete are 'x','y','z' *)

  (* Let's examine the input and output more carefully: *)
  (* input: "tricaasymmeticalacasymriicaleebl" *)
  (* output: "tricaasmmeticalacasmriicaleebl" *)

  (* The output removes all 'y' characters *)
  (* input has 'y' at position 8 and 20 (approx), output removes them *)
  (* 'x' and 'z' not present *)
  (* So delete_chars_impl removes 'y' only *)

  (* After removing all 'y', string becomes "tricaasmmeticalacasmriicaleebl" *)

  (* Check palindrome: false *)

  reflexivity.
Qed.