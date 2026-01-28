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

Example test_spec : problem_112_spec "dveeifieacced" "dveeified" ("acc"%string, false).
Proof.
  unfold problem_112_spec, reverse_delete, del_and_pal_impl, is_pal_impl, delete_chars_impl.
  cbn.

  (* list_ascii_of_string "dveeifieacced" = ["d"; "v"; "e"; "e"; "i"; "f"; "i"; "e"; "a"; "c"; "c"; "e"; "d"] *)
  (* list_ascii_of_string "dveeified" = ["d"; "v"; "e"; "e"; "i"; "f"; "i"; "e"; "d"] *)

  (* delete_chars_impl steps: *)
  (* 'd' in c, skip *)
  (* 'v' in c, skip *)
  (* 'e' in c, skip *)
  (* 'e' in c, skip *)
  (* 'i' in c, skip *)
  (* 'f' in c, skip *)
  (* 'i' in c, skip *)
  (* 'e' in c, skip *)
  (* 'a' not in c, keep *)
  (* 'c' not in c, keep *)
  (* 'c' not in c, keep *)
  (* 'e' in c, skip *)
  (* 'd' in c, skip *)
  (* Result list: ["a"; "c"; "c"] *)

  (* is_pal_impl ["a"; "c"; "c"] = false because "acc" ≠ "cca" *)

  (* string_of_list_ascii returns "acc" *)

  reflexivity.
Qed.