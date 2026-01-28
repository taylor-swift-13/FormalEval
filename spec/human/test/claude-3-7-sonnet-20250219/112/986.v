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

Example test_spec : problem_112_spec "abcedeba" "xabracecartatatarrattatyz" ("d"%string, true).
Proof.
  unfold problem_112_spec, reverse_delete, del_and_pal_impl, is_pal_impl, delete_chars_impl.
  cbn.

  (* list_ascii_of_string "abcedeba" = [ "a"; "b"; "c"; "e"; "d"; "e"; "b"; "a" ] *)
  (* list_ascii_of_string "xabracecartatatarrattatyz" = 
     [ "x"; "a"; "b"; "r"; "a"; "c"; "e"; "c"; "a"; "r"; "t"; "a"; "t"; "a"; "t"; "a"; "r"; 
       "r"; "a"; "t"; "t"; "a"; "t"; "y"; "z" ] *)

  (* delete_chars_impl steps: *)
  (* "a" ∈ c, skip *)
  (* "b" ∈ c, skip *)
  (* "c" ∈ c, skip *)
  (* "e" ∉ c, keep *)
  (* "d" ∉ c, keep *)
  (* "e" ∉ c, keep *)
  (* "b" ∈ c, skip *)
  (* "a" ∈ c, skip *)
  (* Result list: ["e"; "d"; "e"] *)

  (* is_pal_impl compares ["e"; "d"; "e"] with ["e"; "d"; "e"], true *)

  (* string_of_list_ascii converts to "ede" *)
  (* but the output given is ("d", true). So we must look carefully: *)

  (* On careful checking, "e" is in c? "e" is 'e', is it in c? "xabracecartatatarrattatyz" includes 'a', 'b', 'c', 'r', 't', 'y', 'z', 'x' but no 'e'? *)

  (* Checking characters of c: "x a b r a c e c a r t a t a t a r r a t t a t y z" *)
  (* 'e' is indeed in c at position 6 and 8 *)

  (* So 'e' is in c, so e should be deleted *)

  (* Re-evaluate: *)
  (* s = [a; b; c; e; d; e; b; a] *)
  (* c = [x; a; b; r; a; c; e; c; a; r; t; a; t; a; t; a; r; r; a; t; t; a; t; y; z] *)

  (* Check each s char for membership in c: *)
  (* a in c? yes *)
  (* b in c? yes *)
  (* c in c? yes *)
  (* e in c? yes *)
  (* d in c? no *)
  (* e in c? yes *)
  (* b in c? yes *)
  (* a in c? yes *)

  (* So only 'd' remains *)

  (* Result list: ["d"] *)

  (* is_pal_impl compares ["d"] with ["d"], true *)

  (* string_of_list_ascii converts to "d" *)

  reflexivity.
Qed.