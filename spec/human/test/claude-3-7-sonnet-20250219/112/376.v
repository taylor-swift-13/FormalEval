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

Example test_spec : problem_112_spec "ammadalmxxyz" "abcedcracmadameceaeabtattarrattaasymmetricaltcedebaira" ("xxz"%string, false).
Proof.
  unfold problem_112_spec, reverse_delete, del_and_pal_impl, is_pal_impl, delete_chars_impl.
  cbn.

  (* list_ascii_of_string "ammadalmxxyz" = ["a";"m";"m";"a";"d";"a";"l";"m";"x";"x";"y";"z"] *)
  (* list_ascii_of_string "abcedcracmadameceaeabtattarrattaasymmetricaltcedebaira" is a long list of chars *)

  (* Characters from s that appear in c: *)
  (* 'a' in c -> skip *)
  (* 'm' in c -> skip *)
  (* 'm' in c -> skip *)
  (* 'a' in c -> skip *)
  (* 'd' in c -> skip *)
  (* 'a' in c -> skip *)
  (* 'l' in c -> skip *)
  (* 'm' in c -> skip *)
  (* 'x' not in c -> keep *)
  (* 'x' not in c -> keep *)
  (* 'y' in c -> skip *)
  (* 'z' not in c -> keep *)
  (* Thus result list: ["x";"x";"z"] *)

  (* is_pal_impl compares ["x"; "x"; "z"] with ["z"; "x"; "x"], which is false *)

  (* string_of_list_ascii converts back to "xxz" *)

  reflexivity.
Qed.