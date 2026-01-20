Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* Specification Definitions *)

Definition char_string (c : Ascii.ascii) : string := String c EmptyString.

Definition sep_char (c : Ascii.ascii) : Prop :=
  char_string c = " " \/ char_string c = ",".

Definition not_sep_char (c : Ascii.ascii) : Prop := ~ sep_char c.

Fixpoint all_chars (P : Ascii.ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => P c /\ all_chars P s'
  end.

Definition only_seps (s : string) : Prop := all_chars sep_char s.

Definition word (s : string) : Prop := s <> EmptyString /\ all_chars not_sep_char s.

Inductive components : list string -> list string -> Prop :=
| components_end : forall sep, only_seps sep -> components (sep :: nil) nil
| components_cons : forall sep w rest words,
    only_seps sep -> word w -> components rest words ->
    components (sep :: w :: rest) (w :: words).

Fixpoint concat (xs : list string) : string :=
  match xs with
  | nil => EmptyString
  | x :: xs' => x ++ concat xs'
  end.

Definition words_string_spec (s : string) (out : list string) : Prop :=
  exists comps words,
    components comps words /\ out = words /\ s = concat comps.

(* Helper Tactics *)

(* Tactic to prove a string contains only separators *)
Ltac solve_sep :=
  unfold only_seps, all_chars, sep_char, char_string;
  simpl;
  repeat match goal with
  | [ |- _ /\ _ ] => split
  | [ |- True ] => exact I
  | [ |- _ \/ _ ] => (left; reflexivity) || (right; reflexivity)
  end.

(* Tactic to prove a string is a valid word *)
Ltac solve_word :=
  unfold word, not_sep_char, sep_char, char_string;
  split; [ discriminate |
    unfold all_chars; simpl;
    repeat match goal with
    | [ |- _ /\ _ ] => split
    | [ |- True ] => exact I
    | [ |- ~ (_ \/ _) ] => intros [H | H]; discriminate H
    end
  ].

(* Example Proof *)

Example test_case_proof : 
  words_string_spec "Hi, my name is John" ["Hi"; "my"; "name"; "is"; "John"].
Proof.
  unfold words_string_spec.
  (* Existential witness for the raw components list *)
  exists [""; "Hi"; ", "; "my"; " "; "name"; " "; "is"; " "; "John"; ""].
  (* Existential witness for the extracted words list *)
  exists ["Hi"; "my"; "name"; "is"; "John"].
  
  split.
  
  - (* Subgoal 1: Prove components relation *)
    apply components_cons.
    { solve_sep. } (* sep: "" *)
    { solve_word. } (* word: "Hi" *)
    
    apply components_cons.
    { solve_sep. } (* sep: ", " *)
    { solve_word. } (* word: "my" *)
    
    apply components_cons.
    { solve_sep. } (* sep: " " *)
    { solve_word. } (* word: "name" *)
    
    apply components_cons.
    { solve_sep. } (* sep: " " *)
    { solve_word. } (* word: "is" *)
    
    apply components_cons.
    { solve_sep. } (* sep: " " *)
    { solve_word. } (* word: "John" *)
    
    apply components_end.
    { solve_sep. } (* sep: "" *)

  - (* Subgoal 2 & 3: Prove output list equality and string concatenation *)
    split.
    + reflexivity.
    + simpl. reflexivity.
Qed.