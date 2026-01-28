Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* --- Specification Definitions --- *)

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

(* --- Tactics --- *)

(* Solves goals of type `only_seps s` for concrete strings *)
Ltac solve_seps :=
  unfold only_seps; simpl;
  repeat split;
  try exact I; (* Handle the base case True *)
  unfold sep_char, char_string;
  try (left; reflexivity);
  try (right; reflexivity).

(* Solves goals of type `word s` for concrete strings *)
Ltac solve_word :=
  unfold word; split;
  [ intro H; discriminate (* Prove s <> EmptyString *)
  | simpl;
    repeat split;
    try exact I; (* Handle the base case True *)
    unfold not_sep_char, sep_char, char_string;
    intros [H | H]; inversion H (* Prove negation of sep_char *)
  ].

(* --- Test Case Proof --- *)

Example test_words_string :
  words_string_spec "words," ["words"].
Proof.
  (* Instantiate the existential variables with the concrete decomposition *)
  exists ["" ; "words" ; ","].
  exists ["words"].
  
  (* Split the conjunctions explicitly to manage goals *)
  split.
  
  - (* Prove components relation *)
    apply components_cons. { solve_seps. } { solve_word. }
    apply components_end.  { solve_seps. }
    
  - (* Prove remaining equalities *)
    split.
    + (* Prove output list equality *)
      reflexivity.
    + (* Prove string concatenation equality *)
      simpl. reflexivity.
Qed.