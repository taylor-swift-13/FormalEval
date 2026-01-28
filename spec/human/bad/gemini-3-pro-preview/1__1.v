Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* Definition of parenthesis characters *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(* Specification 1: IsBalanced *)
Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.

(* Specification 2: IsMinimalBalanced *)
Definition IsMinimalBalanced (s : string) : Prop :=
  IsBalanced s /\
  ~ (exists s1 s2,
       s1 <> "" /\
       s2 <> "" /\
       s = s1 ++ s2 /\
       IsBalanced s1 /\
       IsBalanced s2).

(* Helper: RemoveSpaces *)
Inductive RemoveSpaces : string -> string -> Prop :=
| RS_nil : RemoveSpaces "" ""
| RS_space : forall t t', RemoveSpaces t t' -> RemoveSpaces (String space t) t'
| RS_char : forall c t t', c <> space -> RemoveSpaces t t' -> RemoveSpaces (String c t) (String c t').

(* Helper: is_paren_or_space *)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(* Helper: ForallChars *)
Inductive ForallChars (P : ascii -> Prop) : string -> Prop :=
| Forall_nil : ForallChars P ""
| Forall_cons : forall c s, P c -> ForallChars P s -> ForallChars P (String c s).

(* Precondition *)
Definition problem_1_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (IsBalanced input).

(* Specification *)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  RemoveSpaces input (String.concat "" output) /\
  (Forall IsMinimalBalanced output).

(* Test Case *)
Definition test_input : string := "(()()) ((())) () ((())()())".
Definition test_output : list string := ["(()())"; "((()))"; "()"; "((())()())"].

(* Tactics for Proof *)

(* Tactic to solve IsBalanced for valid strings *)
Ltac solve_balanced :=
  unfold IsBalanced;
  repeat constructor.

(* Tactic to disprove IsBalanced for invalid strings *)
(* Inverts IsBalanced_ind until contradiction *)
Ltac disprove_balanced_hyp H :=
  let rec aux H :=
    inversion H; subst; clear H;
    try discriminate;
    match goal with
    | [ H' : IsBalanced_ind _ _ |- _ ] => aux H'
    | _ => idtac
    end
  in aux H.

(* Recursive tactic to explore all possible splits of the string s1 ++ s2 = S *)
Ltac peel_and_solve :=
  try discriminate; (* If s1 became longer than S, Heq is impossible *)
  destruct s1 as [|?c s1];
  [ (* Case: s1 ends here (split point) *)
    simpl in Heq; try subst s2;
    (* Either s1 is empty (contradiction Hne1) OR split is invalid (contradiction Hb1/Hb2) *)
    (try (apply Hne1; reflexivity)) || 
    (exfalso; 
     (apply Hb1; solve [disprove_balanced_hyp Hb1]) || 
     (apply Hb2; solve [disprove_balanced_hyp Hb2]))
  | (* Case: s1 continues *)
    simpl in Heq; injection Heq as Heq ?; subst;
    peel_and_solve
  ].

(* Tactic to solve ascii inequality *)
Ltac solve_char_neq :=
  let H := fresh in intro H; inversion H.

Example problem_1_test_proof : problem_1_spec test_input test_output.
Proof.
  unfold problem_1_spec.
  split.
  - (* Part 1: RemoveSpaces *)
    unfold test_input, test_output.
    simpl.
    repeat (apply RS_space || (apply RS_char; [ solve_char_neq | ]) || apply RS_nil).
  
  - (* Part 2: Forall IsMinimalBalanced *)
    unfold test_output.
    repeat constructor.
    + (* "(()())" *)
      split.
      * solve_balanced.
      * intros [s1 [s2 [Hne1 [Hne2 [Heq [Hb1 Hb2]]]]]].
        peel_and_solve.
    + (* "((()))" *)
      split.
      * solve_balanced.
      * intros [s1 [s2 [Hne1 [Hne2 [Heq [Hb1 Hb2]]]]]].
        peel_and_solve.
    + (* "()" *)
      split.
      * solve_balanced.
      * intros [s1 [s2 [Hne1 [Hne2 [Heq [Hb1 Hb2]]]]]].
        peel_and_solve.
    + (* "((())()())" *)
      split.
      * solve_balanced.
      * intros [s1 [s2 [Hne1 [Hne2 [Heq [Hb1 Hb2]]]]]].
        peel_and_solve.
Qed.