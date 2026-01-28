Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* --- Helper Definitions --- *)

(* Converts a list of ascii characters to a string *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* Converts a string to a list of ascii characters *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: (list_ascii_of_string s')
  end.

(* --- Specification Definitions --- *)

Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.
Definition space : ascii := " "%char.

Inductive max_depth_aux_rel : string -> nat -> nat -> nat -> Prop :=
  | mdar_nil : forall current_depth max_seen, max_depth_aux_rel "" current_depth max_seen max_seen
  | mdar_lparen : forall h t current_depth max_seen new_depth new_max result,
      h = lparen ->
      new_depth = S current_depth ->
      new_max = Nat.max max_seen new_depth ->
      max_depth_aux_rel t new_depth new_max result ->
      max_depth_aux_rel (String h t) current_depth max_seen result
  | mdar_rparen : forall h t current_depth max_seen result,
      h = rparen ->
      max_depth_aux_rel t (Nat.pred current_depth) max_seen result ->
      max_depth_aux_rel (String h t) current_depth max_seen result
  | mdar_other : forall h t current_depth max_seen result,
      h <> lparen ->
      h <> rparen ->
      max_depth_aux_rel t current_depth max_seen result ->
      max_depth_aux_rel (String h t) current_depth max_seen result.

Inductive MaxDepth_rel : string -> nat -> Prop :=
  | md_base : forall g result, max_depth_aux_rel g 0 0 result -> MaxDepth_rel g result.

Inductive SplitOnSpaces_aux_rel : list ascii -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group "" [string_of_list_ascii (List.rev current_group)]
  | sosar_space_empty : forall current_group h t result,
      h = space ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = space ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) ((string_of_list_ascii (List.rev current_group)) :: result)
  | sosar_char : forall current_group h t result,
      h <> space ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.

Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Inductive IsBalanced_ind : string -> nat -> Prop :=
| IB_nil : IsBalanced_ind "" 0
| IB_lparen : forall t n, IsBalanced_ind t (S n) -> IsBalanced_ind (String lparen t) n
| IB_rparen : forall t n, IsBalanced_ind t n -> IsBalanced_ind (String rparen t) (S n)
| IB_other : forall c t n, c <> lparen -> c <> rparen -> IsBalanced_ind t n -> IsBalanced_ind (String c t) n.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_ind s 0.

Definition problem_6_pre (input : string) : Prop :=
  (Forall  is_paren_or_space (list_ascii_of_string input)) /\
  (IsBalanced input).

Definition problem_6_spec (input : string) (output : list nat) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    length output = length groups /\
    (forall i, i < length groups -> MaxDepth_rel (nth i groups "") (nth i output 0)).

(* --- Test Case Proof --- *)

Definition test_input : string := "(()()) ((())) () ((())()())".
Definition test_output : list nat := [2; 3; 1; 3].

(* Tactics for automation *)

(* Tactic to step through the SplitOnSpaces_aux_rel derivation *)
Ltac step_split :=
  match goal with
  | [ |- SplitOnSpaces_aux_rel (_::_) "" _ ] => 
      apply sosar_nil_nonempty; discriminate
  | [ |- SplitOnSpaces_aux_rel [] "" _ ] => 
      apply sosar_nil_empty; reflexivity
  | [ |- SplitOnSpaces_aux_rel [] (String ?c ?s) _ ] =>
      match c with
      | " "%char => apply sosar_space_empty; [reflexivity | reflexivity | ] 
      | _ => apply sosar_char; [ discriminate | ] 
      end
  | [ |- SplitOnSpaces_aux_rel (_::_) (String ?c ?s) _ ] =>
      match c with
      | " "%char => apply sosar_space_nonempty; [reflexivity | discriminate | ]
      | _ => apply sosar_char; [ discriminate | ]
      end
  end.

(* Tactic to solve the splitting relation completely *)
Ltac solve_split :=
  apply sos_base;
  repeat step_split;
  simpl; reflexivity.

(* Tactic to solve the max depth relation *)
Ltac solve_depth :=
  apply md_base;
  repeat match goal with
  | [ |- max_depth_aux_rel "" _ _ _ ] => apply mdar_nil
  | [ |- max_depth_aux_rel (String ?c ?s) _ _ _ ] =>
      match c with
      | "("%char => eapply mdar_lparen; [ reflexivity | reflexivity | reflexivity | ]
      | ")"%char => eapply mdar_rparen; [ reflexivity | ]
      | _ => eapply mdar_other; [ discriminate | discriminate | ]
      end
  end.

Example problem_6_test_case : problem_6_spec test_input test_output.
Proof.
  unfold problem_6_spec, test_input, test_output.
  
  (* Explicitly provide the split groups *)
  exists ["(()())"; "((()))"; "()"; "((())()())"].
  
  split.
  - (* Prove SplitOnSpaces_rel *)
    solve_split.
    
  - split.
    + (* Prove length equality *)
      reflexivity.
      
    + (* Prove MaxDepth_rel for each element *)
      intros i H.
      (* Unroll the loop for the 4 elements to avoid variable scoping issues *)
      destruct i. { solve_depth. }
      destruct i. { solve_depth. }
      destruct i. { solve_depth. }
      destruct i. { solve_depth. }
      (* Handle out of bounds *)
      simpl in H. lia.
Qed.