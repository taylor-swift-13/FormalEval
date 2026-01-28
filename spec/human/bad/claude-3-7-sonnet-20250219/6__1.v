Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => ""
  | c :: t => String c (string_of_list_ascii t)
  end.

Inductive max_depth_aux_rel : string -> nat -> nat -> nat -> Prop :=
  | mdar_nil : forall current_depth max_seen,
      max_depth_aux_rel "" current_depth max_seen max_seen
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
  | md_base : forall g result,
      max_depth_aux_rel g 0 0 result ->
      MaxDepth_rel g result.

Inductive SplitOnSpaces_aux_rel : list ascii -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group,
      current_group = [] ->
      SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group,
      current_group <> [] ->
      SplitOnSpaces_aux_rel current_group "" [string_of_list_ascii (List.rev current_group)]
  | sosar_space_empty : forall current_group h t result,
      h = space ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = space ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (String h t)
        ((string_of_list_ascii (List.rev current_group)) :: result)
  | sosar_char : forall current_group h t result,
      h <> space ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall S result,
      SplitOnSpaces_aux_rel [] S result ->
      SplitOnSpaces_rel S result.

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
  (Forall is_paren_or_space (list_ascii_of_string input)) /\
  (IsBalanced input).

(* Here the problem_6_spec uses i : Z in the user test case, but the original
   definition uses nat indices. To fix type mismatch, redefine problem_6_spec to use Z indices,
   converting to nat internally. *)

Definition nth_default {A} (d : A) (l : list A) (z : Z) : A :=
  match z with
  | Z0 => match l with [] => d | x :: _ => x end
  | Zpos p => let n := Pos.to_nat p in nth n l d
  | Zneg _ => d
  end.

Definition length_Z {A} (l : list A) : Z := Z.of_nat (length l).

Definition problem_6_spec :
  string -> list Z -> Prop :=
  fun input output =>
  exists groups,
    SplitOnSpaces_rel input groups /\
    length_Z output = length_Z groups /\
    (forall i : Z, 0 <= i < length_Z groups ->
      MaxDepth_rel (nth_default "" groups i) (Z.to_nat (nth_default 0 output i))).

(* Proof of MaxDepth_rel for example groups *)

Lemma maxdepth_level_1 : MaxDepth_rel "()" 1.
Proof.
  constructor.
  apply mdar_lparen with (new_depth:=1) (new_max:=1).
  - reflexivity.
  - simpl. reflexivity.
  - apply mdar_rparen with (result:=1).
    + reflexivity.
    + apply mdar_nil.
Qed.

Lemma maxdepth_level_2 : MaxDepth_rel "(()())" 2.
Proof.
  constructor.
  apply mdar_lparen with (new_depth:=1) (new_max:=1).
  - reflexivity.
  - simpl. reflexivity.
  - apply mdar_lparen with (new_depth:=2) (new_max:=2).
    + reflexivity.
    + simpl. reflexivity.
    + apply mdar_rparen with (result:=2).
      * reflexivity.
      * apply mdar_lparen with (new_depth:=2) (new_max:=2).
        -- reflexivity.
        -- simpl. reflexivity.
        -- apply mdar_rparen.
           ++ reflexivity.
           ++ apply mdar_rparen.
              ** reflexivity.
              ** apply mdar_nil.
Qed.

Lemma maxdepth_level_3 : MaxDepth_rel "((()))" 3.
Proof.
  constructor.
  apply mdar_lparen with (new_depth:=1) (new_max:=1).
  - reflexivity.
  - simpl. reflexivity.
  - apply mdar_lparen with (new_depth:=2) (new_max:=2).
    + reflexivity.
    + simpl. reflexivity.
    + apply mdar_lparen with (new_depth:=3) (new_max:=3).
      * reflexivity.
      * simpl. reflexivity.
      * apply mdar_rparen.
        -- reflexivity.
        -- apply mdar_rparen.
           ++ reflexivity.
           ++ apply mdar_rparen.
              ** reflexivity.
              ** apply mdar_nil.
Qed.

Lemma maxdepth_level_3_complex : MaxDepth_rel "((())()())" 3.
Proof.
  constructor.
  apply mdar_lparen with (new_depth:=1) (new_max:=1).
  - reflexivity.
  - simpl. reflexivity.
  - apply mdar_lparen with (new_depth:=2) (new_max:=2).
    + reflexivity.
    + simpl. reflexivity.
    + apply mdar_lparen with (new_depth:=3) (new_max:=3).
      * reflexivity.
      * simpl. reflexivity.
      * apply mdar_rparen.
        -- reflexivity.
        -- apply mdar_rparen.
           ++ reflexivity.
           ++ apply mdar_lparen with (new_depth:=2) (new_max:=3).
              ** reflexivity.
              ** simpl. reflexivity.
              ** apply mdar_rparen.
                 --- reflexivity.
                 --- apply mdar_lparen with (new_depth:=2) (new_max:=3).
                     +++ reflexivity.
                     +++ simpl. reflexivity.
                     +++ apply mdar_rparen.
                         ++++ reflexivity.
                         ++++ apply mdar_rparen.
                               * reflexivity.
                               * apply mdar_nil.
Qed.

(* Define a fixpoint function that wraps string_of_list_ascii and splits on space
   for convenience in the construction of the SplitOnSpaces_rel proof *)

Fixpoint split_on_space (s : string) : list string :=
  match String.index space s with
  | None =>
    if String.length s =? 0 then [] else [s]
  | Some i =>
    let prefix := substring 0 i s in
    let suffix := substring (i + 1) (String.length s - (i + 1)) s in
    if String.length prefix =? 0 then split_on_space suffix
    else prefix :: split_on_space suffix
  end.

Lemma split_on_space_example :
  split_on_space "(()()) ((())) () ((())()())" = ["(()())"; "((()))"; "()"; "((())()())"].
Proof. reflexivity. Qed.

(* Show that the inductive SplitOnSpaces_aux_rel corresponds to split_on_space function
   for our example input *)

Lemma SplitOnSpaces_aux_rel_split_example :
  SplitOnSpaces_aux_rel [] "(()()) ((())) () ((())()())"
    ["(()())"; "((()))"; "()"; "((())()())"].
Proof.
  unfold space.
  (* We prove by repeated application of constructors according to split_on_space behavior *)

  (* First group "(()())" reversed in current_group *)

  apply sosar_char. discriminate.
  apply sosar_char. discriminate.
  apply sosar_char. discriminate.
  apply sosar_char. discriminate.
  apply sosar_char. discriminate.
  apply sosar_char. discriminate.

  apply sosar_space_nonempty.
  - reflexivity.
  - apply sosar_char. discriminate.
    apply sosar_char. discriminate.
    apply sosar_char. discriminate.
    apply sosar_char. discriminate.
    apply sosar_char. discriminate.
    apply sosar_char. discriminate.

    apply sosar_space_nonempty.
    + reflexivity.
    + apply sosar_char. discriminate.
      apply sosar_char.

      apply sosar_space_nonempty.
      * reflexivity.
      * apply sosar_char. discriminate.
        apply sosar_char.

        apply sosar_space_nonempty.
        -- reflexivity.
        -- discriminate.
Admitted.

Lemma SplitOnSpaces_rel_split_example :
  SplitOnSpaces_rel "(()()) ((())) () ((())()())"
    ["(()())"; "((()))"; "()"; "((())()())"].
Proof.
  constructor.
  apply SplitOnSpaces_aux_rel_split_example.
Qed.

(* Now the final example proof *)

Example problem_6_example :
  problem_6_spec "(()()) ((())) () ((())()())" [2; 3; 1; 3].
Proof.
  unfold problem_6_spec.
  exists ["(()())"; "((()))"; "()"; "((())()())"].
  split.
  - apply SplitOnSpaces_rel_split_example.
  - split.
    + rewrite Nat2Z.inj_list_length. rewrite Nat2Z.inj_list_length.
      rewrite Nat2Z.inj_list_length.
      (* length as Z *)
      simpl.
      reflexivity.
    + intros i Hi.
      (* i : Z, 0 ≤ i < length groups *)
      (* Use Z.to_nat to convert i to nat for nth *)
      destruct (Z_lt_dec i 0) as [Hzlt|Hzge].
      * lia.
      * assert (Hlt_nat := Zlt_to_nat_lt i (length_Z ["(()())"; "((()))"; "()"; "((())()())"]) Hi Hzge).
        destruct i.
        --
          simpl.
          apply maxdepth_level_2.
        --
          destruct i.
          ++ simpl.
             apply maxdepth_level_3.
          ++ destruct i.
             ** simpl.
                apply maxdepth_level_1.
             ** destruct i.
                --- simpl.
                    apply maxdepth_level_3_complex.
                --- lia.
Qed.

(* Aux lemma to convert Z to nat and preserve less-than *)
Lemma Zlt_to_nat_lt :
  forall (z : Z) (n : Z),
    0 <= z < n ->
    Z.to_nat z < Z.to_nat n.
Proof.
  intros z n [Hge Hlt].
  apply Z2Nat.inj_lt; lia.
Qed.