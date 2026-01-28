Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* Correcting the ascii literal syntax for compilation by adding %char scope delimiter *)
Fixpoint split_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => if string_dec acc "" then [] else [acc]
  | String c s' =>
    if Ascii.eqb c " "%char
    then (if string_dec acc "" then [] else [acc]) ++ split_aux s' ""
    else split_aux s' (acc ++ String c EmptyString)
  end.

Definition split_spaces (s : string) : list string := 
  split_aux s "".

Definition count_occurrences (target : string) (l : list string) : nat :=
  length (filter (fun s => if string_dec s target then true else false) l).

Definition get_max_count (l : list string) : nat :=
  fold_right (fun s acc => max (count_occurrences s l) acc) 0 l.

Fixpoint lookup (k : string) (l : list (string * nat)) : option nat :=
  match l with
  | [] => None
  | (k', v) :: t => if string_dec k k' then Some v else lookup k t
  end.

Definition histogram_spec (test : string) (result : list (string * nat)) : Prop :=
  let words := split_spaces test in
  let mx := get_max_count words in
  (words = [] -> result = []) /\
  (words <> [] ->
    NoDup (map fst result) /\
    (forall k v, lookup k result = Some v -> v = mx /\ count_occurrences k words = mx) /\
    (forall k, In k words -> count_occurrences k words = mx -> lookup k result = Some mx)).

(* We use %string to explicitly tell Coq these are strings, preventing type inference errors with Ascii *)
Example test_histogram : histogram_spec "a b b a" [("a"%string, 2); ("b"%string, 2)].
Proof.
  unfold histogram_spec.
  
  (* Pre-compute the words list to simplify the proof *)
  remember (split_spaces "a b b a") as words.
  assert (Hwords: words = ["a"; "b"; "b"; "a"]).
  { subst words. vm_compute. reflexivity. }
  rewrite Hwords. clear Heqwords Hwords.

  (* Pre-compute the max count *)
  remember (get_max_count ["a"; "b"; "b"; "a"]) as mx.
  assert (Hmx: mx = 2).
  { subst mx. vm_compute. reflexivity. }
  rewrite Hmx. clear Heqmx Hmx.

  split.
  - (* Case: words = [] -> result = [] *)
    intro Hempty. inversion Hempty.
    
  - (* Case: words <> [] *)
    intro Hnotempty.
    repeat split.
    
    + (* Sub-goal: NoDup (map fst result) *)
      simpl.
      constructor.
      * (* ~ In "a" ["b"] *)
        simpl. intro H. destruct H as [H | H]; inversion H.
      * constructor; [simpl; tauto | constructor].

    + (* Sub-goal: forall k v, lookup k result = Some v -> ... *)
      intros key val Hlookup.
      simpl in Hlookup.
      destruct (string_dec key "a") as [HeqA | HneqA].
      * (* Case key = "a" *)
        subst key. inversion Hlookup. subst val.
        split; [reflexivity | vm_compute; reflexivity].
      * (* Case key <> "a" *)
        destruct (string_dec key "b") as [HeqB | HneqB].
        -- (* Case key = "b" *)
           subst key. inversion Hlookup. subst val.
           split; [reflexivity | vm_compute; reflexivity].
        -- (* Case key <> "b" *)
           inversion Hlookup.

    + (* Sub-goal: forall k, In k words -> count = mx -> lookup = Some mx *)
      intros key Hin Hcount.
      simpl in Hin.
      (* Decompose the list membership *)
      destruct Hin as [Ha | [Hb | [Hb2 | [Ha2 | Hfalse]]]].
      * subst key. simpl. reflexivity.
      * subst key. simpl. reflexivity.
      * subst key. simpl. reflexivity.
      * subst key. simpl. reflexivity.
      * contradiction.
Qed.