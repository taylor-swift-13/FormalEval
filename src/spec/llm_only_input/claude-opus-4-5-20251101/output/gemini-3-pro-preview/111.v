Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Fixpoint split_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => if string_dec acc "" then [] else [acc]
  | String c s' =>
    if Ascii.eqb c " "
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

Example test_histogram : histogram_spec "a b b a" (("a", 2) :: ("b", 2) :: nil).
Proof.
  unfold histogram_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H.
    split.
    + constructor.
      * simpl. intro Hcontra. destruct Hcontra as [Hcontra | Hcontra].
        -- discriminate Hcontra.
        -- destruct Hcontra.
      * constructor.
        -- simpl. intro Hcontra. destruct Hcontra.
        -- constructor.
    + split.
      * intros k v Hlookup.
        simpl in Hlookup.
        destruct (string_dec k "a") as [Ha | Ha].
        -- inversion Hlookup. subst. split; reflexivity.
        -- destruct (string_dec k "b") as [Hb | Hb].
           ++ inversion Hlookup. subst. split; reflexivity.
           ++ discriminate Hlookup.
      * intros k Hin Hcount.
        simpl in Hin.
        destruct Hin as [Ha | [Hb | [Hb2 | [Ha2 | Hfalse]]]].
        -- subst k. simpl. destruct (string_dec "a" "a") as [_ | Hcontra]; [reflexivity | contradiction].
        -- subst k. simpl. destruct (string_dec "b" "a") as [Hcontra | _]; [discriminate | ].
           destruct (string_dec "b" "b") as [_ | Hcontra]; [reflexivity | contradiction].
        -- subst k. simpl. destruct (string_dec "b" "a") as [Hcontra | _]; [discriminate | ].
           destruct (string_dec "b" "b") as [_ | Hcontra]; [reflexivity | contradiction].
        -- subst k. simpl. destruct (string_dec "a" "a") as [_ | Hcontra]; [reflexivity | contradiction].
        -- destruct Hfalse.
Qed.